/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2016-2020 Meteor Development Group, Inc.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

'use strict'

const {
  GraphQLSchema,
  GraphQLObjectType,
  Kind,
  extendSchema,
  parse,
  isTypeDefinitionNode,
  isTypeExtensionNode,
  isObjectType,
  printSchema
} = require('graphql')
const { validateSDL } = require('graphql/validation/validate')
const compositionRules = require('./federation/compositionRules')

const BASE_FEDERATION_TYPES = `
  scalar _Any
  scalar _FieldSet

  directive @external on FIELD_DEFINITION
  directive @requires(fields: _FieldSet!) on FIELD_DEFINITION
  directive @provides(fields: _FieldSet!) on FIELD_DEFINITION
  directive @key(fields: _FieldSet!) on OBJECT | INTERFACE
  directive @extends on OBJECT | INTERFACE
`

const FEDERATION_SCHEMA = `
  ${BASE_FEDERATION_TYPES}

  type _Service {
    sdl: String
  }

  extend type Query {
    _service: _Service!
  }
`

const extensionKindToDefinitionKind = {
  [Kind.SCALAR_TYPE_EXTENSION]: Kind.SCALAR_TYPE_DEFINITION,
  [Kind.OBJECT_TYPE_EXTENSION]: Kind.OBJECT_TYPE_DEFINITION,
  [Kind.INTERFACE_TYPE_EXTENSION]: Kind.INTERFACE_TYPE_DEFINITION,
  [Kind.UNION_TYPE_EXTENSION]: Kind.UNION_TYPE_DEFINITION,
  [Kind.ENUM_TYPE_EXTENSION]: Kind.ENUM_TYPE_DEFINITION,
  [Kind.INPUT_OBJECT_TYPE_EXTENSION]: Kind.INPUT_OBJECT_TYPE_DEFINITION
}

const definitionKindToExtensionKind = {
  [Kind.SCALAR_TYPE_DEFINITION]: Kind.SCALAR_TYPE_EXTENSION,
  [Kind.OBJECT_TYPE_DEFINITION]: Kind.OBJECT_TYPE_EXTENSION,
  [Kind.INTERFACE_TYPE_DEFINITION]: Kind.INTERFACE_TYPE_EXTENSION,
  [Kind.UNION_TYPE_DEFINITION]: Kind.UNION_TYPE_EXTENSION,
  [Kind.ENUM_TYPE_DEFINITION]: Kind.ENUM_TYPE_EXTENSION,
  [Kind.INPUT_OBJECT_TYPE_DEFINITION]: Kind.INPUT_OBJECT_TYPE_EXTENSION
}

function removeExternalFields (typeDefinition) {
  return {
    ...typeDefinition,
    fields: typeDefinition.fields.filter(fieldDefinition => !fieldDefinition.directives.some(directive => directive.name.value === 'external'))
  }
}

function hasExtendsDirective (definition) {
  if (!definition.directives) {
    return false
  }
  return definition.directives.some(directive => directive.name.value === 'extends')
}

function getStubTypes (schemaDefinitions, isGateway) {
  const definitionsMap = {}
  const extensionsMap = {}
  const extensions = []
  const directiveDefinitions = []

  for (const definition of schemaDefinitions) {
    const typeName = definition.name.value
    const isTypeExtensionByDirective = hasExtendsDirective(definition)
    /* istanbul ignore else we are not interested in nodes that does not match if statements */
    if (isTypeDefinitionNode(definition) && !isTypeExtensionByDirective) {
      definitionsMap[typeName] = definition
    } else if (isTypeExtensionNode(definition) || (isTypeDefinitionNode(definition) && isTypeExtensionByDirective)) {
      extensionsMap[typeName] = {
        kind: isTypeExtensionByDirective ? definition.kind : extensionKindToDefinitionKind[definition.kind],
        name: definition.name
      }
      if (isTypeExtensionByDirective) {
        definition.kind = definitionKindToExtensionKind[definition.kind]
      }
      extensions.push(isGateway ? removeExternalFields(definition) : definition)
    } else if (definition.kind === Kind.DIRECTIVE_DEFINITION) {
      directiveDefinitions.push(definition)
    }
  }

  // console.log('definitionsMap', definitionsMap)
  // console.log('extensionsMap', extensionsMap)
  // console.log('extensions', extensions)
  // console.log('directiveDefinitions', directiveDefinitions)

  return {
    typeStubs: Object.keys(extensionsMap)
      // .filter(extensionTypeName => !definitionsMap[extensionTypeName])
      .filter(extensionTypeName => !definitionsMap[extensionTypeName] && !['Query', 'Mutation', 'Subscription'].includes(extensionTypeName))
      .map(extensionTypeName => extensionsMap[extensionTypeName]),
    extensions,
    definitions: [
      ...directiveDefinitions,
      ...Object.values(definitionsMap)
    ]
  }
}

function gatherDirectives (type) {
  let directives = []
  for (const node of (type.extensionASTNodes || [])) {
    /* istanbul ignore else we are not interested in nodes that does not have directives */
    if (node.directives) {
      directives = directives.concat(node.directives)
    }
  }

  if (type.astNode && type.astNode.directives) {
    directives = directives.concat(type.astNode.directives)
  }

  return directives
}

function typeIncludesDirective (type, directiveName) {
  const directives = gatherDirectives(type)
  return directives.some(directive => directive.name.value === directiveName)
}

function addTypeNameToResult (result, typename) {
  /* istanbul ignore else when result is null or not an object we return original result */
  if (result !== null && typeof result === 'object') {
    Object.defineProperty(result, '__typename', {
      value: typename
    })
  }
  return result
}

function addEntitiesResolver (schema) {
  const entityTypes = Object.values(schema.getTypeMap()).filter(
    type => isObjectType(type) && typeIncludesDirective(type, 'key')
  )

  if (entityTypes.length > 0) {
    schema = extendSchema(schema, parse(`
      union _Entity = ${entityTypes.join(' | ')}

      extend type Query {
        _entities(representations: [_Any!]!): [_Entity]!
      }
    `), {
      assumeValid: true
    })

    const query = schema.getType('Query')
    const queryFields = query.getFields()
    queryFields._entities = {
      ...queryFields._entities,
      resolve: (_source, { representations }, context, info) => {
        return representations.map((reference) => {
          const { __typename } = reference

          const type = info.schema.getType(__typename)
          if (!type || !isObjectType(type)) {
            throw new Error(
              `The _entities resolver tried to load an entity for type "${__typename}", but no object type of that name was found in the schema`
            )
          }

          const resolveReference = type.resolveReference
            ? type.resolveReference
            : function defaultResolveReference () {
              return reference
            }

          const result = resolveReference(reference, {}, context, info)

          if (result && 'then' in result && typeof result.then === 'function') {
            return result.then(x =>
              addTypeNameToResult(x, __typename)
            )
          }

          return addTypeNameToResult(result, __typename)
        })
      }
    }
  }

  return schema
}

function addServiceResolver (schema, originalSchemaSDL) {
  // schema = extendSchema(schema, parse(`
  //   extend type Query {
  //     _service: _Service!
  //   }
  // `), {
  //   assumeValid: true
  // })
  const query = schema.getType('Query')

  const queryFields = query.getFields()
  queryFields._service = {
    ...queryFields._service,
    resolve: () => ({ sdl: originalSchemaSDL })
  }

  return schema
}

function getServiceSDL (schema) {
  // TODO Remove entities union
  const config = schema.toConfig()

  // Filter federation directives
  config.directives = config.directives.filter(d => {
    return !['external', 'requires', 'provides', 'key', 'extends'].includes(d.name)
  })

  // Filter federation types
  config.types = config.types.filter(t => {
    return t.name !== '_Any' && t.name !== '_FieldSet'
  })

  // Remove Query _service and _entities
  const query = config.types.find(t => t.name === 'Query')

  if (query._fields._service) {
    delete query._fields._service
  }
  if (query._fields._entities) {
    delete query._fields._entities
  }

  config.types.query = query

  const sdl = printSchema(
    new GraphQLSchema({ ...config })
  )
  return sdl
}

function extendFederationSchema (originalSchema, schema, isGateway) {
  // console.log('originalSchema', originalSchema)
  // console.log('schema', schema.definitions)
  const { typeStubs, extensions, definitions } = getStubTypes(schema.definitions, isGateway)

  // Filter existing types (Query, Mutation, Subscriptions ...)
  // const stubs = typeStubs.filter(stub => {
  //   return !originalSchema.getType(stub.name.value)
  // })
  let extendedSchema = new GraphQLSchema({
    ...originalSchema.toConfig()
  })

  // const newQuery = typeStubs.find(t => t.name.value === 'Query')
  // const query = originalSchema.getType('Query')
  // console.log('newQuery', Object.keys(newQuery))
  // if (query && newQuery) {
  //   console.log('MERGE QUERY')
  //   for (const [fieldName, field] of Object.entries(newQuery.fields)) {
  //     query[fieldName] = field
  //   }

  //   extendedSchema = new GraphQLSchema({
  //     ...originalSchema.toConfig(),
  //     query
  //   })
  // }

  console.log('typeStubs', typeStubs)
  // console.log('extensions', extensions)
  // console.log('definitions', definitions)
  // console.log('stubs', stubs)
  // Add type stubs
  extendedSchema = extendSchema(originalSchema, {
    kind: Kind.DOCUMENT,
    definitions: typeStubs
  })

  // Add default type definitions
  extendedSchema = extendSchema(extendedSchema, {
    kind: Kind.DOCUMENT,
    definitions
  })

  // Add all extensions
  const extensionsDocument = {
    kind: Kind.DOCUMENT,
    definitions: extensions
  }

  // instead of relying on extendSchema internal validations
  // we run validations in our code so that we can use slightly different rules
  // as extendSchema internal rules are meant for regular usage
  // and federated schemas have different constraints
  const errors = validateSDL(extensionsDocument, extendedSchema, compositionRules)
  if (errors.length === 1) {
    throw errors[0]
  } else if (errors.length > 1) {
    const err = new Error('Schema issues, check out the .errors property on the Error.')
    err.errors = errors
    throw err
  }

  extendedSchema = extendSchema(extendedSchema, extensionsDocument, { assumeValidSDL: true })

  if (!isGateway) {
    console.log('add entities and service resolvers')
    if (!extendedSchema.getType('Query')) {
      extendedSchema = new GraphQLSchema({
        ...extendedSchema.toConfig(),
        query: new GraphQLObjectType({
          name: 'Query',
          fields: {}
        })
      })
    }

    const sdl = getServiceSDL(extendedSchema)
    extendedSchema = addServiceResolver(extendedSchema, sdl)
    extendedSchema = addEntitiesResolver(extendedSchema)
  }

  return extendedSchema
}

function buildFederationSchema (schema, isGateway) {
  let federationSchema = new GraphQLSchema({
    query: undefined
  })

  federationSchema = extendSchema(federationSchema, parse(isGateway ? BASE_FEDERATION_TYPES : FEDERATION_SCHEMA))

  const parsedSchema = parse(schema)
  federationSchema = extendFederationSchema(federationSchema, parsedSchema, isGateway)

  return new GraphQLSchema({
    ...federationSchema.toConfig(),
    query: federationSchema.getType('Query'),
    mutation: federationSchema.getType('Mutation'),
    subscription: federationSchema.getType('Subscription')
  })
}

module.exports = {
  buildFederationSchema,
  extendFederationSchema
}
