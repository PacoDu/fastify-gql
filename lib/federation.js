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
  GraphQLString,
  GraphQLNonNull,
  GraphQLDirective,
  Kind,
  extendSchema,
  parse,
  isTypeDefinitionNode,
  isTypeExtensionNode,
  isObjectType,
  visit,
  specifiedDirectives,
  DirectiveLocation,
  print,
  stripIgnoredCharacters,
  printSchema
} = require('graphql')
const { validateSDL } = require('graphql/validation/validate')
const compositionRules = require('./federation/compositionRules')
const { MER_ERR_GQL_INVALID_SCHEMA, MER_ERR_GQL_GATEWAY_INVALID_SCHEMA } = require('./errors')
const { cpuUsage } = require('process')

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

const federationDirectives = {
  KeyDirective: new GraphQLDirective({
    name: 'key',
    locations: [DirectiveLocation.OBJECT, DirectiveLocation.INTERFACE],
    args: {
      fields: {
        type: GraphQLNonNull(GraphQLString)
      }
    }
  }),
  ExtendsDirective: new GraphQLDirective({
    name: 'extends',
    locations: [DirectiveLocation.OBJECT, DirectiveLocation.INTERFACE]
  }),
  ExternalDirective: new GraphQLDirective({
    name: 'external',
    locations: [DirectiveLocation.OBJECT, DirectiveLocation.FIELD_DEFINITION]
  }),
  RequiresDirective: new GraphQLDirective({
    name: 'requires',
    locations: [DirectiveLocation.FIELD_DEFINITION],
    args: {
      fields: {
        type: GraphQLNonNull(GraphQLString)
      }
    }
  }),
  ProvidesDirective: new GraphQLDirective({
    name: 'provides',
    locations: [DirectiveLocation.FIELD_DEFINITION],
    args: {
      fields: {
        type: GraphQLNonNull(GraphQLString)
      }
    }
  })
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
    // console.log('isTypeExtensionByDirective', definition, isTypeExtensionByDirective)
    // if (isGateway && typeName === 'Query') {
    //   console.log('isGateway and processing Query')
    // }
    if (isGateway && ['Query', 'Mutation', 'Subscription'].includes(typeName)) {
      console.log('Forcing extension ')
      const kind = definitionKindToExtensionKind[definition.kind]
      extensionsMap[typeName] = {
        kind,
        name: definition.name
      }

      definition.kind = kind
    }

    /* istanbul ignore else we are not interested in nodes that does not match if statements */
    if (isTypeDefinitionNode(definition) && !isTypeExtensionByDirective) {
      // console.log('isTypeDefinitionNode', definition)
      definitionsMap[typeName] = definition
    } else if (isTypeExtensionNode(definition) || (isTypeDefinitionNode(definition) && isTypeExtensionByDirective)) {
      // console.log('isTypeExtensionNode', definition)
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

  return {
    typeStubs: Object.keys(extensionsMap)
      .filter(extensionTypeName => !definitionsMap[extensionTypeName])
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
  let queryFields = schema.getType('Query').getFields()

  if (entityTypes.length > 0) {
    if (!queryFields._entities) {
      schema = extendSchema(schema, parse(`
        union _Entity = ${entityTypes.join(' | ')}
  
        extend type Query {
          _entities(representations: [_Any!]!): [_Entity]!
        }
      `), {
        assumeValid: true
      })

      queryFields = schema.getType('Query').getFields()
    }

    queryFields._entities = {
      ...queryFields._entities,
      resolve: (_source, { representations }, context, info) => {
        return representations.map((reference) => {
          const { __typename } = reference

          const type = info.schema.getType(__typename)
          if (!type || !isObjectType(type)) {
            throw new MER_ERR_GQL_GATEWAY_INVALID_SCHEMA(__typename)
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

function addServiceResolver (schema) {
  const query = schema.getType('Query')
  let queryFields = query.getFields()

  // Add _service resolver if not already defined
  if (!queryFields._service) {
    schema = extendSchema(schema, parse(`
      extend type Query {
        _service: _Service!
      }
    `), {
      assumeValid: true
    })

    queryFields = schema.getType('Query').getFields()
  }

  // Build SDL
  // console.log('Building SDL for')
  // console.log(printSchema(schema))
  const strippedDefinitions = stripCommonPrimitives(parse(printSchema(schema)))
  const sdl = stripIgnoredCharacters(print(strippedDefinitions))
  console.log('******** built sdl ********')
  console.log(sdl)

  queryFields._service = {
    ...queryFields._service,
    resolve: () => ({ sdl })
  }

  return schema
}

function stripCommonPrimitives (document) {
  // console.log('stripCommonPrimitives', document)
  const typeDefinitionVisitor = (node) => {
    // Remove the `_entities` and `_service` fields from the `Query` type
    if (node.name.value === 'Query') {
      const filteredFieldDefinitions = node.fields ? node.fields.filter(
        (fieldDefinition) => !['_service', '_entities'].includes(fieldDefinition.name.value)
      ) : undefined

      // If the 'Query' type is now empty just remove it
      if (!filteredFieldDefinitions || filteredFieldDefinitions.length === 0) {
        return null
      }

      return {
        ...node,
        fields: filteredFieldDefinitions
      }
    }

    // Remove the _Service type from the document
    const isFederationType = node.name.value === '_Service'
    return isFederationType ? null : node
  }

  return visit(document, {
    // Remove all common directive definitions from the document
    DirectiveDefinition (node) {
      const isCommonDirective = false
      // const isCommonDirective = [...Object.values(federationDirectives), ...specifiedDirectives].some(
      //   (directive) => directive.name === node.name.value
      // )
      return isCommonDirective ? null : node
    },
    // Remove all federation scalar definitions from the document
    ScalarTypeDefinition (node) {
      const isFederationScalar = ['_Any', '_FieldSet'].includes(node.name.value)
      return isFederationScalar ? null : node
    },
    // Remove all federation union definitions from the document
    UnionTypeDefinition (node) {
      const isFederationUnion = node.name.value === '_Entity'
      return isFederationUnion ? null : node
    },
    ObjectTypeDefinition: typeDefinitionVisitor,
    ObjectTypeExtension: typeDefinitionVisitor
  })
}

function buildFederationSchema (schema, isGateway) {
  const baseTypes = isGateway ? BASE_FEDERATION_TYPES : FEDERATION_SCHEMA
  console.log('BUILD FEDE', schema)
  const parsedOriginalSchema = parse(schema)
  let federationSchema = new GraphQLSchema({
    query: undefined
  })

  console.log('PARSED', print(parsedOriginalSchema))
  federationSchema = extendSchema(federationSchema, parse(isGateway ? BASE_FEDERATION_TYPES : FEDERATION_SCHEMA))
  console.log('PARSED2', printSchema(federationSchema))
  federationSchema = extendFederationSchema(federationSchema, parsedOriginalSchema, isGateway)
  if (isGateway) {
    console.log('FEDERATION SCHEMA')
    console.log(printSchema(federationSchema))
  } else {
    console.log('SERVICE SCHEMA')
    console.log(printSchema(federationSchema))
  }
  return federationSchema
}

function extendFederationSchema (originalSchema, schemaExtension, isGateway) {
  // console.log('SCHME EXT', schemaExtension)
  // const { typeStubs, extensions, definitions } = getStubTypes(schemaExtension.definitions, isGateway)

  // Filter existing types (Query, Mutation, Subscriptions ...)
  // const stubs = typeStubs.filter(stub => {
  //   return !originalSchema.getType(stub.name.value)
  // })
  // if (isGateway) {
  //   console.log('IS GATEWAY', typeStubs, extensions, definitions)
  //   for (const [index, definition] of Object.entries(typeStubs)) {
  //     console.log('Checking', definitions)
  //     const typeName = definition.type.name
  //     if (['Query', 'Mutation', 'Subscription'].includes(typeName)) {
  //       if (originalSchema.getTypeMap().includes(typeName)) {
  //         console.log('Schema already includes ', typeName)
  //         extensions.push(removeExternalFields(definition))
  //         typeStubs.splice(index, 1)
  //       }
  //     }
  //   }
  // }
  // Manual Query, Mutation, Subscription merge for gateway
  // if (isGateway) {
  //   const query = originalSchema.getType('Query')
  //   const stub = typeStubs.find(stub => stub.name.value === 'Query')
  //   console.log('IS GATEWAY', query, stub)
  //   if (query && stub) {
  //     const queryFields = query.getFields()
  //     console.log(queryFields)
  //     console.log('should merge', stub)
  //   }
  // }

  // Add type stubs
  // let extendedSchema = extendSchema(originalSchema, {
  //   kind: Kind.DOCUMENT,
  //   definitions: typeStubs
  //   // definitions: typeStubs.filter(stub => {
  //   //   return !originalSchema.getType(stub.name.value)
  //   // })
  // })

  // // Add default type definitions
  // extendedSchema = extendSchema(extendedSchema, {
  //   kind: Kind.DOCUMENT,
  //   definitions
  // })

  // // Add all extensions
  // const extensionsDocument = {
  //   kind: Kind.DOCUMENT,
  //   definitions: extensions
  // }

  let extendedSchema = originalSchema
  if (!originalSchema.getType('Query') && schemaExtension.definitions.find(def => def.name.value === 'Query')) {
    extendedSchema = new GraphQLSchema({
      ...extendedSchema.toConfig(),
      query: new GraphQLObjectType({
        name: 'Query',
        fields: {}
      })
    })
  }

  // instead of relying on extendSchema internal validations
  // we run validations in our code so that we can use slightly different rules
  // as extendSchema internal rules are meant for regular usage
  // and federated schemas have different constraints
  // const errors = validateSDL(extensionsDocument, extendedSchema, compositionRules)
  const errors = validateSDL(schemaExtension, extendedSchema, compositionRules)
  if (errors.length === 1) {
    throw errors[0]
  } else if (errors.length > 1) {
    const err = new Error('Schema issues, check out the .errors property on the Error.')
    err.errors = errors
    throw err
  }

  // extendedSchema = extendSchema(extendedSchema, extensionsDocument, { assumeValidSDL: true })
  extendedSchema = extendSchema(extendedSchema, schemaExtension, { assumeValidSDL: true })

  if (!extendedSchema.getType('Query')) {
    extendedSchema = new GraphQLSchema({
      ...extendedSchema.toConfig(),
      query: new GraphQLObjectType({
        name: 'Query',
        fields: {}
      })
    })
  }

  if (!isGateway) {
    extendedSchema = addEntitiesResolver(extendedSchema)
    extendedSchema = addServiceResolver(extendedSchema)
  }

  return new GraphQLSchema({
    ...extendedSchema.toConfig(),
    query: extendedSchema.getType('Query'),
    mutation: extendedSchema.getType('Mutation'),
    subscription: extendedSchema.getType('Subscription')
  })
}

module.exports = {
  buildFederationSchema,
  extendFederationSchema
}
