; Scopes
(module) @local.scope
(operator_definition) @local.scope
(module_definition) @local.scope
(function_definition) @local.scope
(lambda) @local.scope

; Definitions
(constant_declaration (identifier) @local.definition)
(variable_declaration (identifier) @local.definition)
(operator_definition name: (identifier) @local.definition)
(operator_definition parameter: (identifier) @local.definition)
(module_definition name: (identifier) @local.definition)
(module_definition parameter: (identifier) @local.definition)
(function_definition name: (identifier) @local.definition)
(function_definition (quantifier_bound (identifier) @local.definition))
(function_definition (quantifier_bound (tuple_of_identifiers (identifier) @local.definition)))
(lambda (identifier) @local.definition)

; References
(identifier_ref) @local.reference
