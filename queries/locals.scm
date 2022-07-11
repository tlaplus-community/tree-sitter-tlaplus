; Scopes
[
  (bounded_quantification)
  (function_definition) 
  (lambda) 
  (module) 
  (module_definition) 
  (operator_definition)
  (pcal_algorithm)
  (pcal_macro)
  (pcal_procedure)
  (pcal_with)
  (unbounded_quantification)
] @local.scope

; Definitions
(constant_declaration (identifier) @local.definition)
(constant_declaration (operator_declaration name: (_) @local.definition))
(function_definition name: (identifier) @local.definition)
(lambda (identifier) @local.definition)
(module_definition name: (_) @local.definition)
(module_definition parameter: (identifier) @local.definition)
(module_definition parameter: (operator_declaration name: (_) @local.definition))
(operator_definition name: (_) @local.definition)
(operator_definition parameter: (identifier) @local.definition)
(operator_definition parameter: (operator_declaration name: (_) @local.definition))
(pcal_macro_decl parameter: (identifier) @local.definition)
(pcal_proc_var_decl (identifier) @local.definition)
(pcal_var_decl (identifier) @local.definition)
(pcal_with (identifier) @local.definition)
(quantifier_bound (identifier) @local.definition)
(quantifier_bound (tuple_of_identifiers (identifier) @local.definition))
(variable_declaration (identifier) @local.definition)

; References
(identifier_ref) @local.reference
(bound_prefix_op symbol: (_) @local.reference)
(bound_infix_op symbol: (_) @local.reference)
(bound_postfix_op symbol: (_) @local.reference)
(bound_nonfix_op name: (_) @local.reference)

