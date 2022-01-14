; Scopes
[
  (bounded_quantification)
  (function_definition) 
  (lambda) 
  (module) 
  (module_definition) 
  (pcal_p_algorithm)
  (pcal_c_algorithm)
  (pcal_p_macro)
  (pcal_c_macro)
  (pcal_p_procedure)
  (pcal_c_procedure)
  (pcal_p_with)
  (pcal_c_with)
  (unbounded_quantification)
] @local.scope

; Definitions
(constant_declaration (identifier) @local.definition)
(function_definition name: (identifier) @local.definition)
(lambda (identifier) @local.definition)
(module_definition name: (identifier) @local.definition)
(module_definition parameter: (identifier) @local.definition)
(operator_definition name: (identifier) @local.definition)
(operator_definition parameter: (identifier) @local.definition)
(pcal_macro_decl parameter: (identifier) @local.definition)
(pcal_proc_var_decl (identifier) @local.definition)
(pcal_var_decl (identifier) @local.definition)
(pcal_p_with (identifier) @local.definition)
(pcal_c_with (identifier) @local.definition)
(quantifier_bound (identifier) @local.definition)
(quantifier_bound (tuple_of_identifiers (identifier) @local.definition))
(variable_declaration (identifier) @local.definition)

; References
(identifier_ref) @local.reference
