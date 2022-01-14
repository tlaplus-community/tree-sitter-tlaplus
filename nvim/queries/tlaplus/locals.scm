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
] @scope

; ; Definitions
(constant_declaration (identifier) @definition.constant)
(function_definition name: (identifier) @definition.operator)
(lambda (identifier) @definition.parameter)
(operator_definition name: (identifier) @definition.operator)
(operator_definition parameter: (identifier) @definition.parameter)
(pcal_macro_decl parameter: (identifier) @definition.parameter)
(pcal_proc_var_decl (identifier) @definition.parameter)
(pcal_var_decl (identifier) @definition.variable)
(pcal_p_with (identifier) @definition.parameter)
(pcal_c_with (identifier) @definition.parameter)
(quantifier_bound (identifier) @definition.parameter)
(quantifier_bound (tuple_of_identifiers (identifier) @definition.parameter))
(variable_declaration (identifier) @definition.variable)

; Builtin variables
(pcal_p_algorithm_body
  [
    (_ (identifier_ref) @definition.builtin_variable)
    (_ (_ (identifier_ref) @definition.builtin_variable))
    (_ (_ (_ (identifier_ref) @definition.builtin_variable))) 
    (_ (_ (_ (_ (identifier_ref) @definition.builtin_variable))))
    (_ (_ (_ (_ (_ (identifier_ref) @definition.builtin_variable)))))
  ]
  (#vim-match? @definition.builtin_variable "^(self|pc|stack)$")
)
(pcal_c_algorithm_body
  [
    (_ (identifier_ref) @definition.builtin_variable)
    (_ (_ (identifier_ref) @definition.builtin_variable))
    (_ (_ (_ (identifier_ref) @definition.builtin_variable))) 
    (_ (_ (_ (_ (identifier_ref) @definition.builtin_variable))))
    (_ (_ (_ (_ (_ (identifier_ref) @definition.builtin_variable)))))
  ]
  (#vim-match? @definition.builtin_variable "^(self|pc|stack)$")
)

; Builtin libraries! 
(module 
  ( 
    (extends (identifier_ref) @sequences (#eq? @sequences "Sequences"))
    ([
      (_ (identifier_ref) @definition.sequences)
      (_ (_ (identifier_ref) @definition.sequences))
      (_ (_ (_ (identifier_ref) @definition.sequences))) 
      (_ (_ (_ (_ (identifier_ref) @definition.sequences))))
      (_ (_ (_ (_ (_ (identifier_ref) @definition.sequences)))))
    ]
    (#vim-match? @definition.sequences "^(Seq|Len)$")
    )
  )
)
