; highlights.scm
; Default capture names for tree-sitter highlight found here:
; https://github.com/nvim-treesitter/nvim-treesitter/blob/e473630fe0872cb0ed97cd7085e724aa58bc1c84/lua/nvim-treesitter/highlight.lua#L14-L104
; Keywords
[
  "ACTION"
  "ASSUME"
  "ASSUMPTION"
  "AXIOM"
  "BY"
  "CASE"
  "CHOOSE"
  "CONSTANT"
  "CONSTANTS"
  "COROLLARY"
  "DEF"
  "DEFINE"
  "DEFS"
  "DOMAIN"
  "ELSE"
  "ENABLED"
  "EXCEPT"
  "EXTENDS"
  "HAVE"
  "HIDE"
  "IF"
  "IN"
  "INSTANCE"
  "LAMBDA"
  "LEMMA"
  "LET"
  "LOCAL"
  "MODULE"
  "NEW"
  "OBVIOUS"
  "OMITTED"
  "ONLY"
  "OTHER"
  "PICK"
  "PROOF"
  "PROPOSITION"
  "PROVE"
  "QED"
  "RECURSIVE"
  "SF_"
  "STATE"
  "SUBSET"
  "SUFFICES"
  "TAKE"
  "TEMPORAL"
  "THEN"
  "THEOREM"
  "UNCHANGED"
  "UNION"
  "USE"
  "VARIABLE"
  "VARIABLES"
  "WF_"
  "WITH"
  "WITNESS"
  (address)
  (all_map_to)
  (assign)
  (case_arrow)
  (case_box)
  (def_eq)
  (exists)
  (forall)
  (gets)
  (label_as)
  (maps_to)
  (set_in)
  (temporal_exists)
  (temporal_forall)
;  Pluscal keywords
  "--algorithm" 
  "--fair"
  "algorithm"
  "assert"
  "await"
  "begin"
  "call"
  "define"
  "end"
  "fair"
  "goto"
  "macro"
  "or"
  "procedure"
  "process"
  "skip"
  "variable"
  "variables"
  "when"
  "with"
] @keyword
(pcal_with ("=") @keyword)
(pcal_process ("=") @keyword)
[ 
  "if" 
  "then" 
  "else" 
  "elseif" 
  (pcal_end_if)
  "either"
] @conditional
[ 
  "while" 
  "do" 
  (pcal_end_while) 
  "with" 
  (pcal_end_with)
] @repeat
("return") @keyword.return
[ "print" ] @function.macro


; Literals
(nat_number) @number
(real_number) @number
(binary_number (format) @keyword)
(octal_number (format) @keyword)
(hex_number (format) @keyword)
(binary_number (value) @number)
(octal_number (value) @number)
(hex_number (value) @number)
(string) @string
(boolean) @boolean
(string_set) @type
(boolean_set) @type
(nat_number_set) @type
(int_number_set) @type
(real_number_set) @type

; Constants, variables, and operators
(variable_declaration (identifier) @variable.builtin)
(constant_declaration (identifier) @constant.builtin)
(constant_declaration (operator_declaration name: (_) @constant.bulitin))
(recursive_declaration (identifier) @operator)
(recursive_declaration (operator_declaration name: (_) @operator))
(operator_definition name: (_) @operator)
(module name: (_) @namespace)
(extends (identifier_ref) @include)
(module_definition name: (identifier) @function)
(function_definition name: (identifier) @function)
(bound_prefix_op symbol: (_) @function.builtin)
(bound_nonfix_op (prefix_op_symbol) @operator)
(bound_infix_op symbol: (_) @function.builtin)
(bound_nonfix_op (infix_op_symbol) @operator)
(bound_postfix_op symbol: (_) @function.builtin)
(bound_nonfix_op (postfix_op_symbol) @operator)
(pcal_macro name: (identifier) @function.macro)
(pcal_macro_call name: (identifier) @function.macro)
(pcal_procedure name: (identifier) @function.macro)
(pcal_algorithm name: (identifier) @namespace)
(pcal_process name: (identifier) @function)
(pcal_var_decl (identifier) @variable.builtin)
("self") @variable.builtin

; Parameters
(operator_definition parameter: (identifier) @parameter)
(operator_definition (operator_declaration name: (_) @variable.parameter))
(module_definition parameter: (identifier) @variable.parameter)
(module_definition (operator_declaration name: (_) @variable.parameter))
(function_definition (quantifier_bound (identifier) @variable.parameter))
(function_definition (quantifier_bound (tuple_of_identifiers (identifier) @variable.parameter)))
(lambda (identifier) @variable.parameter)
(pcal_macro parameter: (identifier) @parameter)
(pcal_p_var_decl (identifier) @parameter)
(record_literal (identifier) @attribute)
(function_literal (quantifier_bound (identifier) @parameter))
(pcal_with (identifier) @parameter)

; Delimiters
[
  (langle_bracket)
  (rangle_bracket)
  (rangle_bracket_sub)
  "{"
  "}"
  "["
  "]"
  "]_"
  "("
  ")"
] @punctuation.bracket
[
  ","
  ":"
  "."
  "!"
  ";"
  (bullet_conj)
  (bullet_disj)
] @punctuation.delimiter

; Proofs
(proof_step_id "<" @punctuation.bracket)
(proof_step_id (level) @number)
(proof_step_id (name) @constant)
(proof_step_id ">" @punctuation.bracket)
(proof_step_ref "<" @punctuation.bracket)
(proof_step_ref (level) @number)
(proof_step_ref (name) @constant)
(proof_step_ref ">" @punctuation.bracket)

; Reference-based identifier highlighting
(identifier_ref) @parameter.reference

; Comments
(comment) @comment
(block_comment "(*" @comment)
(block_comment "*)" @comment)
(block_comment_text) @comment
(single_line) @comment

; Tags
(pcal_stmt label: (identifier) @tag)
(pcal_goto statement: (identifier) @tag)
