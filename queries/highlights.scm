; ; Intended for consumption by GitHub and the tree-sitter highlight command
; ; Default capture names found here:
; ; https://github.com/tree-sitter/tree-sitter/blob/f5d1c0b8609f8697861eab352ead44916c068c74/cli/src/highlight.rs#L150-L171

; TLA+ Keywords
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
] @keyword

;  PlusCal keywords
[
  "algorithm"
  "assert"
  "await"
  "begin"
  "call"
  "define"
  "either"
  "else" 
  "elsif"
  "end"
  "fair"
  "goto"
  "if" 
  "macro"
  "or"
  "print"
  "procedure"
  "process"
  "return"
  "skip"
  "variable"
  "variables"
  "when"
  "with"
  "then" 
  (pcal_algorithm_start)
  (pcal_end_either)
  (pcal_end_if)
  (pcal_process ("="))
  (pcal_with ("="))
] @keyword

; Literals
(binary_number (format) @keyword)
(binary_number (value) @number)
(boolean) @number
(boolean_set) @type
(hex_number (format) @keyword)
(hex_number (value) @number)
(int_number_set) @type
(nat_number) @number
(nat_number_set) @type
(octal_number (format) @keyword)
(octal_number (value) @number)
(real_number) @number
(real_number_set) @type
(string) @string
(escape_char) @string.special
(string_set) @type

; Namespaces and includes
(extends (identifier_ref) @module)
(module name: (_) @module)
(pcal_algorithm name: (identifier) @module)

; Operators and functions
(bound_infix_op symbol: (_) @function.builtin)
(bound_nonfix_op (infix_op_symbol) @operator)
(bound_nonfix_op (postfix_op_symbol) @operator)
(bound_nonfix_op (prefix_op_symbol) @operator)
(bound_postfix_op symbol: (_) @function.builtin)
(bound_prefix_op symbol: (_) @function.builtin)
(function_definition name: (identifier) @function)
(module_definition name: (identifier) @function)
(operator_definition name: (_) @operator)
(pcal_macro_decl name: (identifier) @function)
(pcal_macro_call name: (identifier) @function)
(pcal_proc_decl name: (identifier) @function)
(pcal_process name: (identifier) @function)
(recursive_declaration (identifier) @operator)
(recursive_declaration (operator_declaration name: (_) @operator))

; Constants and variables
(constant_declaration (identifier) @constant)
(constant_declaration (operator_declaration name: (_) @constant))
(variable_declaration (identifier) @variable.builtin)
(pcal_var_decl (identifier) @variable.builtin)
(pcal_with (identifier) @variable.parameter)
((".") . (identifier) @attribute)
(record_literal (identifier) @attribute)
(set_of_records (identifier) @attribute)

; Parameters
(quantifier_bound (identifier) @variable.parameter)
(quantifier_bound (tuple_of_identifiers (identifier) @variable.parameter))
(lambda (identifier) @variable.parameter)
(module_definition (operator_declaration name: (_) @variable.parameter))
(module_definition parameter: (identifier) @variable.parameter)
(operator_definition (operator_declaration name: (_) @variable.parameter))
(operator_definition parameter: (identifier) @variable.parameter)
(pcal_macro_decl parameter: (identifier) @variable.parameter)
(pcal_proc_var_decl (identifier) @variable.parameter)

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
  (prev_func_val)
  (placeholder)
] @punctuation.delimiter

; Proofs
(proof_step_id "<" @punctuation.bracket)
(proof_step_id (level) @tag)
(proof_step_id (name) @tag)
(proof_step_id ">" @punctuation.bracket)
(proof_step_ref "<" @punctuation.bracket)
(proof_step_ref (level) @tag)
(proof_step_ref (name) @tag)
(proof_step_ref ">" @punctuation.bracket)

; Comments and tags
(block_comment "(*" @comment)
(block_comment "*)" @comment)
(block_comment_text) @comment
(comment) @comment
(single_line) @comment
(_ label: (identifier) @tag)
(label name: (_) @tag)
(pcal_goto statement: (identifier) @tag)

; Reference highlighting
(identifier_ref) @variable.reference
