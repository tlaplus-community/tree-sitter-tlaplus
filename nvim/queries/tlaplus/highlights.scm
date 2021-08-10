; highlights.scm

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
] @keyword

[
  (forall)
  (exists)
  (temporal_forall)
  (temporal_exists)
  (set_in)
  (def_eq)
] @keyword.function

; Literals
(number) @number
(string) @string
(boolean) @boolean
(primitive_value_set) @type

; Comments
(comment) @comment
(block_comment) @comment
(unit (single_line) @comment)
(extramodular_text) @text

; Constants, variables, and operators
(module name: (identifier) @namespace)
(extends (identifier_ref) @namespace)
(instance (identifier_ref) @namespace)
(module_definition (identifier) @namespace)
(variable_declaration (identifier) @variable)
(constant_declaration (identifier) @constant)
(bound_prefix_op symbol: (_) @operator)
(bound_infix_op symbol: (_) @operator)
(bound_postfix_op symbol: (_) @operator)
(prev_func_val) @punctuation.special
(bullet_conj) @punctuation.special
(bullet_disj) @punctuation.special
(proof_step_id (level) @number)
(proof_step_id (name) @symbol)
(proof_step_ref (level) @number)
(proof_step_ref (name) @symbol)

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
  "<"
  ">"
] @punctuation.delimiter

