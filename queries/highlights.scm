; highlights.scm
; Default capture names for tree-sitter highlight found here:
; https://github.com/tree-sitter/tree-sitter/blob/59cd1c3962d5b39e07bff3d5e5449c8b78e7cf61/cli/src/highlight.rs#L150-L172

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
  (def_eq)
  (set_in)
  (gets)
  (forall)
  (exists)
  (temporal_forall)
  (temporal_exists)
  (all_map_to)
  (maps_to)
  (case_box)
  (case_arrow)
  (address)
] @keyword

; Literals
(number) @number
(string) @string
(primitive_value_set) @type

; Comments
(comment) @comment
(block_comment) @comment
(unit (single_line) @comment)

; Constants, variables, and operators
(constant_declaration (identifier) @constant)
(variable_declaration (identifier) @variable.builtin)
(bound_prefix_op symbol: (_) @operator)
(bound_infix_op symbol: (_) @operator)
(bound_postfix_op symbol: (_) @operator)

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
  (bullet_conj)
  (bullet_disj)
] @punctuation.delimiter
