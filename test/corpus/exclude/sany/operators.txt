=============|||
Nonfix Minus (GH884)
=============|||

---- MODULE Test ----
op == - (1,2)
====

--------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (bound_nonfix_op (infix_op_symbol (minus)) (nat_number) (nat_number))
  )
(double_line)))

=============|||
Nonfix Submodule Excl (GH884)
=============|||

---- MODULE Test ----
op == A!B!!!(x,y)
====

--------------|||

(source_file (module (header_line) name: (identifier) (header_line)
  (operator_definition name: (identifier) (def_eq) definition:
    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:
      (bound_nonfix_op symbol: (infix_op_symbol (excl)) (identifier_ref) (identifier_ref)))
  )
(double_line)))

