====================|||
Solitary Comment
====================|||

---- MODULE Test ----
\* This is a comment
====

--------------------|||

(source_file (module (identifier)
  (comment)
))

====================|||
Comment In Definition
====================|||

---- MODULE Test ----
op == \* This is a comment
    id
====

--------------------|||

(source_file (module (identifier)
  (unit (operator_definition
    (identifier) (def_eq) (comment)
    (identifier)
  ))
))

====================|||
Solitary Block Comment
====================|||

---- MODULE Test ----
(*
This
is
a
multi
line
comment
*)
====

--------------------|||

(source_file (module (identifier)
  (block_comment)
))

====================|||
Block Comment in Expression
====================|||

---- MODULE Test ----
op == 1 +
(*
This
is
a
multi
line
comment
*)
2
====

--------------------|||

(source_file (module (identifier)
  (unit (operator_definition
    (identifier) (def_eq) (bound_infix_op
      (number (nat_number)) (plus)
      (block_comment)
      (number (nat_number))
    )
  ))
))

====================|||
Nested Block Comment
====================|||

---- MODULE Test ----
(*
This
is
a
(*nested*)
multi
line
comment
*)
====

--------------------|||

(source_file (module (identifier)
  (block_comment
    (block_comment)
  )
))

====================|||
Complicated Block Comment
====================|||

---- MODULE Test ----
(*
This
( * )
  is a
    (*(*complicated*) *and* (*nested*)*)
  (*multi
  line*)
comment
)
**()**
*)
====

--------------------|||

(source_file (module (identifier)
  (block_comment
    (block_comment
      (block_comment)
      (block_comment)
    )
    (block_comment)
  )
))
