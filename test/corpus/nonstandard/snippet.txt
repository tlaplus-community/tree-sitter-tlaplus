=====================|||
Basic Snippet
=====================|||

op == x

---------------------|||

(source_file
  (operator_definition (identifier) (def_eq) (identifier_ref))
)

=====================|||
Snippet with Multiple Definitions
=====================|||

op == x

op == y

---------------------|||

(source_file
  (operator_definition (identifier) (def_eq) (identifier_ref))
  (operator_definition (identifier) (def_eq) (identifier_ref))
)

=====================|||
Snippet with Jlist
=====================|||

op == x

op ==
  /\ 1
  /\ 2
  /\ /\ 3
     /\ 4

---------------------|||

(source_file
  (operator_definition (identifier) (def_eq) (identifier_ref))
  (operator_definition (identifier) (def_eq)
    (conj_list
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (nat_number))
      (conj_item (bullet_conj) (conj_list
        (conj_item (bullet_conj) (nat_number))
        (conj_item (bullet_conj) (nat_number))
      ))
    )
  )
)

=====================|||
Snippet with Proof
=====================|||

op == x

THEOREM TRUE
<*> 1
<0> 2
<*> 3
<0> 4
<*> 5
<0> QED

---------------------|||

(source_file
  (operator_definition (identifier) (def_eq) (identifier_ref))
  (theorem (boolean)
    (non_terminal_proof
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (proof_step (proof_step_id (level) (name)) (suffices_proof_step (nat_number)))
      (qed_step (proof_step_id (level) (name)))
    )
  )
)

=====================|||
Snippet with PlusCal
=====================|||

op == x

(* --algorithm Test
begin
  assert TRUE
end algorithm *)

---------------------|||

(source_file
  (operator_definition (identifier) (def_eq) (identifier_ref))
  (block_comment
    (pcal_algorithm (pcal_algorithm_start) (identifier)
      (pcal_algorithm_body (pcal_assert (boolean)))
    )
  )
)
