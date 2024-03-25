===================|||
Conjunct Inside Ambiguous Case (GH487)
===================|||

---- MODULE Test ----
op ==
  CASE A ->
    /\ CASE B -> C
       [] D -> E
  [] F -> G

op2 ==
  CASE H ->
    /\ CASE I -> J
       [] OTHER -> K
  [] L -> M

op3 ==
  CASE N ->
    /\ CASE O -> P
       [] Q -> R
    /\ S
  [] T -> U
====

-------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list (conj_item (bullet_conj)
        (case
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          (case_box)
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
        )
      )))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list (conj_item (bullet_conj)
        (case
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          (case_box)
          (other_arm (case_arrow) (identifier_ref))
        )
      )))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list
        (conj_item (bullet_conj)
          (case
            (case_arm (identifier_ref) (case_arrow) (identifier_ref))
            (case_box)
            (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          )
        )
        (conj_item (bullet_conj) (identifier_ref))
      ))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
(double_line)))

===================|||
Unicode Conjunct Inside Ambiguous Case (GH487)
===================|||

---- MODULE Test ----
op ≜
  CASE A →
    ∧ CASE B → C
       □ D → E
  □ F → G

op2 ≜
  CASE H →
    ∧ CASE I → J
       □ OTHER → K
  □ L → M

op3 ≜
  CASE N →
    ∧ CASE O → P
       □ Q → R
    ∧ S
  □ T → U
====

-------------------|||

(source_file (module (header_line) (identifier) (header_line)
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list (conj_item (bullet_conj)
        (case
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          (case_box)
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
        )
      )))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list (conj_item (bullet_conj)
        (case
          (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          (case_box)
          (other_arm (case_arrow) (identifier_ref))
        )
      )))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
  (operator_definition (identifier) (def_eq)
    (case
      (case_arm (identifier_ref) (case_arrow) (conj_list
        (conj_item (bullet_conj)
          (case
            (case_arm (identifier_ref) (case_arrow) (identifier_ref))
            (case_box)
            (case_arm (identifier_ref) (case_arrow) (identifier_ref))
          )
        )
        (conj_item (bullet_conj) (identifier_ref))
      ))
      (case_box)
      (case_arm (identifier_ref) (case_arrow) (identifier_ref))
    )
  )
(double_line)))
