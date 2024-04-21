---- MODULE Test ----
(*
--algorithm Test {
  {
    if (TRUE)
      skip
    else if (TRUE)
      skip
    else if (TRUE)
      skip
  }
}
*)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF TRUE
               THEN /\ TRUE
               ELSE /\ IF TRUE
                          THEN /\ TRUE
                          ELSE /\ IF TRUE
                                     THEN /\ TRUE
                                     ELSE /\ TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================

