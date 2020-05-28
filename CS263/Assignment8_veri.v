Require Import PL.Imp_CF.

Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.

(* ################################################################# *)
(** * Task 1 *)

(** Pick Hoare triples from the following hypothesis list and finish proofs.
You only need to use [hoare_seq], [hoare_skip], [hoare_if] and/or
[hoare_while]. *)

Module Task1.
Import Axiomatic_semantics.


Local Instance X: var := new_var().

Fact veri1 : forall n,
       {{ {[ X ]} = n }}
          X ::= X - 1
       {{ {[ X ]} = n - 1 }}
       {{ False }}
       {{ {[ X ]} = n - 1 }}.
Proof. intros.
  eapply hoare_consequence.
  - apply derives_refl.
  - apply hoare_asgn_fwd.
  - assert_subst. admit.
  - apply derives_refl.
  - apply False_left.
Admitted.

