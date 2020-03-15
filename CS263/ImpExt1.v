Require Import PL.Imp.

Module derived_rules.

Import Concrete_Pretty_Printing.
Import Assertion_S_Rules.
Import Axiomatic_semantics.

Corollary hoare_consequence_pre: forall P P' Q c,
  P |-- P' ->
  {{ P' }} c {{ Q }} ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + apply derives_refl.
Qed.

Corollary hoare_consequence_post: forall P Q Q' c,
  {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + exact H.
  + exact H0.
Qed.

Corollary hoare_if_weak : forall P Q b c1 c2,
  {{P}} c1 {{Q}} ->
  {{P}} c2 {{Q}} ->
  {{P}} If b Then c1 Else c2 EndIf {{Q}}.
Proof.
  intros.
  apply hoare_if.
  + eapply hoare_consequence_pre.
    2: { exact H. }
    apply AND_left1.
    apply derives_refl.
  + eapply hoare_consequence_pre.
    2: { exact H0. }
    apply AND_left1.
    apply derives_refl.
Qed.

Corollary hoare_asgn_seq: forall P `(X: var) E c Q,
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }} c {{ Q }} ->
  {{ P }} X ::= E ;; c {{ Q }}.
Proof.
  intros.
  eapply hoare_seq.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

Corollary hoare_asgn_conseq: forall P `(X: var) E Q,
  EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} |-- Q ->
  {{ P }} X ::= E {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence_post.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

End derived_rules.

(* Sat Mar 14 21:18:27 CST 2020 *)
