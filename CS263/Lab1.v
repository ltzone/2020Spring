(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1. *)

Require Import Coq.micromega.Psatz.
Require Import PL.Imp.
Require Import PL.ImpExt1.
Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.

(* ################################################################# *)
(** * Proving the following first order logic theorem *)

(** Remember how to reason about FOL connectives?
    - for [/\], using [destruct] (for assumptions)
                  and [split] (for conclusions)
    - for [\/], using [destruct] (for assumptions)
                  and [left]/[right] (for conclusions)
    - for [exists], using [destruct] (for assumptions)
                  and [exists] (for conclusions)
    - for [->] and [forall], using [apply]/[pose proof]/[specialize]
                  (for assumptions) and [intros] (for conclusions)
    - for [~] and [False], using [contradiction] and [pose proof classic].
*)

(** **** Exercise: 2 stars, standard (swap_assum)  *)
Theorem swap_assum : forall (P Q R : Prop),
  (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros.
  specialize (H H1 H0).
  apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  intros HP.
  specialize (H HP).
  contradiction.
Qed.
(** [] *)

Theorem and_dup: forall (P: Prop),
  P <-> P /\ P.
Proof.
  intros.
  unfold iff.
  split.
  - intros. split;[apply H|apply H].
  - intros. destruct H. apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (and_not_or)  *)
Theorem and_not_or: forall (P Q: Prop),
  ~ P /\ ~ Q -> ~ (P \/  Q).
Proof.
  intros.
  intros C.
  destruct H as [HP HQ].
  destruct C.
  - contradiction.
  - contradiction.
Qed.

(** [] *)

(* ################################################################# *)
(** * Proving the following assertion derivation *)

(** How to reduce assertion derivation to normal Coq propositions? Using
    [entailer]. How to prove arithmetic facts automatically? Using [lia] or
    [nia]. *)

Module assertion_derivation.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** **** Exercise: 1 star, standard (der1)  *)
Fact der1: 0 <= {[X]} AND 0 <= {[Y]} |-- 0 <= {[X + Y]}.
Proof.
  entailer.
  intros.
  lia.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (der2)  *)
Fact der2: EXISTS k, {[X]} = k * 4 |-- EXISTS k, {[X]} = k * 2.
Proof.
  entailer.
  intros.
  destruct H as [k H].
  exists (k*2).
  lia.
Qed.
(** [] *)

End assertion_derivation.

(* ################################################################# *)
(** * Verifying the following programs *)

(** Here is a list of derived rules that might be useful:

    - hoare_consequence_pre
    - hoare_consequence_post
    - hoare_asgn_seq
    - hoare_asgn_conseq.

    Also, remember that [assert_subst] and [assert_simpl] can be used for
    simplifying assertions. *)

Module squaring.
Import Axiomatic_semantics.
Import derived_rules.

Local Instance X: var := new_var().
Local Instance RES: var := new_var().
Local Instance I: var := new_var().
Local Instance J: var := new_var().

(** The following derivation will be useful. *)

(** **** Exercise: 2 stars, standard (der_before_loop)  *)
Lemma der_before_loop: forall m: Z,
  {[X]} = m AND {[I]} = 0 AND {[RES]} = 0 |--
  {[RES]} = {[I]} * m AND {[X]} = m.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (der_in_loop_body)  *)
Lemma der_in_loop_body: forall m: Z,
  EXISTS x, {[x]} = {[I]} * m AND {[X]} = m AND
            {[! (I == X)]} AND {[RES]} = {[x + X]} |--
  {[RES]} = {[I]} * m + m AND {[X]} = m.
Proof.
  intros.
  entailer.
  intros.
  destruct H as [k [[[? ?] ?] ?]].
  lia.
Qed.
 
(** [] *)

(** **** Exercise: 2 stars, standard (der_after_loop)  *)
Lemma der_after_loop_body: forall m: Z,
  EXISTS x, {[RES]} = {[x]} * m + m AND {[X]} = m AND {[I]} = {[x + 1]} |--
  {[RES]} = {[I]} * m AND {[X]} = m.
Proof.
  intros.
  entailer.
  intros.
  destruct H as [k' [[? ?] ?]].
  lia.
Qed.
(** [] *)

Lemma der: {{ False }} While (X == X) Do Skip EndWhile {{ False }}.
Proof.
  eapply hoare_consequence.
  2: { eapply hoare_while with (P:=  (True)%assert).
       eapply hoare_consequence. 2 :{ eapply hoare_skip. }
       apply derives_refl. entailer. tauto. }
  entailer. tauto.
  entailer. tauto.
Qed.
(** **** Exercise: 2 stars, standard (der_after_loop)  *)
Lemma der_after_loop: forall m: Z,
  {[RES]} = {[I]} * m AND {[X]} = m AND NOT {[! (I == X)]} |-- {[RES]} = m * m.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.
(** [] *)

(** Hint: you can use {[RES]} == {[I]} * m AND {[X]} == m as your loop invariant. *)
(** **** Exercise: 3 stars, standard (square1_correct)  *)
Fact square1_correct: forall m: Z,
  {{ {[X]} = m }}
  I ::= 0;;
  RES ::= 0;;
  While !(I == X)  Do
    RES ::= RES + X;;
    I ::= I + 1
  EndWhile
  {{ {[RES]} = m*m }}.
Proof.
  intros.
  eapply hoare_seq.
  apply hoare_asgn_fwd.
  assert_subst;assert_simpl.
  eapply hoare_consequence_post.
  2: { apply der_after_loop. }
  eapply hoare_seq.
  { eapply hoare_asgn_fwd. }
  assert_subst.
  eapply hoare_consequence_pre.
  2: { apply (hoare_while
        ({[RES]} = {[I]} * m AND {[X]} = m)%assert).
       eapply hoare_seq.
       - apply hoare_asgn_fwd.
       - assert_subst.
         eapply hoare_consequence.
         + apply der_in_loop_body.
         + apply hoare_asgn_fwd.
         + apply der_after_loop_body.
     }
  1: { assert_simpl. 
       apply der_before_loop. }
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard (square2_correct)  *)

Lemma der_into_first_loop : forall m:Z,
 {[X]} = m AND {[I]} = 0 AND {[RES]} = 0
|-- {[RES]} = {[I]} * {[I]} AND {[X]} = m AND 0 <= {[I]}.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.

Lemma der_after_first_loop : forall m:Z, 
{[RES]} = {[I]} * {[I]} AND {[X]} = m AND 0 <= {[I]} AND NOT {[! (I == X)]}
|-- {[RES]} = m * m.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.

Lemma der_into_second_loop : forall m:Z,
{[RES]} = {[I]} * {[I]} AND {[X]} = m AND 0 <= {[I]} AND NOT {[I]} = {[X]}
AND {[J]} = {[I]} + {[I]} + 1
|-- {[RES]} + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
    AND {[X]} = m AND 0 <= {[I]}.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.

Lemma der_after_second_loop: forall m:Z,
{[RES]} + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
AND {[X]} = m AND 0 <= {[I]} AND NOT {[! (J <= 0)]} 
|-- {[RES]} = {[I + 1]} * {[I + 1]} AND {[X]} = m AND 0 <= {[I + 1]}.
Proof.
  intros. 
  entailer.
  intros.
  lia.
Qed.

Lemma der_second_loop_body: forall m:Z,
EXISTS x,
  {[x]} + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
  AND {[X]} = m AND 0 <= {[I]} AND {[! (J <= 0)]} AND 
  {[RES]} = {[x + 1]}
|--
  {[RES]} - 1 + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
  AND {[X]} = m AND 0 <= {[I]} AND {[! (J <= 0)]} .
Proof.
  intros. 
  entailer.
  intros.
  destruct H as [k H].
  lia.
Qed.

Lemma der_second_loop_body2: forall m:Z,
EXISTS x,
({[RES]} - 1 + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
 AND {[X]} = m AND 0 <= {[I]} AND {[! (J <= 0)]}) [J |-> x]
AND {[J]} = {[(J - 1) [J |-> x]]}
|-- {[RES]} + {[J]} = {[I]} * {[I]} + {[I]} + {[I]} + 1 AND 0 <= {[J]}
    AND {[X]} = m AND 0 <= {[I]}.
Proof.
  intros. 
  entailer.
  intros.
  destruct H as [k H].
  lia.
Qed.


Fact square2_correct: forall m: Z,
  {{ {[X]} = m }}
  I ::= 0;;
  RES ::= 0;;
  While !(I == X)  Do
    J ::= I + I + 1;;
    While !(J <= 0) Do
      RES ::= RES + 1;;
      J ::= J - 1
    EndWhile;;
    I ::= I + 1
  EndWhile
  {{ {[RES]} = m*m }}.
Proof.
  intros.
  apply hoare_asgn_seq.
  assert_subst. assert_simpl.
  apply hoare_asgn_seq.
  assert_subst. assert_simpl.
  
  eapply hoare_consequence;
  [ apply der_into_first_loop
  | apply (hoare_while ({[RES]} = {[I]} * {[I]} AND {[X]} = m AND 0 <= {[I]})%assert)
  | apply der_after_first_loop].

  apply hoare_asgn_seq.
  assert_subst. assert_simpl.
  
  eapply hoare_seq.
  - eapply hoare_consequence;
    [ apply der_into_second_loop
    | apply (hoare_while
       ({[RES]}+{[J]} = {[I]}*{[I]} + {[I]} + {[I]} + 1
        AND 0 <= {[J]} AND {[X]} = m AND 0 <= {[I]})%assert)
    | apply der_after_second_loop].
    apply hoare_asgn_seq.
    assert_subst.
    eapply hoare_consequence;
    [ apply der_second_loop_body
    | apply hoare_asgn_fwd
    | apply der_second_loop_body2].
  - eapply hoare_consequence_pre;[|apply hoare_asgn_bwd].
    assert_subst. apply derives_refl.
Qed.
(** [] *)

End squaring.

(* Wed Mar 18 23:56:01 CST 2020 *)
