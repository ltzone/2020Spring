
(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/03/14.                                             *)
(* Due: 2020/03/18, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment2.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment2.vo" file is generated.         *)
(*                                                                   *)
(* 5. Do not copy and paste others' answer.                          *)
(*                                                                   *)
(* 6. Using any theorems and/or tactics provided by Coq's standard   *)
(*    library is allowed in this assignment, if not specified.       *)
(*                                                                   *)
(* 7. When you finish, answer the following question:                *)
(*                                                                   *)
(*      Who did you discuss with when finishing this                 *)
(*      assignment? Your answer to this question will                *)
(*      NOT affect your grade.                                       *)
(*      myself                                                       *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import PL.Imp.
Require Import PL.ImpExt1.
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
Import derived_rules.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

Hypothesis triple01: forall m: Z,
  {{ {[X]} = m }}
  Y ::= 0
  {{ {[Y]} = 0 }}.

Hypothesis triple02: forall m: Z,
  {{ {[X]} = m }}
  Y ::= 0
  {{ {[X]} + {[Y]} = m }}.

Hypothesis triple03: forall m: Z,
  {{ {[X]} = m }}
  Y ::= 0
  {{ {[X]} = m AND {[Y]} = 0 }}.

Hypothesis triple04: forall m: Z,
  {{ {[X]} + {[Y]} = m AND {[! (X == 0)]} }}
  X ::= X - 1
  {{ {[X]} + {[Y]} = m - 1 }}.

Hypothesis triple05: forall m: Z,
  {{ {[X]} + {[Y]} = m AND {[! (X == 0)]} }}
  X ::= X - 1
  {{ {[X]} + {[Y + 1]} = m }}.

Hypothesis triple06: forall m: Z,
  {{ {[X]} + {[Y]} = m - 1 }}
  Y ::= Y + 1
  {{ True }}.

Hypothesis triple07: forall m: Z,
  {{ {[X]} + {[Y + 1]} = m }}
  Y ::= Y + 1
  {{ {[X]} + {[Y]} = m }}.

(** **** Exercise: 2 stars, standard (slow_asgn)  *)

Hypothesis der1: forall m: Z,
  {[X]} + {[Y]} = m AND NOT {[!(X == 0)]} |-- {[Y]} = m.

Fact slow_asgn_correct: forall m: Z,
      {{ {[X]} = m }}
      Y ::= 0;;
      While !(X == 0) Do
        X ::= X - 1;;
        Y ::= Y + 1
      EndWhile
      {{ {[Y]} = m }}.
Proof.
  intros.
  eapply hoare_consequence_post; [| apply der1].
  apply (hoare_seq _ _ _ _ _ (triple02 m)).
  apply hoare_while.
  apply (hoare_seq _ _ _ _ _ (triple05 m)).
  apply triple07.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (slow_asgn)  *)

Hypothesis der2_1: forall m n: Z,
  {[X]} = m AND {[Y]} = n |-- {[X]} + {[Y]} = (m + n)%Z.

Hypothesis der2_2: forall m n: Z,
  {[X]} + {[Y]} = (m + n)%Z AND NOT {[!(X == 0)]} |-- {[Y]} = m + n.

Fact slow_add: forall m n: Z,
      {{ {[X]} = m AND {[Y]} = n }}
      While !(X == 0) Do
        X ::= X - 1;;
        Y ::= Y + 1
      EndWhile
      {{ {[Y]} = m + n }}.
Proof.
  intros.
  eapply hoare_consequence; [apply der2_1 | | apply der2_2].
  apply hoare_while.
  apply (hoare_seq _ _ _ _ _ (triple05 (m+n))).
  apply triple07.
Qed.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2 *)

(** Find out the pre/postconditions of assignment commands according to
[hoare_asgn_fwd] and [hoare_asgn_bwd]. *)

Module Task2_Example.
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().
Local Instance U: var := new_var().
Local Instance V: var := new_var().

(** For the following assignment command，write down the postcondition defined
by [hoare_asgn_fwd]. (Here, [X], [Y], [U] and [V] are program variables.

    {{ {[X * Y]} == k + {[U * V]} }}
    X ::= X + Y
    {{ ??? }}
*)
Definition post (k: Z): Assertion :=
  EXISTS x, {[x * Y]} = k + {[U * V]} AND {[X]} = {[x + Y]}.

(** Hint: you can actually check whether such an answer is correct using Coq.
Here is a proof script. Remark: this is only for illustration. For your
assignment later, it is NOT necessary to write a proof. *)

Goal forall k: Z,
      {{ {[X * Y]} = k + {[U * V]} }}
      X ::= X + Y
      {{ EXISTS x, {[x * Y]} = k + {[U * V]} AND {[X]} = {[x + Y]} }}.
Proof.
  intros.
  pose proof hoare_asgn_fwd
             ({[X * Y]} = k + {[U * V]})%assert
             X
             (X + Y).
  assert_subst in H.
  exact H.
Qed.

(** Remark: you should NOT write:

  EXISTS x, x * {[Y]} = k + {[U]} * {[V]} AND {[X]} = x + {[Y]}

although you might gain this assertion using [assert_simpl]. It is NOT the
postcondition generated by [hoare_asgn_fwd]. It is only equivalent to that.
*)

End Task2_Example.

(** **** Exercise: 1 star, standard  *)
Module Task2_1.
Import Axiomatic_semantics.

Local Instance A: var := new_var().
Local Instance B: var := new_var().
Local Instance C: var := new_var().

(** For the following assignment command，write down the postcondition defined
by [hoare_asgn_fwd].

    {{ 0 <= {[A + B + C]} AND {[A]} <= 0 }}
    A ::= 0
    {{ ??? }}
*)

Definition post: Assertion := 
  EXISTS a, (0 <= {[a + B + C]} AND {[a]} <=0 ) AND {[A]} = {[0]}.

End Task2_1.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_2.
Import Axiomatic_semantics.

Local Instance A: var := new_var().
Local Instance B: var := new_var().

(** For the following assignment command，write down the postcondition defined
by [hoare_asgn_fwd].

    {{ 0 <= {[A]} + {[B]} AND {[A]} * {[B]} <= 100 }}
    A ::= A + B
    {{ ??? }}
*)


Definition post: Assertion :=
  EXISTS a, (0 <= {[a]} + {[B]} AND {[a]} * {[B]} <= 100) AND {[A]} = {[a + B]}.

End Task2_2.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_3.
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** For the following assignment command，write down the postcondition defined
by [hoare_asgn_fwd].

    {{ EXISTS x, x = a AND {[Y]} = b AND {[X]} = x + b }}
    Y ::= X - Y
    {{ ??? }}
*)

Definition post (a b: Z): Assertion :=
  EXISTS y, (EXISTS x, x = a AND {[y]} = b AND {[X]} = x + b) AND {[Y]} = {[X - y]}.

End Task2_3.
(** [] *)

(** **** Exercise: 4 stars, standard  *)
Module Task2_4.
Require Import Coq.Lists.List.
Import ListNotations.  
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** For the following assignment command，write down the precondition defined
by [hoare_asgn_bwd].

    {{ ??? }}
    Y ::= X - Y
    {{ {[X]} = x + y AND {[Y]} = x }}
*)

Definition pre (x y: Z): Assertion :=
  {[X]} = x + y AND {[X - Y]} = x.

(** Reversely, consider the same assignment command, please write down the
strongest postcondition defined by [hoare_asgn_fwd]

    {{ Your_precondition [pre] }}
    Y ::= X - Y
    {{ ??? }}
*)

Definition post (x y: Z): Assertion :=
  EXISTS z, ({[X]} = x + y AND {[X - z]} = x) AND {[Y]} = {[X - z]}.

(** Now, if comparing the original postcondition and the strongest postcondition
that you just wrote down. Which one in the following statements is correct?

1. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is strictly
   stronger.

2. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is strictly
   weaker.

3. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is equivalent
   to that strongest postcondition of weakest precondition.

4. They two are not comparable. *)

Definition the_correct_statement_number: Z := 3.

(** More generally, consider an arbitrary assertion [P] and an assignment
command [X ::= E] in our simple toy programming language. Let [Q] be the weakest
precondition of [P] and [X ::= E] and let [R] be the strongest postcondition of
[Q] and [X ::= E]. Which statements about [P] and [R] may be true?

1. [P] is strictly stronger than [R].

2. [P] is strictly weaker than [R].

3. [P] is equivalent to [R].

4. [P] and [R] are not comparable.

Hint: this is a multiple-choice problem. You should use a Coq list to describe
your answer, e.g. [1; 2; 3; 4], [1; 3], [2]. *)

Definition the_statements_that_may_be_true: list Z := [2; 3].

End Task2_4.
(** [] *)

(* ################################################################# *)
(** * Task 3 *)

(** Both of the following programs calculate the minimum number of [X] and [Y].
We provide decorated programs to verify them. You are going to formalize these
proofs in Coq. Related assertion derivation has been claimed as hypotheses.
You do not need to add more hypothesis.

    min_if:
      If A <= B
      Then C ::= A
      Else C ::= B
      EndIf

    min_while:
      C ::= 0;;
      While (! (A == 0) && ! (B == 0)) Do
        A ::= A - 1;;
        B ::= B - 1;;
        C ::= C + 1
      EndWhile
*)

Module Task3.
Import Axiomatic_semantics.
Import derived_rules.

Local Instance A: var := new_var().
Local Instance B: var := new_var().
Local Instance C: var := new_var().

(** Here is the decorated program for [min_if]:

  /* {[A]} = a AND {[B]} = b */
  If A <= B
  Then
    /* {[A]} = a AND {[B]} = b AND {[A <= B]} */
    /* {[A]} = a AND a <= b */
    C ::= A
    /* EXISTS c, {[A]} = a AND a <= b AND {[C]} = {[A]} */
    /* {[A]} = a AND a <= b AND {[C]} = {[A]} */
    /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */
  Else
    /* {[A]} = a AND {[B]} = b AND NOT {[A <= B]} */
    /* {[B]} = b AND b < a */
    C ::= B
    /* EXISTS c, {[B]} = b AND b < a AND {[C]} = {[B]} */
    /* {[B]} = b AND b < a AND {[C]} = {[B]} */
    /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */
  EndIf
  /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */.

And here are the derivation needed in proof. *)

Hypothesis der1_1: forall a b: Z,
  {[A]} = a AND {[B]} = b AND {[A <= B]} |-- 
  {[A]} = a AND a <= b.

Hypothesis der1_2: forall a b: Z,
  {[A]} = a AND a <= b AND {[C]} = {[A]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

Hypothesis der1_3: forall a b: Z,
  {[A]} = a AND {[B]} = b AND NOT {[A <= B]} |-- 
  {[B]} = b AND b < a.

Hypothesis der1_4: forall a b: Z,
  {[B]} = b AND b < a AND {[C]} = {[B]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

(** Now, your task is to write a formal Coq proof.  Hint: [hoare_asgn_fwd] will
be useful in this proofs.*)

(** **** Exercise: 2 stars, standard (min_if_correct)  *)
Fact min_if_correct: forall a b: Z,
      {{ {[A]} = a AND {[B]} = b }}
      If A <= B
      Then C ::= A
      Else C ::= B
      EndIf
      {{ {[C]} = a AND a <= b OR {[C]} = b AND b < a }}.
Proof.
  intros.
  apply hoare_if.
  - eapply hoare_consequence;[apply der1_1|apply hoare_asgn_fwd|].
    assert_subst. assert_simpl. apply der1_2.
  - eapply hoare_consequence;[apply der1_3|apply hoare_asgn_fwd|].
    assert_subst. assert_simpl. apply der1_4.
Qed.

(** [] *)

(** Here is the decorated program for [min_while]:

  /* {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b */
  /* {[A]} + {[0]} = a AND 0 <= a AND a <= b OR {[B]} + {[0]} = b AND 0 <= b AND b < a */
  C ::= 0;;
  /* {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a */
  While (! (A == 0) && ! (B == 0)) Do
    /* ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
        {[B]} + {[C]} = b AND 0 <= b AND b < a) AND
       {[! (A == 0) && ! (B == 0)]} */
    /* {[A - 1]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a */
    A ::= A - 1;;
    /* {[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a */
    B ::= B - 1;;
    /* {[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B]} + {[C + 1]} = b AND 0 <= b AND b < a */
    C ::= C + 1
    /* {[A]} + {[C]} = a AND 0 <= a AND a <= b OR
       {[B]} + {[C]} = b AND 0 <= b AND b < a */
  EndWhile
  /* ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
      {[B]} + {[C]} = b AND 0 <= b AND b < a) AND
     NOT {[! (A == 0) && ! (B == 0)]} */
  /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */.

And here are the derivation needed in proof. *)

Hypothesis der2_1: forall a b: Z,
  {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b |--
  {[A]} + {[0]} = a AND 0 <= a AND a <= b OR {[B]} + {[0]} = b AND 0 <= b AND b < a.

Hypothesis der2_2: forall a b: Z,
  ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)
  AND {[! (A == 0) && ! (B == 0)]} |--
  {[A - 1]} + {[C + 1]} = a AND 0 <= a AND a <= b OR {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a.

Hypothesis der2_3: forall a b: Z,
  {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a |--
  {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a.

Hypothesis der2_4: forall a b: Z,
  ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)
  AND NOT {[! (A == 0) && ! (B == 0)]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

(** Now, your task is to write a formal Coq proof.  Hint: [hoare_asgn_bwd] will
be useful in this proofs.*)

(** **** Exercise: 3 stars, standard (min_while_correct)  *)
Fact min_while_correct: forall a b: Z,
      {{ {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b }}
      C ::= 0;;
      While (! (A == 0) && ! (B == 0)) Do
        A ::= A - 1;;
        B ::= B - 1;;
        C ::= C + 1
      EndWhile
      {{ {[C]} = a AND a <= b OR {[C]} = b AND b < a }}.
Proof.
  intros.
  eapply hoare_consequence.
  1: { apply der2_1. }
  2: { apply der2_4. }
  pose proof hoare_asgn_bwd
            ({[A]} + {[C]} = a AND 0 <= a AND a <= b 
              OR {[B]} + {[C]} = b AND 0 <= b AND b < a)%assert
             C 0.
  assert_subst in H.
  eapply hoare_seq. apply H. clear H.
  eapply hoare_while.
  eapply hoare_consequence_pre;[apply der2_2|].
  pose proof hoare_asgn_bwd
             ({[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
              {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a)%assert
             A (A-1).
  assert_subst in H. eapply hoare_seq. apply H. clear H.
  pose proof hoare_asgn_bwd
             ({[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
              {[B]} + {[C + 1]} = b AND 0 <= b AND b < a)%assert
              B (B-1).
  assert_subst in H. eapply hoare_seq. apply H. clear H.
  pose proof hoare_asgn_bwd
             ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
              {[B]} + {[C]} = b AND 0 <= b AND b < a)%assert
              C (C+1).
  assert_subst in H. apply H.
Qed.
(** [] *)

End Task3.

(* ################################################################# *)
(** * Task 4 *)

(** In this task you need to derive more rules from primary rules. *)

Module Task4.

Import Axiomatic_semantics.
Import derived_rules.

(** **** Exercise: 2 stars, standard (hoare_while_single)  *)
Lemma hoare_while_single: forall P Q R b c,
  P |-- Q ->
  {{ Q AND {[ b ]} }} c {{ Q }} ->
  Q AND NOT {[ b ]} |-- R ->
  {{ P }} While b Do c EndWhile {{ R }}.
Proof.
  intros.
  eapply hoare_consequence.
  - exact H.
  - apply hoare_while. apply H0.
  - apply H1.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (hoare_if_then)  *)
Lemma hoare_if_then: forall P Q b c,
  {{ P AND {[ b ]} }} c {{ Q }} ->
  P AND NOT {[ b ]} |-- Q ->  
  {{ P }} If b Then c Else Skip EndIf {{ Q }}.
Proof.
  intros. apply hoare_if.
  - apply H.
  - eapply hoare_consequence_pre.
    + apply H0.
    + apply hoare_skip.
Qed.
(** [] *)

End Task4.

(* Sat Mar 14 21:18:27 CST 2020 *)
