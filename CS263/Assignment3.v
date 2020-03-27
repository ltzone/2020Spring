(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/03/26.                                             *)
(* Due: 2020/03/30, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment3.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment3.vo" file is generated.         *)
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
(*      (* FILL IN YOUR ANSWER HERE AS COMMENT *)                    *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import PL.Imp.
Require Import PL.ImpExt1.
Require Import PL.ImpExt2.
Require Import Coq.micromega.Psatz.

(* ################################################################# *)
(** * Task 1: Hoare Logic Based Verification *)

Module Task1.
Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.
Import Axiomatic_semantics.
Import derived_rules.

Module Task1_1.
Import Axiomatic_semantics.
Import derived_rules.

(** **** Exercise: 3 stars, standard (tri_correct)  *)

(** The following program try to find the smallest number [N] such
that [1 + 2 + 3 + .. + N > X].

    S ::= 0;;
    N ::= 0;;
    While S <= X Do
      N ::= N + 1;;
      S ::= S + N
    EndWhile.

Remember, you can always add auxiliary lemmas before start proving
the main theorem in every subtasks. But of course, these lemmas needs
to be proved. *)

Local Instance X: var := new_var().
Local Instance S: var := new_var().
Local Instance N: var := new_var().

Lemma enter_loop: 
0 <= {[X]} AND {[S]} = 0 AND {[N]} = 0 
|-- 2 * {[S]} = {[N]} * ({[N]} + 1) AND {[N]} * ({[N]} - 1) <= 2 * {[X]}.
Proof.
  entailer.
  intros.
  lia.
Qed.

Lemma after_loop:
2 * {[S]} = {[N]} * ({[N]} + 1) AND {[N]} * ({[N]} - 1) <= 2 * {[X]}
AND NOT {[S <= X]}
|-- {[N]} * ({[N]} - 1) <= 2 * {[X]} AND 2 * {[X]} < {[N]} * ({[N]} + 1).
Proof.
  entailer.
  intros.
  lia.
Qed.

Lemma loop_body:
  EXISTS x,
  2 * {[S]} = x * (x + 1) AND x * (x - 1) <= 2 * {[X]} AND {[S]} <= {[X]}
  AND {[N]} = x + 1 
|--   2 * {[S]} = ({[N]} - 1) * {[N]} 
 AND ({[N]} - 1) * ({[N]} - 2) <= 2 * {[X]} AND {[S]} <= {[X]} .
Proof.
  entailer.
  intros.
  destruct H as [k H].
  lia.
Qed.

Lemma exit_loop:
EXISTS x,
(2 * {[S]} = ({[N]} - 1) * {[N]} AND ({[N]} - 1) * ({[N]} - 2) <= 2 * {[X]}
 AND {[S]} <= {[X]}) [S |-> x] AND {[S]} = {[(S + N) [S |-> x]]}
|-- 2 * {[S]} = {[N]} * ({[N]} + 1) AND {[N]} * ({[N]} - 1) <= 2 * {[X]}.
Proof.
  entailer.
  intros.
  destruct H as [k H].
  lia.
Qed.

Fact tri_correct:
  {{ 0 <= {[X]} }}
    S ::= 0;;
    N ::= 0;;
    While S <= X Do
      N ::= N + 1;;
      S ::= S + N
    EndWhile
  {{ {[N * (N-1)]} <= 2 * {[X]} AND
     2 * {[X]} < {[N * (N + 1)]} }}.
Proof.
  apply hoare_asgn_seq.
  apply hoare_asgn_seq.
  assert_simpl.
  eapply hoare_consequence;
  [ apply enter_loop |
  | apply after_loop].
  apply hoare_while.
  apply hoare_asgn_seq.
  assert_subst. assert_simpl.
  eapply hoare_consequence;
  [ apply loop_body
  | apply hoare_asgn_fwd
  | apply exit_loop].
Qed.

(** [] *)

End Task1_1.

Module Task1_2.
Import Axiomatic_semantics.
Import derived_rules.

(** **** Exercise: 3 stars, standard (sqrt_correct)  *)

(** The following program computes the integer part of [X]'s square
root.

    I ::= 0;;
    While (I+1)*(I+1) <= X Do
      I ::= I+1
    EndWhile.

Your task is to prove its correctness. *)

Local Instance X: var := new_var().
Local Instance I: var := new_var().

Lemma into_loop: forall m:Z,
0 <= {[X]} AND {[X]} = m AND {[I]} = 0
|-- 0 <= {[X]} AND {[X]} = m AND  {[I]} * {[I]} <= m.
Proof.
  intros.
  entailer.
  intros.
  lia.
Qed.

Lemma after_loop: forall m:Z,
0 <= {[X]} AND {[X]} = m AND {[I]} * {[I]} <= m AND NOT {[(I + 1) * (I + 1) <= X]}
|-- {[I]} * {[I]} <= m AND m < ({[I]} + 1) * ({[I]} + 1).
Proof.
  intros.
  entailer.
  intros. 
  lia.
Qed.

Lemma loop_body: forall m:Z,
EXISTS x,
(0 <= {[X]} AND {[X]} = m AND {[I]} * {[I]} <= m AND {[(I + 1) * (I + 1) <= X]})
[I |-> x] AND {[I]} = {[(I + 1) [I |-> x]]}
|-- 0 <= {[X]} AND {[X]} = m AND {[I]} * {[I]} <= m.
Proof.
  intros.
  entailer.
  intros.
  destruct H as [k H].
  lia.
Qed.

Fact sqrt_correct: forall m: Z,
  {{ 0 <= {[X]} AND {[X]} = m }}
    I ::= 0;;
    While (I+1)*(I+1) <= X Do
      I ::= I+1
    EndWhile
  {{ {[I]} * {[I]} <= m AND m < ({[I]} + 1) * ({[I]} + 1) }}.
Proof.
  intros.
  apply hoare_asgn_seq.
  assert_simpl.
  eapply hoare_consequence;
  [ apply into_loop |
  | apply after_loop].
  apply hoare_while.
  eapply hoare_consequence_post;
  [ apply hoare_asgn_fwd
  | apply loop_body].
Qed.

(** [] *)

End Task1_2.

End Task1.

(* ################################################################# *)
(** * Task 2: Understanding Denotations *)

(** In this task, you will read descriptions about program states and decide
    whether the following pairs of programs states belong to corresponding
    programs' denotations. *)

(** **** Exercise: 1 star, standard  *)
Module Task2_1.

(** Suppose [X] and [Y] are different program variables. If [st X = 1] and
    [st Y = 2], then does (st, st) belong to the following program's denotation?

    Y ::= X + 1

    1: Yes. 2: No. *)

Definition my_choice: Z := 1.

End Task2_1.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_2.

(** Suppose [X] is a program variables. If [st1 X = 100], [st2 X = 1] and all
    other variables in [st1] and [st2] are zero, then does (st1, st2) belong to
    the following program's denotation?

    While 1 <= X Do X ::= X + 1 EndWhile

    1: Yes. 2: No. *)

Definition my_choice: Z := 2.

End Task2_2.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_3.

(** Suppose [X] and [Y] are different program variables. If [st1 X = 1],
    [st1 Y = 2], [st2 X = 2], [st2 Y = 1] and all other variables in [st1] and
    [st2] are zero, then does (st1, st2) belong to the following program's
    denotation?

    Z ::= X;; X ::= Y;; Y ::= Z

    1: Yes. 2: No. *)

Definition my_choice: Z := 2.

End Task2_3.
(** [] *)

(* ################################################################# *)
(** * Task 3: Reasoning About Recursions *)

(** Here is a recursive function about integer expressions. Try to understand
    what it tries to do and prove related properties. *)

Fixpoint aexp_reverse (a: aexp): aexp :=
  match a with
  | ANum n => ANum n
  | AId X => AId X
  | APlus a1 a2 => APlus (aexp_reverse a2) (aexp_reverse a1)
  | AMinus a1 a2  => AMinus (aexp_reverse a1) (aexp_reverse a2)
  | AMult a1 a2 => AMult (aexp_reverse a2) (aexp_reverse a1)
  end.

(** **** Exercise: 2 stars, standard (reverse_equiv)  *)
Lemma reverse_equiv: forall a st, aeval (aexp_reverse a) st = aeval a st.
Proof.
  intros.
  induction a;simpl.
  - reflexivity.
  - reflexivity.
  - unfold Func.add.
    rewrite IHa1, IHa2.
    lia.
  - unfold Func.sub.
    rewrite IHa1, IHa2.
    lia.
  - unfold Func.mul.
    rewrite IHa1, IHa2.
    lia.
Qed.

(** **** Exercise: 2 stars, standard (reversed_reverse)  *)
Lemma reversed_reverse: forall a1 a2,
  aexp_reverse a1 = a2 ->
  a1 = aexp_reverse a2.  
Proof.
  intros.
  rewrite <- H. clear H.
  induction a1; simpl; try reflexivity.
  - rewrite IHa1_1, IHa1_2 at 1.
    reflexivity.
  - rewrite IHa1_1, IHa1_2 at 1.
    reflexivity.
  - rewrite IHa1_1, IHa1_2 at 1.
    reflexivity.
Qed.


(** You may wonder whether [aexp_reverse] is a meaningful operation. Well, it
    might be. Try to answer the following questions about it. *)

(** **** Exercise: 1 star, standard  *)
Module Task3_3.

(** In comparison, which one of the following is the better optimazation?

    - do [fold_constants] directly;

    - do [fold_constants] after [aexp_reverse].

    Choose one correct statement:

    0. They always generate results with the same length.

    1. The first one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    2. The second one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    3. They are not comparable. *)

Definition my_choice: Z := 3.

End Task3_3.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task3_4.

(** In comparison, which one of the following is the better optimazation?

    - do [fold_constants] directly;

    - do [fold_constants], then [aexp_reverse], and [fold_constants] again
      in the end

    Choose one correct statement:

    0. They always generate results with the same length.

    1. The first one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    2. The second one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    3. They are not comparable. *)

Definition my_choice: Z := 2.

End Task3_4.
(** [] *)

(* ################################################################# *)
(** * Task 4: Understanding Higher-Order Functions *)

(** Suppose [f] and [g] are both functions from [A] to [A]. How shall we define
    the function that applies [f] first and then applies [g]? *)

(** **** Exercise: 2 stars, standard (compose)  *)

Definition compose {A: Type} (f g: A -> A): A -> A :=
  fun x => g (f x).

(** It is obvious that [ compose f (compose g h) ] is equivalent with
    [ compose (compose f g) h ]. Your task is to prove it in Coq. *)

Theorem compose_assoc: forall f g h: Z -> Z,
  Func.equiv (compose f (compose g h)) (compose (compose f g) h).
Proof.
  intros.
  unfold Func.equiv.
  intros.
  unfold compose.
  reflexivity.
Qed.

(** [] *)


(* Thu Mar 26 09:44:52 CST 2020 *)
