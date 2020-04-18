(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/04/17.                                             *)
(* Due: 2019/04/21, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment5.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment5.vo" file is generated.         *)
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

Require Import PL.Imp3 PL.ImpExt4 PL.ImpExt5.

(* ################################################################# *)
(** * Task 1: Understanding Steps *)

(** Prove the following step relations. *)

(** **** Exercise: 1 star, standard: (step_sample1)  *)

Module Task1.
Import Abstract_Pretty_Printing.

Example step_sample1: forall (X: var) (st: state),
  st X = 5 ->
  astep st ((1 + X) * 2) ((1 + 5) * 2).
Proof.
  intros.
  apply AS_Mult1.
  apply AS_Plus2;[apply AH_num|].
  rewrite <- H.
  apply AS_Id.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard: (step_sample1)  *)

Example step_sample2: forall (X: var) (st: state),
  cstep (If (0 <= (1 + 5) * 2) Then X ::= X - 1 Else Skip EndIf, st)%imp
        (If (0 <= 6 * 2) Then X ::= X - 1 Else Skip EndIf, st)%imp.
Proof.
  intros.
  apply CS_IfStep.
  apply BS_Le2;[apply AH_num|].
  apply AS_Mult1.
  apply AS_Plus.
Qed.

End Task1.

(* ################################################################# *)
(** * Task 2: Alternative Small Step Semantics *)

Module Task2.
Import Abstract_Pretty_Printing.
Local Open Scope imp.

(** Alice wrote an alternative definition of [cstep] as follows. Her purpose
    is to avoid administrative steps, i.e. the step from [Skip;; c] to [c]. *)

Inductive cstep' : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep' : forall st X a a',
      astep st a a' ->
      cstep' (CAss X a, st) (CAss X a', st)
  | CS_Ass' : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep' (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep' : forall st c1 c1' st' c2,
      cstep' (c1, st) (c1', st') ->
      cstep' (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq' : forall st c2 st' c2',
      cstep' (c2, st) (c2', st') ->
      cstep' (Skip ;; c2, st) (c2', st')   (* <- This is different. *)
  | CS_IfStep' : forall st b b' c1 c2,
      bstep st b b' ->
      cstep'
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue' : forall st c1 c2,
      cstep' (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse' : forall st c1 c2,
      cstep' (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While' : forall st b c,
      cstep'
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

(** But she is not sure, on what extent this [cstep'] is a well-defined
    semantics. Your task is to give her an answer using the following
    examples. *)

(** **** Exercise: 1 star, standard  *)

Definition claim1: Prop := forall (st: state) (X Y: var),
  st X = 1 ->
  cstep' (Skip;; Y ::= X, st) (Y ::= 1, st).

Fact claim1_veri : claim1.
Proof. hnf.
  intros.
  apply CS_Seq'.
  apply CS_AssStep'.
  rewrite <- H.
  apply AS_Id.
Qed.

(** Does [cstep'] satisfy this claim? 1: Yes. 2: No. *)

Definition my_choice1: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

Definition claim2: Prop := forall (st: state) (X: var),
  st X = 0 ->
  cstep' ((Skip;; Skip);; X ::= 0, st) (Skip, st).

(** Does [cstep'] satisfy this claim? 1: Yes. 2: No. *)

Definition my_choice2: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

Definition claim3: Prop := forall (st: state) (X: var),
  st X = 0 ->
  cstep' (Skip;; Skip;; X ::= 0, st) (Skip, st).

Fact claim3_veri : claim3.
Proof.
  hnf. intros.
  apply CS_Seq'.
  apply CS_Seq'.
  apply CS_Ass';[apply H|].
  intros. reflexivity.
Qed.
(** Does [cstep'] satisfy this claim? 1: Yes. 2: No. *)

Definition my_choice3: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

Definition claim4: Prop := forall (st: state),
  cstep' (Skip;; Skip;; Skip, st) (Skip, st).


(** Does [cstep'] satisfy this claim? 1: Yes. 2: No. *)

Definition my_choice4: Z := 2.
(** [] *)

End Task2.

(* ################################################################# *)
(** * Task 3: Middle Step Relation *)

Module Task3.
Import Abstract_Pretty_Printing.
Local Open Scope imp.

(** Between denotational semantics (also called big step semantics) and small
   step semantics, there could be other choices. The famous certified compiler
   CompCert formalizes the program semantics of C using "middle step semantics".
   Here is a similar version for [IMP]. *)

Inductive mstep : (com * state) -> (com * state) -> Prop :=
  | MS_Ass : forall st1 st2 X E,
      st2 X = aeval E st1 ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      mstep (CAss X E, st1) (Skip, st2)
  | MS_SeqStep : forall st c1 c1' st' c2,
      mstep (c1, st) (c1', st') ->
      mstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | MS_Seq : forall st c2,
      mstep (Skip ;; c2, st) (c2, st)
  | MS_IfTrue : forall st b c1 c2,
      beval b st ->
      mstep (If b Then c1 Else c2 EndIf, st) (c1, st)
  | MS_IfFalse : forall st b c1 c2,
      ~ beval b st ->
      mstep (If b Then c1 Else c2 EndIf, st) (c2, st)
  | MS_WhileTrue : forall st b c,
      beval b st ->
      mstep
        (While b Do c EndWhile, st)
        (c;; While b Do c EndWhile, st)
  | MS_WhileFalse : forall st b c,
      ~ beval b st ->
      mstep (While b Do c EndWhile, st) (Skip, st).

Definition multi_mstep := clos_refl_trans mstep.

(** Your task is to prove half of the semantic equivalence between this
    middle step semantics and small step semantics. Specifically, your
    eventual goal is:

    Theorem Multi_MidStep_To_SmallStep: forall c st1 st2,
      multi_mstep (c, st1) (Skip, st2) ->
      multi_cstep (c, st1) (Skip, st2).

To prove this theorem, the main idea is to discover the relation between middle
steps [mstep] and small steps [cstep]. It is critical to see the following
observation: every middle step can be represented by finite small steps. In your
proof, you can freely use the following theorems, which we have demostrated in
class. *)

Check semantic_equiv_aexp1.

(* semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n). *)

Check semantic_equiv_bexp1.

(* semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse). *)

Check multi_congr_CAss.

(* multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  multi_cstep (CAss X a, st) (CAss X a', st). *)

Check multi_congr_CSeq.

(* multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (CSeq c1 c2, st1) (CSeq c1' c2, st1'). *)

Check multi_congr_CIf.

(* multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep (CIf b c1 c2, st) (CIf b' c1 c2, st). *)

(** **** Exercise: 4 stars, standard (One_MidStep_To_SmallStep)  *)

(** Hint: In the following lemma, [a] and [b] are pairs of program commands and
    program states. You may use tactics like [ destruct a as [c1 st1] ] so that
    a real pair is demonstrated in the proof goal. But, you are the one to
    choose between destructing them and not destructing them, depending on
    which way is more convenient for building a Coq proof. *)

Lemma One_MidStep_To_SmallStep: forall a b,
  mstep a b -> multi_cstep a b.
Proof.
  intros.
  induction H.
  - symmetry in H. apply semantic_equiv_aexp1 in H.
    apply multi_congr_CAss with (X:=X)  in H.
    transitivity_n1 (X ::= st2 X, st1);auto.
    apply CS_Ass;auto.
  - apply multi_congr_CSeq. auto.
  - transitivity_n1 (Skip;; c2, st);[reflexivity|].
    apply CS_Seq.
  - apply (proj1 (semantic_equiv_bexp1 _ _)) in H.
    transitivity_n1 (If BTrue Then c1 Else c2 EndIf, st).
    + apply multi_congr_CIf. auto.
    + apply CS_IfTrue.
  - apply (proj2 (semantic_equiv_bexp1 _ _)) in H.
    transitivity_n1 (If BFalse Then c1 Else c2 EndIf, st).
    + apply multi_congr_CIf. auto.
    + apply CS_IfFalse.
  - apply (proj1 (semantic_equiv_bexp1 _ _)) in H.
    transitivity_1n (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).
    + apply CS_While.
    + transitivity_n1 (If BTrue Then c;; While b Do c EndWhile Else Skip EndIf, st).
      * apply multi_congr_CIf. auto.
      * apply CS_IfTrue.
  - apply (proj2 (semantic_equiv_bexp1 _ _)) in H.
    transitivity_1n (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).
    + apply CS_While.
    + transitivity_n1 (If BFalse Then c;; While b Do c EndWhile Else Skip EndIf, st).
      * apply multi_congr_CIf. auto.
      * apply CS_IfFalse.
Qed.

(** Now, from this conclusion above to our final target, we only need two
    properties about reflexive transitive closures. *)

(** **** Exercise: 2 stars, standard (rt_idempotent)  *)
Theorem rt_idempotent : forall (X: Type) (R: X -> X -> Prop) (x y: X),
  clos_refl_trans (clos_refl_trans R) x y <-> clos_refl_trans R x y.
Proof.
  intros. split;intro.
  - induction H.
    + auto.
    + reflexivity.
    + transitivity y;auto.
  - apply rt_step. auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (rt_mono)  *)
Theorem rt_mono : forall (X: Type) (R1 R2: X -> X -> Prop),
  (forall x y, R1 x y -> R2 x y) ->
  (forall x y, clos_refl_trans R1 x y -> clos_refl_trans R2 x y).
Proof.
  intros.
  induction_n1 H0.
  - reflexivity.
  - transitivity_n1 y;auto.
Qed.
(** [] *)

(** Here is our final target! *)

(** **** Exercise: 2 stars, standard (Multi_MidStep_To_SmallStep)  *)

Theorem Multi_MidStep_To_SmallStep: forall c st1 st2,
  multi_mstep (c, st1) (Skip, st2) ->
  multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  induction H.
  + apply One_MidStep_To_SmallStep in H. auto.
  + reflexivity.
  + apply (rt_mono _ _ _ One_MidStep_To_SmallStep) in H.
    apply (rt_mono _ _ _ One_MidStep_To_SmallStep) in H0.
    apply rt_idempotent.
    transitivity y;auto.
Qed.
(** [] *)

End Task3.

(* Fri Apr 17 00:44:35 CST 2020 *)
