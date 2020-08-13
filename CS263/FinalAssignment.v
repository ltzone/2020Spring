(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/06/18.                                             *)
(* Due: 2020/06/29, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (FinalAssignment.v) on CANVAS.     *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "FinalAssignment.vo" file is generated.     *)
(*                                                                   *)
(* 5. Do not copy and paste others' answer.                          *)
(*                                                                   *)
(* 6. Using any theorems and/or tactics provided by Coq's standard   *)
(*    library is allowed in this assignment, if not specified.       *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.ImpExt4 PL.Imp3 PL.Lambda2 PL.ImpExt5 PL.ImpExt6.
Import ListNotations.

(* ################################################################# *)
(** * Task 1: General Questions *)

Module Task1.

(** **** Exercise: 1 star, standard  *)

(** Suppose you write a program in a software company and the company uses
    compiler [G]. If your program should have behavior [A] according the
    language's standard documentation [D] but does have behavior [B] when you
    compiler it and run it, which statements below about compiler [G] and
    language standard [D] are correct?

    1. The standard [D] is wrong and should be fixed.

    2. The compiler [G] has a bug.

    3. If the program is designed to have behavior [A], you should modify the
       program.

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice1: list Z := [2;3].
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Suppose a verification tool [V] is developed in Coq to verify programs, and
    these programs will be compiled by compiler [G]. If a program is proved in
    Coq to have behavior [A] via [V] but turns our to have behavior [B] when
    developers compile it and run it, which statement below is correct?

    1. The verification tool [V] does not correctly formalize programs'
       behavior.

    2. The compiler [G] has a bug. *)

Definition my_choice2: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Here is a Hoare triple:

    [ {{ False }} While (X == X) Do Skip EndWhile {{ False }}. ]

    Which assertions below can be used as the loop invariant to prove this Hoare
    triple?

    1. [True]

    2. [False]

    3. [ {[X]} = 0 ].

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice3: list Z := [1;2;3].
(** [] *)

End Task1.

(** We learnt three different program semantics in this course. Thus we can
    express _program equivalence_ with three different approaches. In the
    following tasks, you need to prove the following two programs equivalent
    w.r.t. three different definitions:

    - [ If b1
        Then (If b2 Then c1 Else c2 EndIf)
        Else (If b2 Then c3 Else c4 EndIf)
        EndIf; ]

    - [ If b2
        Then (If b1 Then c1 Else c3 EndIf)
        Else (If b1 Then c2 Else c4 EndIf)
        EndIf. ] *)

(* ################################################################# *)
(** * Task 2: Program Equivalence w.r.t. Hoare logic *)

Module Task2.

Section Task2.

Import Assertion_D.

Variable T: FirstOrderLogic.
Hypothesis T_sound: FOL_sound T.
Hypothesis T_complete: FOL_complete T.

(** To prove these two programs equivalent via Hoare logic, you may need the
    following auxiliary lemmas. We provide it for you. *)

Lemma der_aux:
  forall P Q R: Assertion,
  P AND Q AND R |-- P AND R AND Q.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  unfold FOL_valid.
  intros.
  simpl.
  tauto.
Qed.

(** This next theorem that your are going to prove is a meta theorem of Hoare
    logic. It says, if one triple for the former program is provable, then the
    corresponding one for the latter program is also provable, and vise versa.
*)

(** **** Exercise: 2 stars, standard (PE_Hoare)  *)
Lemma hoare_if_inv: forall P b c1 c2 Q,
  |-- {{P}} If b Then c1 Else c2 EndIf {{Q}} ->
  (|-- {{ P  AND {[b]} }} c1 {{Q}}) /\
  (|-- {{ P  AND NOT {[b]} }} c2 {{Q}}).
Proof.
  intros.
  remember ({{P}} If b Then c1 Else c2 EndIf {{Q}}) as Tr.
  revert P b c1 c2 Q HeqTr; induction H; intros.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ? ? ?; subst.
    clear IHprovable1 IHprovable2.
    tauto.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ?; subst.
    assert ({{P'}} If b Then c1 Else c2 EndIf {{Q'}} = 
            {{P'}} If b Then c1 Else c2 EndIf {{Q'}}).
    { reflexivity. }
    pose proof IHprovable _ _ _ _ _ H2; clear IHprovable H2.
    destruct H3.
    split.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H2.
      * apply H1.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H3.
      * apply H1.
Qed.


Theorem PE_Hoare:
  forall P b1 b2 c1 c2 c3 c4 Q,
  |-- {{ P }} 
        If b1
        Then (If b2 Then c1 Else c2 EndIf)
        Else (If b2 Then c3 Else c4 EndIf)
        EndIf
      {{ Q }}
  <->  
  |-- {{ P }} 
        If b2
        Then (If b1 Then c1 Else c3 EndIf)
        Else (If b1 Then c2 Else c4 EndIf)
        EndIf
      {{ Q }}.
Proof.
  intros. split;intro.
  + apply hoare_if_inv in H.
    destruct H.
    apply hoare_if_inv in H. destruct H.
    apply hoare_if_inv in H0. destruct H0.
    econstructor.
    - econstructor.
      * eapply hoare_consequence.
        { apply der_aux. } { apply H. } { apply derives_refl. }
      * eapply hoare_consequence.
        { apply der_aux. } { apply H0. } { apply derives_refl. }
    - econstructor.
      * eapply hoare_consequence.
        { apply der_aux. } { apply H1. } { apply derives_refl. }
      * eapply hoare_consequence.
        { apply der_aux. } { apply H2. } { apply derives_refl. }
  + apply hoare_if_inv in H.
    destruct H.
    apply hoare_if_inv in H. destruct H.
    apply hoare_if_inv in H0. destruct H0.
    econstructor.
    - econstructor.
      * eapply hoare_consequence.
        { apply der_aux. } { apply H. } { apply derives_refl. }
      * eapply hoare_consequence.
        { apply der_aux. } { apply H0. } { apply derives_refl. }
    - econstructor.
      * eapply hoare_consequence.
        { apply der_aux. } { apply H1. } { apply derives_refl. }
      * eapply hoare_consequence.
        { apply der_aux. } { apply H2. } { apply derives_refl. }
Qed.

End Task2.
End Task2.

(* ################################################################# *)
(** * Task 3: Program Equivalence w.r.t. Denotational Semantics *)

Import Relation_Operators.

(** To prove these two programs equivalent via denotational semantics, you may
    need the following lemmas about [Relation_Operators.union] and
    [Relation_Operators.concat]. *)

(** **** Exercise: 1 star, standard (concat_assoc)  *)

Lemma union_assoc: forall R1 R2 R3: state -> state -> Prop,
  Rel.equiv
    (union (union R1 R2) R3)
    (union R1 (union R2 R3)).
Proof.
  intros. hnf. intros.
  split;intro.
  - hnf. hnf in H. destruct H as [[H | H]| H].
    + left;tauto.
    + right;left;tauto.
    + right;right;tauto.
  - hnf. hnf in H. destruct H as [H |[H | H]].
    + left;left;tauto.
    + left;right;tauto.
    + right;tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (concat_union_distr_l)  *)

Lemma concat_union_distr_l: forall R1 R2 R3: state -> state -> Prop,
  Rel.equiv
    (concat R1 (union R2 R3))
    (union (concat R1 R2) (concat R1 R3)).
Proof.
  intros. hnf. intros.
  split;intro.
  - hnf. hnf in H. destruct H as [c [H1 [H2|H2]]].
    + left. exists c. auto.
    + right. exists c. auto.
  - hnf. hnf in H. destruct H as [[c [H1 H2]]|[c [H1 H2]]].
    + exists c. split;auto. left;auto.
    + exists c. split;auto. right;auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (test_sem_swap)  *)

Lemma test_sem_swap: forall (S1 S2: state -> Prop) (R: state -> state -> Prop),
  Rel.equiv
    (concat (test_rel S1) (concat (test_rel S2) R))
    (concat (test_rel S2) (concat (test_rel S1) R)).
Proof.
  intros. hnf. intros;split;intro;hnf in *;
  destruct H as [c1 [[H1' H1] [c2 [[H2' H2] H3]]]]; subst c1 c2.
  - exists a. split;hnf;auto.
    exists a. split;hnf;auto.
  - exists a. split;hnf;auto.
    exists a. split;hnf;auto.
Qed.
(** [] *)

(** Now, you are ready to prove this final theorem. You may find [ceval_CIf]
    and [union_comm] useful. *)

(** **** Exercise: 2 stars, standard (PE_Denote)  *)

Theorem PE_Denote: forall b1 b2 c1 c2 c3 c4,
  com_equiv
   (If b1
    Then (If b2 Then c1 Else c2 EndIf)
    Else (If b2 Then c3 Else c4 EndIf)
    EndIf)
   (If b2
    Then (If b1 Then c1 Else c3 EndIf)
    Else (If b1 Then c2 Else c4 EndIf)
    EndIf).
Proof.
  intros.
  unfold com_equiv.
  unfold ceval. fold ceval.
  unfold if_sem.
  rewrite !concat_union_distr_l.
  rewrite union_assoc.
  rewrite <- (union_assoc  (concat (test_rel (beval b1))
           (concat (test_rel (beval (! b2))) (ceval c2)))).
  rewrite (union_comm _ _ (concat (test_rel (beval b1))
              (concat (test_rel (beval (! b2))) (ceval c2)))).
  rewrite (union_assoc (concat (test_rel (beval (! b1)))
              (concat (test_rel (beval b2)) (ceval c3)))).
  rewrite <- (union_assoc (concat (test_rel (beval b1))
        (concat (test_rel (beval b2)) (ceval c1)))).
  rewrite !(test_sem_swap (beval b1)).
  rewrite !(test_sem_swap (beval (!b1))).
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 4: Program Equivalence w.r.t. Small Step Semantics *)

Local Open Scope imp_scope.

(** The following theorem states a program equivalence via small step semantics.
    In order to prove it, you may find a shortcut: the connection between
    denotational semantics and small step semantics. In other words, you may use
    [PE_Denote] and [semantic_equiv]. *)

(** **** Exercise: 1 star, standard (PE_SmallStep)  *)

Theorem PE_SmallStep: forall b1 b2 c1 c2 c3 c4 st st',
  multi_cstep 
   (If b1
    Then (If b2 Then c1 Else c2 EndIf)
    Else (If b2 Then c3 Else c4 EndIf)
    EndIf, st)
   (Skip, st') <->
  multi_cstep
   (If b2
    Then (If b1 Then c1 Else c3 EndIf)
    Else (If b1 Then c2 Else c4 EndIf)
    EndIf, st)
   (Skip, st').
Proof.
  intros. split;intro.
  - apply semantic_equiv. apply PE_Denote.
    apply semantic_equiv. auto.
  - apply semantic_equiv. apply PE_Denote.
    apply semantic_equiv. auto.
Qed.
(** [] *)

(** Some of you may feel that [PE_SmallStep] only expresses a coarse grained
    equivalence. But can we state a more fine grained version using our small
    step semantics? Please answer the following questions. *)

(** **** Exercise: 1 star, standard  *)

Definition finer_grained_statement: Prop :=
  forall b1 b2 c1 c2 c3 c4 st c' st',
  multi_cstep 
   (If b1
    Then (If b2 Then c1 Else c2 EndIf)
    Else (If b2 Then c3 Else c4 EndIf)
    EndIf, st)
   (c', st') <->                      (* <---- this is different *)
  multi_cstep
   (If b2
    Then (If b1 Then c1 Else c3 EndIf)
    Else (If b1 Then c2 Else c4 EndIf)
    EndIf, st)
   (c', st').                         (* <---- this is different *)

(** Is the statement above correct? 1. Yes. 2. No. *)

Definition my_choice1: Z :=2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

Definition statement_instance: Prop :=
  forall b1 b2 c1 c2 c3 c4 st,
  multi_cstep 
   (If b1
    Then (If b2 Then c1 Else c2 EndIf)
    Else (If b2 Then c3 Else c4 EndIf)
    EndIf, st)
   (c1, st) <->                      (* <---- this is different *)
  multi_cstep
   (If b2
    Then (If b1 Then c1 Else c3 EndIf)
    Else (If b1 Then c2 Else c4 EndIf)
    EndIf, st)
   (c1, st).                         (* <---- this is different *)

(** Is the statement above correct? 1. Yes. 2. No. *)

Definition my_choice2: Z := 1.
(** [] *)

(** Can you briefly explain why? Please write down your reasons in English or
    in Chinese here in comments. *)

(* ***************************************************************** *)
(* The first statement is wrong                                      *)
(* because the evaluation orders of cexp are different, for example, *)
(* set b1 and b2 to be both true, then the first cexp can step to    *)
(*   (If True(b2) Then c1 Else c2, st),                              *)
(* but by no means can the second expression take such steps since   *)
(* c1 and c2 are in two distinct branches.                           *)
(* The second statement is true                                      *)
(* because stepping to the (c1,st) state means (beval b1 st) and     *)
(* (beval b2 st) hold in both programs. Since if_sem steps preserve  *)
(* the denotation and have no side effects, both programs can step   *)
(* to (c1,st).                                                       *)
(* ***************************************************************** *)