(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/04/30.                                             *)
(* Due: 2019/05/08, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment7.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment7.vo" file is generated.         *)
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

Require Import PL.Imp3 PL.ImpExt4 PL.ImpExt5 PL.ImpExt6.
Require Import Coq.Lists.List.

(* ################################################################# *)
(** * Task 1: Reasoning About Inductive Predicates *)

Module Task1.
Import Abstract_Pretty_Printing.
Local Open Scope imp.

(** We have seen this middle step definition in our previous assignments. *)

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

(** We have already proved the following theorem:

    Theorem Multi_MidStep_To_SmallStep: forall c st1 st2,
      multi_mstep (c, st1) (Skip, st2) ->
      multi_cstep (c, st1) (Skip, st2).

This time, you are going to prove the reverse direction. Our proof will be based
on a proof technology called simulation. The main idea is define a simulation
relation between a small-step state and a middle-step state.

    (c1, st) -------> (c1a, st) -------> (c1b, st) -------> (c1', st')
            small step         small step         small step
       |                  |                  |                  |
       |                  |                  |                  |
       |                  |                  |                  |
       |                  |                  |                  |

    (c2, st) -------> (c2 , st) -------> (c2 , st) -------> (c2', st')
             no step            no step          middle step
       |                                                        |
       |                                                        |
       |                                                        |
       |                                                        |

    (c2, st) ---------------------------------------------> (c2', st')
                             middle step

In this diagram above, [(c1, st)] is a state in small step semantics and 
[(c2, st)] is the corresponding middle step state. We want to define such a
corresponding relation is a simulation. In other words, when a small step is
taken (1) either the result still corresponds to the original middle step state
(2) or this small step corresponds to a middle step. The following ternary
relation is such a simulation relation. *)

Inductive sim: com -> com -> state -> Prop :=
| Sim_Ass: forall X a1 a2 st,
    aeval a1 st = aeval a2 st ->
    sim (CAss X a1) (CAss X a2) st
| Sim_Seq: forall c1 c2 c3 st,
    sim c1 c2 st ->
    sim (c1 ;; c3) (c2 ;; c3) st
| Sim_Skip: forall st,
    sim CSkip CSkip st
| Sim_If: forall b1 b2 c1 c2 st,
    (beval b1 st <-> beval b2 st) ->
    sim (CIf b1 c1 c2) (CIf b2 c1 c2) st
| Sim_While: forall b c st,
    sim (CWhile b c) (CWhile b c) st
| Sim_While_Mid: forall b1 b2 c st,
    (beval b1 st <-> beval b2 st) ->
    sim (CIf b1 (c;; CWhile b2 c) Skip) (CWhile b2 c) st.

(** This is the simulation statement:

Lemma sim_forward_simulation: forall c1 c2 st c1' st',
  sim c1 c2 st ->
  cstep (c1, st) (c1', st') ->
  exists c2',
  sim c1' c2' st' /\ multi_mstep (c2, st) (c2', st').

But in order to verify this simulation relation, you may need the following two
auxiliary properties. *)

(** **** Exercise: 1 star, standard (sim_refl)  *)
Lemma sim_refl: forall c st,
  sim c c st.
Proof.
  intros.
  induction c.
  - apply Sim_Skip.
  - apply Sim_Ass. reflexivity.
  - apply Sim_Seq. apply IHc1. 
  - apply Sim_If. tauto.
  - apply Sim_While.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (multi_mstep_congr_CSeq)  *)
Theorem multi_mstep_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_mstep (c1, st1) (c1', st1') ->
  multi_mstep (CSeq c1 c2, st1) (CSeq c1' c2, st1').
Proof.
  intros.
  induction_n1 H.
  - apply rt_refl.
  - transitivity_n1 (c;; c2, s);auto.
    apply MS_SeqStep. apply H.
Qed.
(** [] *)

(** Now, we are ready to verify our simulation relation. Hint: you may prove it
    by induction over the proof tree of [sim c1 c2 st] or the proof tree of
    [cstep (c1, st) (c1', st')]. For the former choice, remember that you can
    choose to have a stronger induction hypothesis by using some [revert] before
    [induction]. For the latter choice, remember that Coq's [induction] cannot
    directly handle pairs in [cstep]'s arguments. Tactics like:
    [
      remember (c1, st) as cst eqn:EQ.
      remember (c1', st') as cst' eqn:EQ'.
      revert c1 st EQ c1' st' EQ' H.
    ]
    may be useful before your induction. By the way, you may also think about
    not choosing induction proofs. It seems a reasonable solution to do case
    analysis only (instead of induction) over how [sim c1 c2 st] and/or
    [cstep (c1, st) (c1', st')] is established. You can try Coq's [inversion]
    tactic and find out whether it works.
*)

(** **** Exercise: 4 stars, standard (sim_forward_simulation)  *)

Lemma sim_forward_simulation: forall c1 c2 st c1' st',
  sim c1 c2 st ->
  cstep (c1, st) (c1', st') ->
  exists c2',
  sim c1' c2' st' /\ multi_mstep (c2, st) (c2', st').
Proof.
  intros. revert st' c1' H0.
  induction H;intros.
  - inversion H0;subst.
    + exists (X ::= a2).
      split.
      { apply Sim_Ass.
        apply aeval_preserve in H2.
        rewrite <-H, <-H2.
        reflexivity. }
      { reflexivity. }
    + exists Skip. split.
      { apply Sim_Skip. }
      { apply rt_step. apply MS_Ass.
        - rewrite <- H. reflexivity.
        - apply H7. }
  - inversion H0;subst.
    + specialize (IHsim _ _ H2).
      destruct IHsim as [c2' [H1 H3]].
      exists (c2';;c3). split.
      { apply Sim_Seq. apply H1. }
      { apply multi_mstep_congr_CSeq. apply H3. }
    + inversion H;subst. exists c1'. split.
      { apply sim_refl. }
      { apply rt_step. apply MS_Seq. }
  - inversion H0.
  - inversion H0;subst.
    + exists (If b2 Then c1 Else c2 EndIf).
      split.
      { apply Sim_If. apply beval_preserve in H2. tauto. }
      { reflexivity. }
    + exists c1'.
      split.
      { apply sim_refl. }
      { apply rt_step. apply MS_IfTrue. apply H. apply I. }
    + exists c1'.
      split.
      { apply sim_refl. }
      { apply rt_step. apply MS_IfFalse. intros C. 
        apply H in C. destruct C. }
  - inversion H0;subst.
    exists (While b Do c EndWhile).
    split.
    { apply Sim_While_Mid. tauto. }
    { reflexivity. }
  - inversion H0;subst.
    + exists (While b2 Do c EndWhile).
      split.
      { apply Sim_While_Mid. apply beval_preserve in H2. tauto. }
      { reflexivity. }
    + exists (c;; While b2 Do c EndWhile).
      split.
      { apply sim_refl. }
      { apply rt_step. apply MS_WhileTrue. apply H. apply I. }
    + exists Skip.
      split.
      { apply sim_refl. }
      { apply rt_step. apply MS_WhileFalse. intros C. 
        apply H in C. destruct C. }
Qed.

(** [] *)

(** Now that we have verified the simulation relation [sim], it is already not
    far away from our final target. The next theorem says: if one step relation
    [RX] (like our small step relation [cstep]) are simulated by another step
    relation [RY] (like our middle step relation), then the reflexive transitive
    closure of [RX] is also simulated by the reflexive transitive closure of
    [RY]. This theorem allows us to use a simulation relation to connect the
    reflexive transitive closure of two step relations. *)

(** **** Exercise: 3 stars, standard (rt_forward_simulation)  *)
Theorem rt_forward_simulation :
  forall (X Y: Type) (RX: X -> X -> Prop) (RY: Y -> Y -> Prop) (S: X -> Y -> Prop),
    (forall x1 x2 y1,
       S x1 y1 -> RX x1 x2 ->
       exists y2, S x2 y2 /\ clos_refl_trans RY y1 y2) ->
    (forall x1 x2 y1,
       S x1 y1 -> clos_refl_trans RX x1 x2 ->
       exists y2, S x2 y2 /\ clos_refl_trans RY y1 y2).
Proof.
  intros.
  induction_n1 H1.
  - exists y1. split.
    { apply H0. }
    { reflexivity. }
  - destruct IHrt as [y2 [H3 H4]].
    specialize (H _ _ _ H3 H1).
    destruct H as [y3 [H5 H6]].
    exists y3.
    split;[apply H5|].
    transitivity y2;assumption.
Qed.
(** [] *)

(** OK. Its time to put pieces together now. Let's first restate our simulation
    theorem to fit [rt_forward_simulation]'s assumption. We do that for you. *)

Inductive sim': com * state-> com * state -> Prop :=
| sim'_intro: forall c1 c2 st, sim c1 c2 st -> sim' (c1, st) (c2, st).

Corollary sim'_forward_simulation: forall cst1 cst1' cst2,
  sim' cst1 cst2 ->
  cstep cst1 cst1' ->
  exists cst2',
  sim' cst1' cst2' /\ multi_mstep cst2 cst2'.
Proof.
  intros.
  inversion H; subst.
  destruct cst1' as [c1' st'].
  pose proof sim_forward_simulation c1 c2 st c1' st' H1 H0.
  destruct H2 as [c2' [? ?]].
  exists (c2', st').
  split; [apply sim'_intro; tauto | tauto].
Qed.

(** The final step is left for you. *)

(** EX1 (Multi_SmallStep_To_MidStep) *)
Theorem Multi_SmallStep_To_MidStep: forall c st1 st2,
  multi_cstep (c, st1) (Skip, st2) ->
  multi_mstep (c, st1) (Skip, st2).
Proof.
  pose proof rt_forward_simulation _ _ cstep mstep sim' sim'_forward_simulation.
  intros.
  pose proof (sim_refl c st1).
  apply sim'_intro in H1.
  specialize (H _ _ _ H1 H0).
  destruct H as [y2 [H2 H3]].
  inversion H2;subst.
  inversion H6;subst.
  apply H3.
Qed.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Reasoning About Lists *)

Module Task2.
Import Abstract_Pretty_Printing.
Import Assertion_D.  
Local Open Scope imp.

(** In class, we have proved that [ {{ P }} c1 ;; (c2 ;; c3) {{ Q }} ] is
    provable if and only if [ {{ P }} (c1 ;; c2) ;; c3 {{ Q }} ] is provable.
    Obviously, we can reassociate sequential compositions arbitrarily. For
    example,
    [    {{ P }} c1 ;; ((c2 ;; c3);; (c4;; c5)) {{ Q }}   ]
    if and only 
    [    {{ P }} ((c1 ;; c2) ;; c3);; (c4;; c5) {{ Q }}.   ]
    How can we describe such arbitrary reassociation? One potential approach is
    as follows. *)

Fixpoint unfold_CSeq (c: com): list com :=
  match c with
  | CSeq c1 c2 => (unfold_CSeq c1) ++ (unfold_CSeq c2)
  | _ => c :: nil
  end.

(** Mainly, [unfold_CSeq] flattens the tree structure of sequential composition.
    For example: *)

Example unfold_CSeq_ex1:
  unfold_CSeq (Skip ;; ((Skip ;; Skip);; (Skip;; Skip))) =
  Skip :: Skip :: Skip :: Skip :: Skip :: nil.
Proof. intros. reflexivity. Qed.

Example unfold_CSeq_ex2:
  unfold_CSeq (((Skip ;; Skip);; Skip);; (Skip;; Skip)) =
  Skip :: Skip :: Skip :: Skip :: Skip :: nil.
Proof. intros. reflexivity. Qed.

(** Using [unfold_CSeq], the following proposition says: arbitrarily reassociating
    sequential composition does not change Hoare triple's provability. *)

Definition seq_assoc_der_n_statement {T: FirstOrderLogic}: Prop :=
  forall P c1 c2 Q,
  unfold_CSeq c1 = unfold_CSeq c2 ->
  |-- {{ P }} c1 {{ Q }} ->
  |-- {{ P }} c2 {{ Q }}.

(** In order to prove this proposition, we need an auxiliary definition and an
    auxiliary lemma. *)

Definition fold_CSeq (cs: list com) c0: com := fold_right CSeq c0 cs.

(** Here, [fold_CSeq] is like a reverse function of [unfold_CSeq] but sequential
    compositions are all arranged in a right associative style. For example: *)

Example fold_CSeq_ex: forall c,
  fold_CSeq (Skip :: Skip :: Skip :: Skip :: Skip :: nil) c =
  (Skip;; (Skip;; (Skip;; (Skip;; (Skip;; c))))).
Proof. intros. reflexivity. Qed.

Section Task2.

Context {T: FirstOrderLogic}
        {T_sound: FOL_sound T}
        {T_complete: FOL_complete T}.

(** Your task now is to prove the following auxiliary lemma,
    [unfold_CSeq_fold_CSeq]. This lemma says, it is fine to apply [unfold_CSeq]
    and [fold_CSeq] in a Hoare triple. In its proof, you may need to use
    [Hoare_triple_congr_CSeq]. We provided it in our [Imp] library. *)


(* forall c1 c1' c2 c2',
  (forall P Q, |-- {{ P }} c1 {{ Q }} <-> |-- {{ P }} c1' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c2 {{ Q }} <-> |-- {{ P }} c2' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c1;; c2 {{ Q }} <-> |-- {{ P }} c1';; c2' {{ Q }}). *)

(** **** Exercise: 3 stars, standard (unfold_CSeq_fold_CSeq)  *)

Lemma prop_iff {P Q R}: P <-> Q -> Q <-> R -> P <-> R.
Proof. tauto. Qed.

Lemma prop_iff2 {P Q R}: Q <-> R -> P <-> Q -> P <-> R.
Proof. tauto. Qed.

Lemma fold_right_app : forall {A B: Type}
(f: A -> B -> B) (l1 l2: list A) (x: B),
 fold_right f x (l1 ++ l2) =
       fold_right f (fold_right f x l2) l1.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Lemma unfold_CSeq_fold_CSeq: forall P Q c c0,
  |-- {{ P }} fold_CSeq (unfold_CSeq c) c0 {{ Q }} <->
  |-- {{ P }} c ;; c0 {{ Q }}.
Proof.
  intros P Q c. revert P Q.
  induction c;simpl;try tauto.
  unfold fold_CSeq.
  intros.
  rewrite fold_right_app.
  pose proof (IHc1 P Q (fold_right CSeq c0 (unfold_CSeq c2))).
  apply (prop_iff H); clear H.
  pose proof (seq_assoc_der P c1 c2 c0 Q).
  apply (prop_iff2 H);clear H.
  apply Hoare_triple_congr_CSeq.
  { intros. tauto. }
  intros.
  apply IHc2.
Qed.

(** Is it enough to prove [seq_assoc_der_n_statement]? Yes, as long as we know
    [c ;; Skip] is somehow the same as [c] for any program c. *)

(* forall c P Q,
  |-- {{ P }} c;; Skip {{ Q }} <-> |-- {{ P }} c {{ Q }}. *)

(** **** Exercise: 2 stars, standard (seq_assoc_der_n)  *)

Theorem seq_assoc_der_n: seq_assoc_der_n_statement.
Proof.
  unfold seq_assoc_der_n_statement.
  intros.
  pose proof unfold_CSeq_fold_CSeq P Q c1 Skip.
  pose proof unfold_CSeq_fold_CSeq P Q c2 Skip.
  apply (prop_iff H2).
  { apply seq_skip. }
  rewrite <- H.
  apply H1.
  apply seq_skip.
  apply H0.
Qed.

End Task2.

End Task2.

(* Thu Apr 30 00:22:48 CST 2020 *)
