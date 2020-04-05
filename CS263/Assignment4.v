(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/04/04.                                             *)
(* Due: 2020/04/08, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment4.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment4.vo" file is generated.         *)
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
Require Import PL.ImpExt3.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(** In this assignment, we are going to establish another denotational semantics
    for our simple imperative language. This time, a program's denotation is
    defined as a ternary relation. Specifically, [st1, t, st2] belongs to the
    denotation of program [c] if and only if executing [c] from [st1] may take
    time [t] and stop at state [st2].

    We could write a more realistic definition here, but in order to make things
    simple, we assume every assignment command takes one unit of time, every
    testing (for either if-command, or loop condition testing) takes one unit of
    time and the [Skip] command does not take any time. *)

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 0.

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    t = 1.

Definition seq_sem (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = t1 + t2.

Definition test_sem (X: state -> Prop): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ X st1 /\ t = 1.

Definition union_sem (d d': state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    d st1 t st2 \/ d' st1 t st2.

Definition if_sem (b: bexp) (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 => exists n, d n st1 t st2.

Definition loop_sem (b: bexp) (loop_body: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

(* ################################################################# *)
(** * Task 1: The Theory Of Ternary Relations *)

Definition sem_equiv (d1 d2: state -> Z -> state -> Prop): Prop :=
  forall st1 t st2, d1 st1 t st2 <-> d2 st1 t st2.

(** You should first prove that [sem_equiv] is an equivalence relation and it
    is preserved by [seq_sem], [union_sem], [omega_union_sem]. Also, [test_sem]
    will always turn equivalent state sets into equivalent ternary relations. *)

(** **** Exercise: 1 star, standard (sem_equiv_refl)  *)

Lemma sem_equiv_refl: Reflexive sem_equiv.
Proof.
  unfold Reflexive, sem_equiv.
  intros.
  split;intro;exact H.
Qed.
(** [] *)
  
(** **** Exercise: 1 star, standard (sem_equiv_sym)  *)

Lemma sem_equiv_sym: Symmetric sem_equiv.
Proof.
  unfold Symmetric, sem_equiv.
  intros.
  split;intro;apply H,H0.
Qed.
(** [] *)
  
(** **** Exercise: 1 star, standard (sem_equiv_trans)  *)

Lemma sem_equiv_trans: Transitive sem_equiv.
Proof.
  unfold Transitive, sem_equiv.
  intros.
  split;intro.
  - apply H0, H, H1.
  - apply H, H0, H1.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_sem_equiv)  *)

Lemma seq_sem_equiv: Proper (sem_equiv ==> sem_equiv ==> sem_equiv) seq_sem.
Proof.
  unfold Proper, respectful.
  intros. unfold seq_sem, sem_equiv.
  intros. split;intros [t1 [t2 [st' [H1 [H2 H3]]]]].
  - exists t1, t2, st'. repeat split.
    + apply H. exact H1.
    + apply H0. exact H2.
    + exact H3.
  - exists t1, t2, st'. repeat split.
    + apply H. exact H1.
    + apply H0. exact H2.
    + exact H3.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (union_sem_equiv)  *)

Lemma union_sem_equiv: Proper (sem_equiv ==> sem_equiv ==> sem_equiv) union_sem.
Proof.
  unfold Proper, respectful.
  intros. unfold union_sem, sem_equiv.
  intros. split;intros [H1|H1];
  try apply H in H1; try apply H0 in H1; tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (omega_union_sem_equiv)  *)

Lemma omega_union_sem_equiv: forall d1 d2: nat -> state -> Z -> state -> Prop,
  (forall n: nat, sem_equiv (d1 n) (d2 n)) ->
  sem_equiv (omega_union_sem d1) (omega_union_sem d2).  
Proof.
  intros.
  unfold sem_equiv, omega_union_sem.
  split;intros [n H0];exists n;apply H;tauto.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (test_sem_equiv)  *)

Lemma test_sem_equiv: Proper (Sets.equiv ==> sem_equiv) test_sem.
Proof.
  unfold Proper, respectful.
  intros. unfold sem_equiv,test_sem.
  intros. split; intros [H1 [H2 H3]];apply H in H2;tauto.
Qed.
(** [] *)

Existing Instances sem_equiv_refl
                   sem_equiv_sym
                   sem_equiv_trans
                   seq_sem_equiv
                   union_sem_equiv
                   test_sem_equiv.

(** Also, it is important that [union_sem] is commutative and associative, and
    [seq_sem] is associative, distributive and absorbing [skip_sem].  *)

(** **** Exercise: 1 star, standard (union_sem_comm)  *)

Lemma union_sem_comm: forall d1 d2,
  sem_equiv (union_sem d1 d2) (union_sem d2 d1).
Proof.
  intros.
  unfold sem_equiv, union_sem.
  intros. tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (union_sem_assoc)  *)

Lemma union_sem_assoc: forall d1 d2 d3,
  sem_equiv (union_sem d1 (union_sem d2 d3)) (union_sem (union_sem d1 d2) d3).
Proof.
  intros.
  unfold sem_equiv, union_sem.
  intros. tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_sem_assoc)  *)

Lemma seq_sem_assoc: forall d1 d2 d3,
  sem_equiv (seq_sem d1 (seq_sem d2 d3)) (seq_sem (seq_sem d1 d2) d3).
Proof.
Proof.
  intros.
  unfold sem_equiv, seq_sem.
  intros.
  split; intros [t1 [t2 [st3 [H1 H2]]]].
  - destruct H2 as [[t3 [t4 [st4 [H2 [H3 H4]]]]] H5].
    exists (t1+t3), t4, st4.
    repeat split;subst t t2;auto;try lia.
    exists t1,t3, st3.
    tauto.
  - destruct H2 as [H4 H5].
    destruct H1 as [t3 [t4 [st4 [H1 [H2 H3]]]]].
    exists t3, (t4 + t2), st4.
    repeat split;auto;try lia.
    exists t4, t2, st3.
    tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_union_distr_l)  *)

Lemma seq_union_distr_l: forall d1 d2 d3,
  sem_equiv
    (seq_sem d1 (union_sem d2 d3))
    (union_sem (seq_sem d1 d2) (seq_sem d1 d3)).
Proof.
  intros. unfold sem_equiv.
  intros. unfold seq_sem, union_sem. split;intro.
  - destruct H as [t1 [t2 [st3 [H1 [[H2|H2] H3]]]]].
    + left. exists t1, t2,st3. tauto.
    + right. exists t1, t2, st3. tauto.
  - destruct H as [[t1 [t2 [st3 H]]]|[t1 [t2 [st3 H]]]];
    exists t1, t2, st3;tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_union_distr_r)  *)

Lemma seq_union_distr_r: forall d1 d2 d3,
  sem_equiv
    (seq_sem (union_sem d1 d2) d3)
    (union_sem (seq_sem d1 d3) (seq_sem d2 d3)).
Proof.
  unfold sem_equiv, seq_sem, union_sem.
  intros. split;intro.
  - destruct H as [t1 [t2 [st3 [[H|H] H1]]]].
    + left. exists t1, t2, st3. tauto.
    + right. exists t1, t2, st3. tauto.
  - destruct H as [[t1 [t2 [st3 H]]]|[t1 [t2 [st3 H]]]];
    exists t1, t2, st3;tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_skip_l)  *)

Lemma seq_skip_l: forall d, sem_equiv (seq_sem skip_sem d) d.
Proof.
  intros. unfold sem_equiv, seq_sem, skip_sem.
  intros. split;intro.
  - destruct H as [t1 [t2 [st3 [[? ?] [? ?]]]]].
    subst. apply H1. 
  -  exists 0, t, st1. tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_skip_r)  *)

Lemma seq_skip_r: forall d, sem_equiv (seq_sem d skip_sem) d.
Proof.
  intros. unfold sem_equiv, seq_sem, skip_sem.
  intros. split;intro.
  - destruct H as [t1 [t2 [st3 [? [[? ?] ?]]]]].
    subst. rewrite Zplus_0_r. apply H. 
  - exists t, 0, st2. rewrite Zplus_0_r. tauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 2: Program Equivalence Is An Equivalence *)

(** By a different program semantics, we can have a different sense of program
    equivalence. For example, the following two program were thought to be
    equivalent in class because they have the same effects: [ X ::= 0 ] vs.
    [ X ::= 1;; X ::= 0 ]. However, they take different amount of time to
    execute according to our semantic model. Thus, in some sense, they are
    not that equivalent.

    In this task, we will prove for you that our new program equivalence (see
    below) is an equivalence relation. You need to answer some questions about
    these proofs. *)

Definition com_equiv (c1 c2: com): Prop :=
  sem_equiv (ceval c1) (ceval c2).

Lemma com_equiv_refl: Reflexive com_equiv.
Proof.
  unfold Reflexive, com_equiv.
  intros.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_refl_uses)  *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans].

    Hint: this is a multiple-choice problem. You should use an ascending Coq
    list to describe your answer, e.g. [1; 2; 3; 4], [1; 3], [2]. *)

Definition com_equiv_refl_uses: list Z := [1].
(** [] *)

Lemma com_equiv_sym: Symmetric com_equiv.
Proof.
  unfold Symmetric, com_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_sym_uses)  *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans]. *)

Definition com_equiv_sym_uses: list Z := [1;2;3].
(** [] *)

Lemma com_equiv_trans: Transitive com_equiv.
Proof.
  unfold Transitive, com_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_trans_uses)  *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans]. *)

Definition com_equiv_trans_uses: list Z := [1;3].
(** [] *)

(* ################################################################# *)
(** * Task 3: Program Equivalence Is A Congruence *)

(** In this task, you need to prove that [com_equiv] is a congruence. The first
    one is done for you.*)

Lemma CSeq_congr: Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros c1 c1' ? c2 c2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (CAss_congr)  *)

Instance asgn_congr: forall (X: var),
Proper (aexp_equiv ==> sem_equiv) (asgn_sem X).
Proof.
  unfold Proper, respectful.
  intros. unfold sem_equiv.
  unfold ceval, asgn_sem, sem_equiv.
  intros. split;intro.
  - rewrite <- H. exact H0.
  - rewrite H. exact H0.
Qed.

Lemma CAss_congr: forall (X: var),
  Proper (aexp_equiv ==> com_equiv) (CAss X).
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros X s1 s1' ?. simpl.
  rewrite H.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (CIf_congr)  *)

Lemma CIf_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros b b' ? x y ? x' y' ?.
  simpl. unfold if_sem. rewrite H0. rewrite H1.
  unfold bexp_equiv in H.
  simpl. rewrite H.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (CWhile_congr)  *)

Lemma CWhile_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
Proof.
  hnf. unfold respectful.
  unfold com_equiv.
  intros b b' ? x x' ?.
  simpl. unfold loop_sem.
  apply omega_union_sem_equiv.
  intros.
  induction n.
  - simpl. unfold bexp_equiv in H. rewrite H.
    reflexivity.
  - simpl. rewrite IHn. unfold bexp_equiv in H.
    rewrite H. rewrite H0. reflexivity.
Qed.

(** [] *)

(* ################################################################# *)
(** * Task 4: Typical Program Transiformations *)

(** In this task, you need to prove that the following transformations still
    genetate equivalent programs, according to our new definition of
    [com_equiv]. Hint: some lemmas that we have proved in previous tasks may be
    helpful. *)

(** **** Exercise: 1 star, standard (swap_if_branches)  *)

Theorem swap_if_branches : forall b c1 c2,
  com_equiv
    (If b Then c1 Else c2 EndIf)
    (If (BNot b) Then c2 Else c1 EndIf).
Proof.
  intros.
  unfold com_equiv. simpl.
  unfold if_sem.
  simpl.
  rewrite Sets_complement_complement.
  apply union_sem_comm.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_assoc)  *)

Theorem seq_assoc : forall c1 c2 c3,
  com_equiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  unfold com_equiv.
  simpl. rewrite seq_sem_assoc.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (if_seq)  *)
Theorem if_seq : forall b c1 c2 c3,
  com_equiv
    (If b Then c1 Else c2 EndIf;; c3)
    (If b Then c1;; c3 Else c2;; c3 EndIf).
Proof.
  intros.
  unfold com_equiv.
  simpl. unfold if_sem.
  rewrite seq_union_distr_r.
  rewrite !seq_sem_assoc.
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 5: Understanding Bourbaki-Witt Fix Point *)

Module BW_FixPoint.

Section BW_FixPoint.

(** Given a boolean expression [b] and a loop body's denotation [d], we have
    defined [loop_sem b d] as the whole loop's denotation. In this new
    denotational semantics, [loop_sem b d] is also the least fix point of the
    following [F], although its construction is not identical to the one in
    Bourbaki-Witt Fix Point theorem. *)

Variable b: bexp.
Variable d: state -> Z -> state -> Prop.
  
Definition F X := if_sem b (seq_sem d X) skip_sem.

(** In other words, [loop_sem b d] is equivalent with [F (loop_sem b d)]. *)

(** Now, let's discover the relation between our definition of [loop_sem] and
    Bourbaki-Witt's construction. Bourbaki-Witt's construction is based on a
    bottom element, in this case, the empty ternary relation. *)

Definition Bot: state -> Z -> state -> Prop := fun _ _ _ => False.

(** And the least fix point is the least upper bound of:

    - Bot

    - F Bot

    - F (F Bot)

    - F (F (F Bot))

    - ... *)

Fixpoint FBot (n: nat) :=
  match n with
  | O => Bot
  | S n' => F (FBot n')
  end.

Definition loop_sem' := omega_union_sem (FBot).

(** In this case, the least upper bound of a ternary relation sequence is their
    [omega_union_sem]. Thus, Bourbaki-Witt's fixpoint can be formalized as
    [loop_sem'] above. *)

End BW_FixPoint.

(** Now, let's discover the relationship between [loop_sem]'s construction and
    [loop_sem']'s construction.

    Hint 1: Both [iter_loop_body] and [FBot] are recursively defined. You may
    write [simpl] to use their definitions.

    Hint 2: Some properties about [union_sem], [seq_sem] and [skip_sem] in
    previous tasks may be helpful here.

    Hint 3: Proving some extra properties about [Bot] could make your proofs
    more concise. *)

(** **** Exercise: 2 stars, standard (FBot1_fact)  *)

Fact FBot1_fact: forall b d, sem_equiv (iter_loop_body b d 0) (FBot b d 1).
Proof.
  intros.
  simpl.
  unfold F, if_sem.
  simpl. rewrite seq_skip_r.
  split;intro.
  - right. exact H.
  - destruct H.
    + hnf in H. destruct H as [t1 [t2 [st3 [? [? ?]]]]].
      hnf in H0. destruct H0 as [t3 [t4 [st4 [? [? ?]]]]].
      hnf in H2. destruct H2.
    + exact H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (FBot2_fact)  *)

Instance FB_congruence b d : Proper (sem_equiv ==> sem_equiv) (F b d ).
Proof. hnf. intros.
  unfold F. unfold if_sem. rewrite H.
  reflexivity.
Qed.

Fact FBot2_fact: forall b d,
  sem_equiv
    (union_sem (iter_loop_body b d 1) (iter_loop_body b d 0))
    (FBot b d 2).
Proof.
  intros.
  replace (FBot b d 2) with (F b d (FBot b d 1)) by reflexivity.
  rewrite <- FBot1_fact.
  simpl. unfold F, if_sem.
  rewrite seq_skip_r.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (FBot_n_fact_statement)  *)

(** For generic natural number [n], what is the connection between [FBot b d n]
    and [iter_loop_body]? Write down a proposition to describe this connection.
    Note that your [FBot_n_fact_statement] should have the following form:

    - forall b d n, sem_equiv (...) (FBot b d n).

    And you probably need to write some auxiliary definition(s) first. *)

Fixpoint finite_union_sem (n:nat)
   (rs: nat -> state -> Z -> state -> Prop): state -> Z -> state -> Prop :=
   match n with
   | O => rs O
   | S n' => union_sem (rs (S n')) (finite_union_sem n' rs)
   end.

Definition FBot_n_fact_statement: Prop :=
  forall b d n, sem_equiv (finite_union_sem n (iter_loop_body b d)) (FBot b d (S n)).

Lemma FBot_n_fact_help: forall b d n,
  sem_equiv
    (finite_union_sem (S n) (iter_loop_body b d))
    ( union_sem
      (test_sem (beval (! b)))
      (seq_sem (test_sem (beval b))
         (seq_sem d (finite_union_sem n (iter_loop_body b d))))).
Proof.
  induction n.
  + simpl. apply union_sem_comm.
  + replace (finite_union_sem (S (S n)) (iter_loop_body b d)) with
    (union_sem (iter_loop_body b d (S (S n))) (finite_union_sem (S n) (iter_loop_body b d)))
    by reflexivity.
    rewrite IHn at 1.
    rewrite union_sem_assoc.
    rewrite (union_sem_comm _ (test_sem (beval (! b)))).
    rewrite <- union_sem_assoc.
    simpl. rewrite seq_union_distr_l.
    rewrite seq_union_distr_l. reflexivity.
Qed.

Theorem FBot_n_fact: FBot_n_fact_statement.
Proof.
  hnf. intros.
  induction n.
  - apply FBot1_fact.
  - replace (FBot b d (S (S n))) 
      with (F b d (FBot b d (S n))) by reflexivity.
    rewrite <- IHn.
    simpl. unfold F, if_sem.
    rewrite seq_skip_r.
    destruct n.
    + simpl. reflexivity.
    + simpl.
      rewrite (FBot_n_fact_help b d n) at 1.
      rewrite seq_union_distr_l.
      rewrite seq_union_distr_l.
      simpl.
      rewrite (union_sem_comm (test_sem (Sets.complement (beval b)))).
      rewrite union_sem_assoc.
      reflexivity.
Qed.

(** [] *)

End BW_FixPoint.

(* Fri Apr 3 20:44:10 CST 2020 *)
