(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1 and volume 2. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import PL.Imp.
Require Import PL.ImpExt2.
Import Relation_Operators.

(* ################################################################# *)
(** * Review: Programs' Denotations *)

Definition omega_union {A B} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (concat (test_rel (beval b)) then_branch)
    (concat (test_rel (beval (BNot b))) else_branch).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         test_rel (beval (BNot b))
  | S n' =>
         concat
           (test_rel (beval b))
           (concat
              loop_body
              (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

(* ################################################################# *)
(** * Inductively Defined Denotational Semantics *)

(** Today, we turn to consider a different approach of defining denotational
    semantics. The following Coq commands define [ceval] as an inductive
    predicate. *)

Module Inductive_Denotations.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      ceval CSkip st  st
  | E_Ass  : forall st1 st2 X E,
      st2 X = aeval E st1 ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      ceval (CAss X E) st1 st2
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (c1 ;; c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
      beval b st ->
      ceval c1 st st' ->
      ceval (If b Then c1 Else c2 EndIf) st st'
  | E_IfFalse : forall st st' b c1 c2,
      ~ beval b st ->
      ceval c2 st st' ->
      ceval (If b Then c1 Else c2 EndIf) st st'
  | E_WhileFalse : forall b st c,
      ~ beval b st ->
      ceval (While b Do c EndWhile) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval b st ->
      ceval c st st' ->
      ceval (While b Do c EndWhile) st' st'' ->
      ceval (While b Do c EndWhile) st st''.

(** What does this definition mean?

    - First, it defines a ternary relation. We can see this from [ceval]'s type.
      That is: [com -> state -> state -> Prop]. As we know, [ceval c st st']
      means executing [c] from state [st] may end in [st'].

    - Second, in only 7 situations, command-state-state triples can appear in
      this ternary relation. These 7 situations are tagged by [E_Skip], [E_Ass],
      [E_Seq], etc.

    - Using [E_Seq] as an example, it says, if [(c1, st, st')] is in this
      ternary relation and [(c2, st', st'')] is in this ternary relation, then
      [(c1;; c2, st', st'')] is also in this relation. This is rule stating who
      can appear in [ceval].

    - Overall, this definition says every triple in [ceval] must have a reason,
      one of these 7 kinds. If it is based an assumption that another triple is
      in [ceval], that one must have a reason as well.

    This is called an _inductive definition_ (归纳定义). Sometimes, we also call
    it a rule-based definition.

    It is worth noticing that this definition is very first-order, in contrast
    to the higher-order fashion in two previous lectures. Computer scientists
    even prefer not to call it denotational semantics but big-step semantics.
    That is, [ceval c st st'] holds if we can take a big step (executing [c])
    from [st] and get to [st']. You can find more information about it in
    << Software Foundations >> volume 1.

    Although we will not use this inductively defined [ceval] later in this
    course, but inductive definitions are widely used in programming language
    theories. *)

End Inductive_Denotations.

(* ################################################################# *)
(** * Understanding Inductive Propositions *)

(* ================================================================= *)
(** ** Stone game *)

(** Consider a simple game between two players.

    - There are [n] stones initially in a pile.

    - Players move in turn.

    - In his/her move, a player may remove one, two or three stones from the
      pile.

    - Who makes the pile empty wins the game.

    We can ask: if [n = 10], can the first player to move win the game? In the
    classical game theory, every game state is either a previous-player-win 
    state or a next-player-win state. In this example, a game state can be
    described by an integer, the number of stones left in the pile. And the
    question is just to ask whether [10] is a next-player-win state.

    Now, let's formalize these concepts in Coq. *)

Module StoneGame.

Inductive kind: Type :=
| previous_player_win
| next_player_win.

Inductive state_class: Z -> kind -> Prop :=
| neg_illegal: forall n,
    n < 0 ->
    state_class n next_player_win
| zero_win:
    state_class 0 previous_player_win
| winner_strategy_1: forall n,
    n > 0 ->
    state_class (n-1) previous_player_win ->
    state_class n next_player_win 
| winner_strategy_2: forall n,
    n > 0 ->
    state_class (n-2) previous_player_win ->
    state_class n next_player_win 
| winner_strategy_3: forall n,
    n > 0 ->
    state_class (n-3) previous_player_win ->
    state_class n next_player_win 
| loser_strategy: forall n,
    n > 0 ->
    state_class (n-1) next_player_win ->
    state_class (n-2) next_player_win ->
    state_class (n-3) next_player_win ->
    state_class n previous_player_win.

Theorem ten_wins: state_class 10 next_player_win.
Proof.
  intros.
  assert (H0: state_class 0 previous_player_win).
  { apply zero_win. }
  assert (H1: state_class 1 next_player_win).
  { apply winner_strategy_1; [ lia | exact H0 ]. }
  assert (H2: state_class 2 next_player_win).
  { apply winner_strategy_2; [ lia | exact H0 ]. }
  assert (H3: state_class 3 next_player_win).
  { apply winner_strategy_3; [ lia | exact H0 ]. }
  assert (H4: state_class 4 previous_player_win).
  { apply loser_strategy; [ lia | tauto ..]. }
  assert (H5: state_class 5 next_player_win).
  { apply winner_strategy_1; [ lia | exact H4 ]. }
  assert (H6: state_class 6 next_player_win).
  { apply winner_strategy_2; [ lia | exact H4 ]. }
  assert (H7: state_class 7 next_player_win).
  { apply winner_strategy_3; [ lia | exact H4 ]. }
  assert (H8: state_class 8 previous_player_win).
  { apply loser_strategy; [ lia | tauto ..]. }
  assert (H9: state_class 9 next_player_win).
  { apply winner_strategy_1; [ lia | exact H8 ]. }
  assert (H10: state_class 10 next_player_win).
  { apply winner_strategy_2; [ lia | exact H8 ]. }
  exact H10.
Qed.

End StoneGame.

(* ================================================================= *)
(** ** Reflexive Transitive Closure *)

(** The reflexive, transitive closure of a relation [R] is the smallest relation
    that contains [R] and is both reflexive and transitive. All three following
    definitions express this same meaning. *)

Inductive clos_refl_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Inductive clos_refl_trans_1n {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt1n_refl : forall x, clos_refl_trans_1n R x x
    | rt1n_trans_1n : forall x y z,
          R x y ->
          clos_refl_trans_1n R y z ->
          clos_refl_trans_1n R x z.

Inductive clos_refl_trans_n1 {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rtn1_refl : forall x, clos_refl_trans_n1 R x x
    | rtn1_trans_n1 : forall x y z : A,
          R y z ->
          clos_refl_trans_n1 R x y ->
          clos_refl_trans_n1 R x z.

(** Are they really equivalent? We can prove that they actually shares some
    common properties. *)

Lemma rt_trans_1n: forall A (R: A -> A -> Prop) x y z,
  R x y ->
  clos_refl_trans R y z ->
  clos_refl_trans R x z.
Proof.
  intros.
  eapply rt_trans with y; [| exact H0].
  apply rt_step.
  exact H.
Qed.

Lemma rt_trans_n1: forall A (R: A -> A -> Prop) x y z,
  R y z ->
  clos_refl_trans R x y ->
  clos_refl_trans R x z.
Proof.
(* WORKED IN CLASS *)
  intros.
  eapply rt_trans with y; [exact H0 |].
  apply rt_step.
  exact H.
Qed.

Lemma rt1n_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_1n R x y.
Proof.
(* WORKED IN CLASS *)
  intros.
  apply rt1n_trans_1n with y.
  + exact H.
  + apply rt1n_refl.
Qed.

Lemma rtn1_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_n1 R x y.
Proof.
(* WORKED IN CLASS *)
  intros.
  apply rtn1_trans_n1 with x.
  + exact H.
  + apply rtn1_refl.
Qed.

(* ================================================================= *)
(** ** Induction On Inductive Propositions *)

(** We will use the following proof as an example to show how to do induction
    over an inductively defined proposition. You may ask why we can do induction
    proof. Intuitively, the reason of why [clos_refl_trans_1n R x y] is a proof
    tree. Thus, we can do structural induction over proof trees. *)

Lemma rt1n_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  revert H0.
  induction H.
  + (* [clos_refl_trans_1n R a b] is true due to [rt1n_refl] *)
    (* i.e. [clos_refl_trans_1n R x x] holds, where [a = x], [b = x] *)
    tauto.
  + (* [clos_refl_trans_1n R a b] is true due to [rt1n_trans_1n] *)
    (* i.e. [clos_refl_trans_1n R x z] holds because [R x y] and
       [clos_refl_trans_1n R y z], where [a = x], [b = z] *)
    intros.
    apply rt1n_trans_1n with y.
    - exact H.
    - apply IHclos_refl_trans_1n, H1.
Qed.

(** In fact, the [revert] befor [induction] is not necessary. *)

Lemma rt1n_trans_again: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  induction H.
  + exact H0.
  + apply IHclos_refl_trans_1n in H0.
    apply rt1n_trans_1n with y.
    - exact H.
    - exact H0.
Qed.

(** Now, try to finish a similar proof by yourself. *)

Lemma rtn1_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_n1 R a b ->
  clos_refl_trans_n1 R b c ->
  clos_refl_trans_n1 R a c.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H0.
  + exact H.
  + apply rtn1_trans_n1 with y; tauto.
Qed.

(** In the end, we can prove equivalences. *)

Lemma rt1n_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_1n R a b -> clos_refl_trans R a b.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_1n with y; tauto.
Qed.

(** The other three directions are left as exercise. *)

Lemma rt_rt1n: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_1n R a b.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H.
  + apply rt1n_step, H.
  + apply rt1n_refl.
  + apply rt1n_trans with y; tauto.
Qed.

Lemma rtn1_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_n1 R a b -> clos_refl_trans R a b.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_n1 with y; tauto.
Qed.

Lemma rt_rtn1: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_n1 R a b.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H.
  + apply rtn1_step, H.
  + apply rtn1_refl.
  + apply rtn1_trans with y; tauto.
Qed.

(* ################################################################# *)
(** * 32-bit Evaluation Again *)

Module Bounded_Evaluation.

(** In this course, the expression evaluation of integer expressions is
unbounded, unlike the situation of normal programming languages like C and Java.
But still, we can define "whether evaluating an expression [a]" is within the
range of signed 32-bit integers. We have defined this property in our previous
lectures. We redefine it again as an inductive predicate in Coq. *)

Definition max32: Z := 2^31 -1.
Definition min32: Z := - 2^31.

Inductive signed32_eval: aexp -> state -> Z -> Prop :=
  | S32_ANum: forall (n: Z) st,
      min32 <= n <= max32 ->
      signed32_eval (ANum n) st n
  | S32_AId: forall (X: var) st,
      min32 <= st X <= max32 ->
      signed32_eval (AId X) st (st X)
  | S32_APlus: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 + v2 <= max32 ->
      signed32_eval (APlus a1 a2) st (v1 + v2)
  | S32_AMinus: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 - v2 <= max32 ->
      signed32_eval (AMinus a1 a2) st (v1 - v2)
  | S32_AMult: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 * v2 <= max32 ->
      signed32_eval (AMult a1 a2) st (v1 * v2).

(** In short, [signed32_eval a st v] says that evaluating [a] on state [st] is
within the range of signed 32-bit integers (including all intermediate results)
the final result is [v]. Obviously, the evaluation result must coincide with
the expressions' denotations defined by [aeval]. *)

Theorem signed32_eval_correct: forall a st v,
  signed32_eval a st v ->
  aeval a st = v.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    unfold Func.add.
    rewrite IHsigned32_eval1.
    rewrite IHsigned32_eval2.
    reflexivity.
  + simpl.
    unfold Func.sub.
    rewrite IHsigned32_eval1.
    rewrite IHsigned32_eval2.
    reflexivity.
  + simpl.
    unfold Func.mul.
    rewrite IHsigned32_eval1.
    rewrite IHsigned32_eval2.
    reflexivity.
Qed.

(** Similarly, we can defined 16-bit evaluation. *)

Definition max16: Z := 2^15 -1.
Definition min16: Z := - 2^15.

Inductive signed16_eval: aexp -> state -> Z -> Prop :=
  | S16_ANum: forall (n: Z) st,
      min16 <= n <= max16 ->
      signed16_eval (ANum n) st n
  | S16_AId: forall (X: var) st,
      min16 <= st X <= max16 ->
      signed16_eval (AId X) st (st X)
  | S16_APlus: forall a1 a2 st v1 v2,
      signed16_eval a1 st v1 ->
      signed16_eval a2 st v2 ->
      min16 <= v1 + v2 <= max16 ->
      signed16_eval (APlus a1 a2) st (v1 + v2)
  | S16_AMinus: forall a1 a2 st v1 v2,
      signed16_eval a1 st v1 ->
      signed16_eval a2 st v2 ->
      min16 <= v1 - v2 <= max16 ->
      signed16_eval (AMinus a1 a2) st (v1 - v2)
  | S16_AMult: forall a1 a2 st v1 v2,
      signed16_eval a1 st v1 ->
      signed16_eval a2 st v2 ->
      min16 <= v1 * v2 <= max16 ->
      signed16_eval (AMult a1 a2) st (v1 * v2).

(** Of course, 16-bit evaluation defines only a subset of 32-bit evaluation.
Second half of the proof is left as exercise. *)

Lemma range16_range32: forall v,
  min16 <= v <= max16 ->
  min32 <= v <= max32.
Proof.
  intros.
  unfold min16, max16 in H.
  unfold min32, max32.
  simpl in H.
  simpl.
  lia.
Qed.

Theorem signed16_signed32: forall a st v,
  signed16_eval a st v ->
  signed32_eval a st v.
Proof.
  intros.
  induction H.
  + apply S32_ANum.
    apply range16_range32.
    exact H.
  (* WORKED IN CLASS *)
  + apply S32_AId.
    apply range16_range32.
    exact H.
  + apply S32_APlus.
    - tauto.
    - tauto.
    - apply range16_range32.
      exact H1.
  + apply S32_AMinus.
    - tauto.
    - tauto.
    - apply range16_range32.
      exact H1.
  + apply S32_AMult.
    - tauto.
    - tauto.
    - apply range16_range32.
      exact H1.
Qed.

(** Moreover, from the definition of [signed32_eval], we know that if all
intermediate results of evaluating [a] on [st] fails in the range of 32-bit,
the same property is also true for any [a]'s subexpression [a']. We first
define [sub_aexp]. *)

Inductive sub_aexp: aexp -> aexp -> Prop :=
| sub_aexp_refl: forall e: aexp,
    sub_aexp e e
| sub_aexp_APlus1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (APlus e1 e2)
| sub_aexp_APlus2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (APlus e1 e2)
| sub_aexp_AMinus1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (AMinus e1 e2)
| sub_aexp_AMinus2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (AMinus e1 e2)
| sub_aexp_AMult1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (AMult e1 e2)
| sub_aexp_AMult2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (AMult e1 e2).

Theorem signed32_eval_sub_aexp: forall e1 e2 st,
  sub_aexp e1 e2 ->
  (exists v2, signed32_eval e2 st v2) ->
  (exists v1, signed32_eval e1 st v1).
Proof.
  intros.
(* WORKED IN CLASS *)
  induction H.
  + exact H0.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v1.
    tauto.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v2.
    tauto.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v1.
    tauto.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v2.
    tauto.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v1.
    tauto.
  + apply IHsub_aexp.
    clear IHsub_aexp.
    destruct H0.
    inversion H0; subst.
    exists v2.
    tauto.
Qed.

End Bounded_Evaluation.

(* ################################################################# *)
(** * Loop-free Programs *)

Module Loop_Free.

Import Relation_Operators.

(** Now, we prove that a loop free program always terminate. *)

Inductive loop_free: com -> Prop :=
  | loop_free_skip:
      loop_free Skip
  | loop_free_asgn: forall X E,
      loop_free (CAss X E)
  | loop_free_seq: forall c1 c2,
      loop_free c1 ->
      loop_free c2 ->
      loop_free (c1 ;; c2)
  | loop_free_if: forall b c1 c2,
      loop_free c1 ->
      loop_free c2 ->
      loop_free (If b Then c1 Else c2 EndIf).

Theorem loop_free_terminate: forall c,
  loop_free c ->
  (forall st1, exists st2, ceval c st1 st2).
Proof.
  intros.
  (** Try to understand why we need to strengthen the induction hypothesis
  here. *)
  revert st1.
  induction H; intros.
  + exists st1.
    unfold ceval.
    unfold id.
    reflexivity.
  + unfold ceval.
Abort.

(** In order to construct a program state [st2] here. We want to use the
    following definition and proof from our last lectures. *)

Definition state_update (st: state) (X: var) (v: Z): state :=
  fun Y => if (Nat.eq_dec X Y) then v else st Y.

Lemma state_update_spec: forall st X v,
  (state_update st X v) X = v /\
  (forall Y, X <> Y -> st Y = (state_update st X v) Y).
Proof.
  intros.
  unfold state_update.
  split.
  + destruct (Nat.eq_dec X X).
    - reflexivity.
    - assert (X = X). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec X Y).
    - tauto.
    - reflexivity.
Qed.

(** Now we are ready to prove [loop_free_terminate]. *)

Theorem loop_free_terminate: forall c,
  loop_free c ->
  (forall st1, exists st2, ceval c st1 st2).
Proof.
  intros.
  revert st1.
  induction H; intros.
  + exists st1.
    unfold ceval.
    unfold id.
    reflexivity.
  + unfold ceval.
    exists (state_update st1 X (aeval E st1)).
    apply state_update_spec.
  (* WORKED IN CLASS *)
  + specialize (IHloop_free1 st1).
    destruct IHloop_free1 as [st2 ?].
    specialize (IHloop_free2 st2).
    destruct IHloop_free2 as [st3 ?].
    exists st3.
    simpl.
    unfold concat.
    exists st2.
    tauto.
  + simpl.
    unfold if_sem.
    unfold union, concat, test_rel.
    simpl.
    pose proof classic (beval b st1).
    destruct H1.
    - specialize (IHloop_free1 st1).
      destruct IHloop_free1 as [st2 ?].
      exists st2.
      left.
      exists st1.
      tauto.
    - specialize (IHloop_free2 st1).
      destruct IHloop_free2 as [st2 ?].
      exists st2.
      right.
      exists st1.
      tauto.
Qed.

(** You migh wonder why we choose not to define "loop_free" by a recursive
function. For example: *)

Fixpoint loop_free_fun (c: com): Prop :=
  match c with
  | CSkip => True
  | CAss _ _ => True
  | CSeq c1 c2 => loop_free_fun c1 /\ loop_free_fun c2
  | CIf b c1 c2 => loop_free_fun c1 /\ loop_free_fun c2
  | CWhile _ _ => False
  end.

(** It is no problem. And you can try to prove a similar theorem about
termination. *)

Theorem loop_free_fun_terminate: forall c,
  loop_free_fun c ->
  (forall st1, exists st2, ceval c st1 st2).
Proof.
  intros.
  revert st1.
  induction c as [| X E | c1 IH1 c2 IH2 | b c1 IH1 c2 IH2 | b c]; intros.
(* WORKED IN CLASS *)
  + exists st1.
    unfold ceval.
    unfold id.
    reflexivity.
  + unfold ceval.
    exists (state_update st1 X (aeval E st1)).
    apply state_update_spec.
  + simpl in H.
    destruct H.
    specialize (IH1 H st1).
    destruct IH1 as [st2 ?].
    specialize (IH2 H0 st2).
    destruct IH2 as [st3 ?].
    exists st3.
    simpl.
    unfold concat.
    exists st2.
    tauto.
  + simpl in H.
    destruct H.
    simpl.
    unfold if_sem.
    unfold union, concat, test_rel.
    simpl.
    pose proof classic (beval b st1).
    destruct H1.
    - specialize (IH1 H st1).
      destruct IH1 as [st2 ?].
      exists st2.
      left.
      exists st1.
      tauto.
    - specialize (IH2 H0 st1).
      destruct IH2 as [st2 ?].
      exists st2.
      right.
      exists st1.
      tauto.
  + simpl in H.
    destruct H.
Qed.

(** If we compare [loop_free] and [loop_free_fun], the latter one is less
flexible to extend. *)

Inductive loop_free': com -> Prop :=
  | loop_free'_skip:
      loop_free' Skip
  | loop_free'_asgn: forall X E,
      loop_free' (CAss X E)
  | loop_free'_seq: forall c1 c2,
      loop_free' c1 ->
      loop_free' c2 ->
      loop_free' (c1 ;; c2)
  | loop_free'_if: forall b c1 c2,
      loop_free' c1 ->
      loop_free' c2 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_if_then: forall b c1 c2,
      (forall st, beval b st) ->
      loop_free' c1 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_if_else: forall b c1 c2,
      (forall st, ~ beval b st) ->
      loop_free' c2 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_while_false: forall b c,
      (forall st, ~ beval b st) ->
      loop_free' (While b Do c EndWhile).

(** This definition says: if an if-condition is always true, then the loops in
its else-branch should not be considered as real loops. Similarly, if an
if-condition is always false, then the loops in its then-branch should not be
considered as real loops. Also, if a while-loop's loop condition is always
false, the loop body will never be executed -- that is not a real loop either. *)

Theorem loop_free'_terminate: forall c,
  loop_free' c ->
  (forall st1, exists st2, ceval c st1 st2).
Proof.
(* WORKED IN CLASS *)
  intros.
  revert st1.
  induction H; intros.
  + exists st1.
    unfold ceval.
    unfold id.
    reflexivity.
  + unfold ceval.
    exists (state_update st1 X (aeval E st1)).
    apply state_update_spec.
  + specialize (IHloop_free'1 st1).
    destruct IHloop_free'1 as [st2 ?].
    specialize (IHloop_free'2 st2).
    destruct IHloop_free'2 as [st3 ?].
    exists st3.
    simpl.
    unfold concat.
    exists st2.
    tauto.
  + simpl.
    unfold if_sem.
    unfold union, concat, test_rel.
    simpl.
    pose proof classic (beval b st1).
    destruct H1.
    - specialize (IHloop_free'1 st1).
      destruct IHloop_free'1 as [st2 ?].
      exists st2.
      left.
      exists st1.
      tauto.
    - specialize (IHloop_free'2 st1).
      destruct IHloop_free'2 as [st2 ?].
      exists st2.
      right.
      exists st1.
      tauto.
  + (* new case # 1 *)
    simpl.
    unfold if_sem.
    unfold union, concat, test_rel.
    specialize (IHloop_free' st1).
    destruct IHloop_free' as [st2 ?].
    exists st2.
    left.
    exists st1.
    specialize (H st1).
    tauto.
  + (* new case # 2 *)
    simpl.
    unfold if_sem.
    unfold union, concat, test_rel.
    specialize (IHloop_free' st1).
    destruct IHloop_free' as [st2 ?].
    exists st2.
    right.
    exists st1.
    specialize (H st1).
    tauto.
  + (* new case # 3 *)
    simpl.
    exists st1.
    unfold loop_sem.
    unfold omega_union.
    exists O.
    simpl.
    unfold test_rel, Sets.complement.
    specialize (H st1).
    split.
    - reflexivity.
    - exact H.
Qed.

End Loop_Free.

(* Thu Apr 2 09:43:56 CST 2020 *)
