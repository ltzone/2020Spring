(** Remark. Some material in this lecture is from << Software Foundation >>
volume 2. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import PL.Lambda.
Local Open Scope Z.
Local Open Scope string.

Import LambdaIB.

(* ################################################################# *)
(** * Review *)

(** Lambda expressions' types are defined inductived as a ternary relation among
    type contexts (类型环境), lambda expressions and types.

    - [ Gamma |- t \in T ]

    Remark. In this setting, one expression may have different types, which
    seems not natural. In modern languages like C++ and ocaml, polymorphic types
    (like [ forall T, T ~> T ]) are introduced so that each legal lambda
    expression has only one type, if enough type annotations are provided. Also,
    type inference algorithms are designed so that the compiler can deduce types
    from limited annotations. We will not include polymorphic types and type
    inferences in this course. *)

(* ################################################################# *)
(** * Properties Of Evaluation Results *)

Lemma eval_result_bool : forall (t: tm),
  empty_context |- t \in TBool ->
  tm_halt t ->
  exists b: bool, t = b.
Proof.
  intros.
  inversion H; subst.
  + discriminate H1.
  + inversion H0; subst.
    inversion H3; subst; deduce_types_from_head H1.
  + inversion H1; subst.
    - exists b; reflexivity.
    - inversion H2.
Qed.

Lemma eval_result_int : forall (t: tm),
  empty_context |- t \in TInt ->
  tm_halt t ->
  exists n: Z, t = n.
Proof.
  intros.
  inversion H; subst.
  + discriminate H1.
  + inversion H0; subst.
    inversion H3; subst; deduce_types_from_head H1.
  + inversion H1; subst.
    - exists n; reflexivity.
    - inversion H2.
Qed.

Ltac deduce_int_bool_result H1 H2 :=
  first
    [ let n := fresh "n" in
      let H := fresh "H" in
      pose proof eval_result_int _ H1 H2 as [n H]
    | let b := fresh "b" in
      let H := fresh "H" in
      pose proof eval_result_bool _ H1 H2 as [b H]
    ].

(* ################################################################# *)
(** * Progress *)

Inductive halt_not_pend: tm -> Prop :=
  | HNP_and_false:
      halt_not_pend (app Oand false)
  | HNP_if1: forall b: bool,
      halt_not_pend (app Oifthenelse b)
  | HNP_if2: forall (b: bool) (t: tm),
      halt_not_pend (app (app Oifthenelse b) t).

Lemma base_pend_or_not_pend: forall t,
  tm_base_halt t ->
  tm_base_pend t \/ halt_not_pend t.
Proof.
  intros.
  inversion H; try first [left; constructor | right; constructor].
  subst t.
  destruct b; [left | right]; constructor.
Qed.

Lemma pend_or_not_pend: forall t,
  tm_halt t ->
  tm_pend t \/ halt_not_pend t.
Proof.
  intros.
  inversion H.
  + subst.
    left.
    apply P_abs.
  + subst.
    left.
    apply P_con.
  + subst.
    apply base_pend_or_not_pend in H0.
    destruct H0; [| tauto].
    left.
    apply P_base, H0.
Qed.

Lemma app_not_pending_progress: forall t1 t2 T11 T12,
  empty_context |- t1 \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  halt_not_pend t1 ->
  tm_halt (app t1 t2) \/ exists t', step (app t1 t2) t'.
Proof.
  intros.
  inversion H1; subst.
  + right.
    eexists.
    apply S_base.
    constructor.
  + left.
    apply H_base.
    constructor.
  + right.
    destruct b; eexists; apply S_base; constructor.
Qed.

Lemma app_const_halting_progress: forall (c: constant) t2 T11 T12,
  empty_context |- c \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  tm_halt t2 ->
  tm_halt (app c t2) \/ exists t', step (app c t2) t'.
Proof.
  intros.
  destruct c.
  + (* int_const *)
    inversion H; subst.
    inversion H4.
  + (* bool_const *)
    inversion H; subst.
    inversion H4.
  + (* op_const *)
    destruct o;
    deduce_types_from_head H;
    deduce_int_bool_result H0 H1; subst t2.
    - left.
      apply H_base.
      constructor.
    - left.
      apply H_base.
      constructor.
    - left.
      apply H_base.
      constructor.
    - left.
      apply H_base.
      constructor.
    - left.
      apply H_base.
      constructor.
    - right.
      eexists.
      apply S_base.
      constructor.
    - left.
      apply H_base.
      constructor.
    - left.
      apply H_base.
      constructor.
Qed.

Lemma app_base_pending_halting_progress: forall t1 t2 T11 T12,
  empty_context |- t1 \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  tm_base_pend t1 ->
  tm_halt t2 ->
  tm_halt (app t1 t2) \/ exists t', step (app t1 t2) t'.
Proof.
  intros.
  inversion H1; subst t1;
  deduce_types_from_head H;
  deduce_int_bool_result H0 H2; subst t2.
  + right.
    eexists.
    apply S_base.
    constructor.
  + right.
    eexists.
    apply S_base.
    constructor.
  + right.
    eexists.
    apply S_base.
    constructor.
  + right.
    destruct (Z.eq_dec n n0); eexists; apply S_base.
    - apply BS_eq_true; tauto.
    - apply BS_eq_false; tauto.
  + right.
    destruct (Z_le_gt_dec n n0); eexists; apply S_base.
    - apply BS_le_true; tauto.
    - apply BS_le_false; tauto.
  + right.
    eexists.
    apply S_base.
    constructor.
Qed.

Lemma app_pending_halting_progress: forall t1 t2 T11 T12,
  empty_context |- t1 \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  tm_pend t1 ->
  tm_halt t2 ->
  tm_halt (app t1 t2) \/ exists t', step (app t1 t2) t'.
Proof.
  intros.
  inversion H1; subst t1.
  + right.
    eexists.
    apply S_beta, H2.
  + eapply app_const_halting_progress;
      [exact H | exact H0 | exact H2].
  + eapply app_base_pending_halting_progress;
      [exact H | exact H0 | exact H3 | exact H2].
Qed.

Theorem progress : forall t T,
  empty_context |- t \in T ->
  tm_halt t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  remember empty_context as Gamma.
  induction Ht; subst Gamma.
  + (* T_var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  + (* T_abs *)
    (* Function abstraction is already halting *)
    left.
    apply H_abs.
    
  + (* T_app *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] steps... *)
    specialize (IHHt1 ltac:(reflexivity)).
    specialize (IHHt2 ltac:(reflexivity)).
    destruct IHHt1 as [| [t1' ?]].
    - (* evaluating t1 ends *)
      pose proof pend_or_not_pend _ H.
      destruct H0.
      * (* t2 needs to be evaluated *)
        destruct IHHt2 as [| [t2' ?]].
       ++ (* evaluating t2 also ends *)
          eapply app_pending_halting_progress;
            [exact Ht1 | exact Ht2 | exact H0 | exact H1].
       ++ (* t2 steps *)
          right; eexists.
          apply S_app2; [exact H0 |].
          apply H1.
      * (* t2 does not need to be evaluated *)
          eapply app_not_pending_progress;
            [exact Ht1 | exact Ht2 | exact H0].
    - (* t1 steps *)
      right; eexists.
      apply S_app1, H.

  + (* T_con *)
    left.
    apply H_con.
Qed.

(* ################################################################# *)
(** * Preservation *)

(** In order to prove preservation, we need to address 4 problems:

    - whether all base steps have the preservation property;

    - whether beta reduction steps have the preservation property;

    - if a step on [t1] has preservation, does the corresponding step on
      [app t1 t2] have preservation?

    - if a step on [t2] has preservation, does the corresponding step on
      [app t1 t2] have preservation?

    In fact, all other 3 things are easy, except the reasoning for beta
    reductinos. This is for base step's preservation: *)

Lemma base_preservation : forall t t' T,
  empty_context |- t \in T  ->
  base_step t t'  ->
  empty_context |- t' \in T.
Proof.
  intros.
  inversion H0; subst; deduce_types_from_head H; repeat constructor; tauto.
Qed.

(** For beta reductions, we need to analyze syntactic substituion,
    free variables and type contexts very carefully. If you forget, this is the
    definition of syntactic substitution in lambda expressions.

subst = 
fix subst (x : string) (s t : tm) {struct t} : tm :=
  match t with
  | var x' => if string_dec x x' then s else t
  | app t1 t2 => app (subst x s t1) (subst x s t2)
  | abs x' t1 => abs x' (if string_dec x x' then t1 else subst x s t1)
  | con c => con c
  end
     : string -> tm -> tm -> tm

    Here, we start with the definition of free variables. *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (app t1 t2)
  | afi_abs : forall x y t,
      y <> x  ->
      appears_free_in x t ->
      appears_free_in x (abs y t).

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma |- t \in T ->
  exists T', Gamma x = Some T'.
Proof.
  intros.
  revert Gamma T H0; induction H; intros.
  + (* afi_var *)
    inversion H0; subst.
    exists T; tauto.
  + (* afi_app *)
    inversion H0; subst.
    eapply IHappears_free_in, H4.
  + (* afi_app *)
    inversion H0; subst.
    eapply IHappears_free_in, H6.
  + (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H6.
    unfold context_update in H6.
    destruct (string_dec y x) in H6; [tauto |].
    exact H6.
Qed.

Corollary typable_empty__closed : forall t T,
    empty_context |- t \in T  ->
    closed t.
Proof.
  intros. unfold closed. intros ? ?.
  pose proof (free_in_context _ _ _ _ H0 H) as [?T ?].
  discriminate H1.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof.
  intros.
  revert Gamma' H0; induction H; intros.
  + (* T_var *)
    apply T_var.
    rewrite <- H0.
    - exact H.
    - constructor.
  + (* T_abs *)
    apply T_abs.
    apply IHhas_type.
    intros x' Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [x|->T11;Gamma] *)
    unfold context_update.
    destruct (string_dec x x'); [reflexivity |].
    apply H0.
    constructor; tauto.
  + (* T_App *)
    apply T_app with T11.
    - apply IHhas_type1.
      intros; apply H1.
      apply afi_app1, H2.
    - apply IHhas_type2.
      intros; apply H1.
      apply afi_app2, H2.
  + (* T_con *)
    apply T_con, H.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  (x |-> U ; Gamma) |- t \in T ->
  empty_context |- v \in U   ->
  Gamma |- t [x |-> v] \in T.
Proof.
  intros.
  revert Gamma T H; induction t; intros; inversion H; subst.
  + (* var *)
    rename s into y.
    simpl; unfold context_update in H3.
    destruct (string_dec x y) as [Hxy | Hxy].
    - (* x=y *)
      injection H3 as ?.
      subst.
      eapply context_invariance; [apply H0 |].
      apply typable_empty__closed in H0. unfold closed in H0.
      intros.
      specialize (H0 x); tauto.
    - (* x<>y *)
      apply T_var. tauto.
  + (* app *)
    simpl.
    eapply T_app with T11.
    - apply IHt1; tauto.
    - apply IHt2; tauto.
  + (* abs *)
    rename s into y.
    simpl.
    apply T_abs.
    destruct (string_dec x y) as [Hxy | Hxy].
    - (* x=y *)
      subst.
      eapply context_invariance; [apply H5 |].
      intros.
      unfold context_update.
      destruct (string_dec y x); reflexivity.
    - (* x<>y *)
      apply IHt.
      eapply context_invariance; [apply H5 |].
      intros z ?.
      unfold context_update.
      destruct (string_dec y z).
      * (* y=z *)
        subst.
        destruct (string_dec x z); [tauto | reflexivity].
      * reflexivity.
  + simpl.
    apply T_con, H3.
Qed.

Theorem preservation : forall t t' T,
  empty_context |- t \in T  ->
  step t t'  ->
  empty_context |- t' \in T.
Proof.
  intros.
  revert T H; induction H0; intros.
  + eapply base_preservation; [exact H0 | exact H].
  + inversion H0; subst.
    inversion H4; subst.
    apply substitution_preserves_typing with T11; tauto.
  + inversion H; subst.
    apply T_app with T11.
    - apply IHstep, H4.
    - apply H6.
  + inversion H1; subst.
    apply T_app with T11.
    - apply H5.
    - apply IHstep, H7.
Qed.



(* Tue Jun 2 13:27:40 CST 2020 *)
