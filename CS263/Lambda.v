(** (This following part of this file is copied from <<Software Foundation>>
volume 1 & 2. It should be only used for lecture notes and homework assignments
for course CS263 of Shanghai Jiao Tong University, 2020 spring. Any other usage
are not allowed. For the material of thses parts, please refer to the original
book.) *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PL.ImpExt4.
Local Open Scope Z.
Local Open Scope string.
Local Open Scope list.

Module LambdaIB.

Inductive op : Type :=
  | Oplus
  | Ominus
  | Omult
  | Oeq
  | Ole
  | Onot
  | Oand
  | Oifthenelse.

Inductive constant : Type :=
  | int_const (n: Z): constant
  | bool_const (b: bool): constant
  | op_const (o: op): constant.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> tm -> tm
  | con : constant -> tm.

Coercion var: string >-> tm.
Coercion op_const: op >-> constant.
Coercion bool_const: bool >-> constant.
Coercion int_const: Z >-> constant.
Coercion con: constant >-> tm.

Example do_it_three_times: tm :=
  abs "f" (abs "x" (app "f" (app "f" (app "f" "x")))).

Example add_one: tm :=
  abs "x" (app (app Oplus "x") 1).

Example square: tm :=
  abs "x" (app (app Omult "x") "x").

Inductive tm_base_halt: tm -> Prop :=
  | BH_plus: forall n: Z, tm_base_halt (app Oplus n)
  | BH_minus: forall n: Z, tm_base_halt (app Ominus n)
  | BH_mult: forall n: Z, tm_base_halt (app Omult n)
  | BH_eq: forall n: Z, tm_base_halt (app Oeq n)
  | BH_le: forall n: Z, tm_base_halt (app Ole n)
  | BH_and: forall b: bool, tm_base_halt (app Oand b)
  | BH_if1: forall b: bool, tm_base_halt (app Oifthenelse b)
  | BH_if2: forall (b: bool) (t: tm), tm_base_halt (app (app Oifthenelse b) t).

Inductive tm_base_pend: tm -> Prop :=
  | BP_plus: forall n: Z, tm_base_pend (app Oplus n)
  | BP_minus: forall n: Z, tm_base_pend (app Ominus n)
  | BP_mult: forall n: Z, tm_base_pend (app Omult n)
  | BP_eq: forall n: Z, tm_base_pend (app Oeq n)
  | BP_le: forall n: Z, tm_base_pend (app Ole n)
  | BP_and_true: tm_base_pend (app Oand true).

Inductive tm_halt: tm -> Prop :=
  | H_abs: forall x t, tm_halt (abs x t)
  | H_con: forall c, tm_halt (con c)
  | H_base: forall t, tm_base_halt t -> tm_halt t.

Inductive tm_pend: tm -> Prop :=
  | P_abs: forall x t, tm_pend (abs x t)
  | P_con: forall c, tm_pend (con c)
  | P_base: forall t, tm_base_pend t -> tm_pend t.

Inductive base_step: tm -> tm -> Prop :=
  | BS_plus: forall n1 n2: Z, base_step (app (app Oplus n1) n2) (n1 + n2)
  | BS_minus: forall n1 n2: Z, base_step (app (app Ominus n1) n2) (n1 - n2)
  | BS_mult: forall n1 n2: Z, base_step (app (app Omult n1) n2) (n1 * n2)
  | BS_eq_true: forall n1 n2: Z,
                  n1 = n2 -> base_step (app (app Oeq n1) n2) (true)
  | BS_eq_false: forall n1 n2: Z,
                  n1 <> n2 -> base_step (app (app Oeq n1) n2) (false)
  | BS_le_true: forall n1 n2: Z,
                  n1 <= n2 -> base_step (app (app Ole n1) n2) (true)
  | BS_le_false: forall n1 n2: Z,
                  n1 > n2 -> base_step (app (app Ole n1) n2) (false)
  | BS_not: forall b: bool, base_step (app Onot b) (negb b)
  | BS_and_true: forall b: bool, base_step (app (app Oand true) b) b
  | BS_and_false: forall t: tm, base_step (app (app Oand false) t) false
  | BS_if_true: forall t1 t2: tm,
                  base_step (app (app (app Oifthenelse true) t1) t2) t1
  | BS_if_false: forall t1 t2: tm,
                  base_step (app (app (app Oifthenelse false) t1) t2) t2
.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if string_dec x x' then s else t
  | abs x' t1 =>
      abs x' (if string_dec x x' then t1 else subst x s t1)
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | con c =>
      con c
  end.

Notation "t [ x |-> s ]" := (subst x s t) (at level 10, x at next level).

Inductive step: tm -> tm -> Prop :=
  | S_base: forall t t',
              base_step t t' -> step t t'
  | S_beta: forall x t1 t2,
              tm_halt t2 -> step (app (abs x t1) t2) (t1 [ x |-> t2])
  | S_app1: forall t1 t1' t2,
              step t1 t1' -> step (app t1 t2) (app t1' t2)
  | S_app2: forall t1 t2 t2',
              tm_pend t1 -> step t2 t2' -> step (app t1 t2) (app t1 t2')
.

Definition is_base_halting (t: tm): bool :=
  match t with
  | app (con (op_const Oplus)) (con (int_const _)) => true
  | app (con (op_const Ominus)) (con (int_const _)) => true
  | app (con (op_const Omult)) (con (int_const _)) => true
  | app (con (op_const Oeq)) (con (int_const _)) => true
  | app (con (op_const Ole)) (con (int_const _)) => true
  | app (con (op_const Oand)) (con (bool_const _)) => true
  | app (con (op_const Oifthenelse)) (con (bool_const _)) => true
  | app
      (app (con (op_const Oifthenelse)) (con (bool_const _)))
      (con (int_const _)) => true
  | _ => false
  end.

Definition is_base_pending (t: tm): bool :=
  match t with
  | app (con (op_const Oplus)) (con (int_const _)) => true
  | app (con (op_const Ominus)) (con (int_const _)) => true
  | app (con (op_const Omult)) (con (int_const _)) => true
  | app (con (op_const Oeq)) (con (int_const _)) => true
  | app (con (op_const Ole)) (con (int_const _)) => true
  | app (con (op_const Oand)) (con (bool_const true)) => true
  | _ => false
  end.

Definition is_halting (t: tm): bool :=
  match t with
  | abs _ _ => true
  | con _ => true
  | _ => is_base_halting t
  end.

Definition is_pending (t: tm): bool :=
  match t with
  | abs _ _ => true
  | con _ => true
  | _ => is_base_pending t
  end.

Definition base_next_state (t: tm): option tm :=
  match t with
  | app (app Oplus (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 + n2)))
  | app (app Ominus (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 - n2)))
  | app (app Omult (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 * n2)))
  | app (app Oeq (con (int_const n1))) (con (int_const n2)) =>
      if Z.eq_dec n1 n2
      then Some (con (bool_const true))
      else Some (con (bool_const false))
  | app (app Ole (con (int_const n1))) (con (int_const n2)) =>
      if Z_le_gt_dec n1 n2
      then Some (con (bool_const true))
      else Some (con (bool_const false))
  | app Onot (con (bool_const b)) =>
      Some (con (bool_const (negb b)))
  | app (app Oand (con (bool_const true))) (con (bool_const b)) =>
      Some (con (bool_const b))
  | app (app Oand (con (bool_const false))) _ =>
      Some (con (bool_const false))
  | app (app (app Oifthenelse (con (bool_const true))) t1) _ =>
      Some t1
  | app (app (app Oifthenelse (con (bool_const false))) _) t2 =>
      Some t2
  | _ => None
  end.

Definition beta_next_state (t: tm): option tm :=
  match t with
  | app (abs x t1) t2 => Some (t1 [x |-> t2])
  | _ => None
  end.

Definition core_next_state (t: tm): option tm :=
  match beta_next_state t, base_next_state t with
  | Some t', _ => Some t'
  | _, Some t' => Some t'
  | _, _ => None
  end.

Fixpoint next_state (t: tm): option tm :=
  match t with
  | app t1 t2 =>
      match next_state t1 with
      | Some t1' => Some (app t1' t2)
      | None => if is_pending t1
                then match next_state t2 with
                     | Some t2' => Some (app t1 t2')
                     | None => if is_halting t2
                               then core_next_state t
                               else None
                     end
                else base_next_state t
      end
  | _ => None
  end.

Ltac case_analysis_and_discriminiate H :=
  match type of H with
  | match ?t with _ => _ end = _ =>
      destruct t;
      match type of H with
      | false = true => discriminate H
      | None = Some _ => discriminate H
      | Some _ = Some _ => injection H as H
      | _ => idtac                                       
      end
  end.

Lemma is_base_halting_sound: forall t,
  is_base_halting t = true ->
  tm_base_halt t.  
Proof.
  intros.
  unfold is_base_halting in H.
  repeat case_analysis_and_discriminiate H; constructor.
Qed.

Lemma is_base_pending_sound: forall t,
  is_base_pending t = true ->
  tm_base_pend t.  
Proof.
  intros.
  unfold is_base_pending in H.
  repeat case_analysis_and_discriminiate H; constructor.
Qed.

Lemma is_halting_sound: forall t,
  is_halting t = true ->
  tm_halt t.  
Proof.
  intros.
  unfold is_halting in H.
  repeat case_analysis_and_discriminiate H; try constructor.
  + apply is_base_halting_sound in H; auto.
  + apply is_base_halting_sound in H; auto.
Qed.

Lemma is_pending_sound: forall t,
  is_pending t = true ->
  tm_pend t.  
Proof.
  intros.
  unfold is_pending in H.
  repeat case_analysis_and_discriminiate H; try constructor.
  + apply is_base_pending_sound in H; auto.
  + apply is_base_pending_sound in H; auto.
Qed.

Lemma base_next_state_sound: forall t t',
  base_next_state t = Some t' ->
  base_step t t'.
Proof.
  intros.
  unfold base_next_state in H.
  repeat case_analysis_and_discriminiate H; try (subst; constructor).
  + reflexivity.
  + tauto.
  + tauto.
  + tauto.
Qed.

Lemma beta_next_state_sound: forall t1 t2 t',
  tm_halt t2 ->
  beta_next_state (app t1 t2) = Some t' ->
  step (app t1 t2) t'.
Proof.
  intros.
  unfold beta_next_state in H0.
  repeat case_analysis_and_discriminiate H0.
  subst.
  apply S_beta, H.
Qed.

Lemma core_next_state_sound: forall t1 t2 t',
  tm_halt t2 ->
  core_next_state (app t1 t2) = Some t' ->
  step (app t1 t2) t'.
Proof.
  intros.
  unfold core_next_state in H0.
  destruct (beta_next_state (app t1 t2)) eqn:?H.
  + injection H0 as H0; subst t'.
    apply beta_next_state_sound; tauto.
  + destruct (base_next_state (app t1 t2)) eqn:?H; [| discriminate H0].
    injection H0 as H0; subst t'.
    apply base_next_state_sound in H2.
    apply S_base; tauto.
Qed.

Arguments base_next_state: simpl never.
Arguments beta_next_state: simpl never.
Arguments core_next_state: simpl never.

Lemma next_state_sound: forall t t',
  next_state t = Some t' ->
  step t t'.
Proof.
  intros.
  revert t' H; induction t; intros; simpl in H;
    [discriminate H | | discriminate H | discriminate H].
  destruct (next_state t1) eqn:?H in H.
  {
    apply IHt1 in H0.
    injection H as H; subst t'.
    apply S_app1, H0.
  }
  destruct (is_pending t1) eqn:?H in H.
  2: {
    apply base_next_state_sound in H.
    apply S_base, H.
  }
  apply is_pending_sound in H1.
  destruct (next_state t2) eqn:?H in H.
  {
    apply IHt2 in H2.
    injection H as H; subst t'.
    apply S_app2; tauto.
  }
  destruct (is_halting t2) eqn:?H in H.
  {
    apply is_halting_sound in H3.
    apply core_next_state_sound; tauto.
  }
  {
    discriminate H.
  }
Qed.

Inductive ty : Type :=
  | TBool : ty
  | TInt : ty
  | TArrow : ty -> ty -> ty.

Notation "T1 ~> T2" := (TArrow T1 T2) (right associativity, at level 30).

Definition context := string -> option ty.

Definition empty_context: context := fun _ => None.

Definition context_update (Gamma : context) (x : string) (T : ty) :=
  fun x' => if string_dec x x' then Some T else Gamma x'.

Notation "x '|->' T ';' Gamma" := (context_update Gamma x T)
  (at level 100, T at next level, right associativity).

Inductive op_type: op -> ty -> Prop :=
  | OT_plus: op_type Oplus (TInt ~> TInt ~> TInt)
  | OT_minus: op_type Ominus (TInt ~> TInt ~> TInt)
  | OT_mult: op_type Omult (TInt ~> TInt ~> TInt)
  | OT_eq: op_type Oeq (TInt ~> TInt ~> TBool)
  | OT_le: op_type Ole (TInt ~> TInt ~> TBool)
  | OT_not: op_type Onot (TBool ~> TBool)
  | OT_and: op_type Oand (TBool ~> TBool ~> TBool)
  | OT_if: forall T, op_type Oifthenelse (TBool ~> T ~> T ~> T)
.

Inductive const_type: constant -> ty -> Prop :=
  | CT_int: forall n, const_type (int_const n) TInt
  | CT_bool: forall b, const_type (bool_const b) TBool
  | CT_op: forall o T, op_type o T -> const_type (op_const o) T
.

Inductive has_type: context -> tm -> ty -> Prop :=
  | T_var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (var x) T
  | T_abs : forall Gamma x T11 T12 t12,
      has_type (x |-> T11 ; Gamma) t12 T12 ->
      has_type Gamma (abs x t12) (T11 ~> T12)
  | T_app : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (T11 ~> T12) ->
      has_type Gamma t2 T11 ->
      has_type Gamma (app t1 t2) T12
  | T_con : forall T Gamma c,
      const_type c T ->
      has_type Gamma (con c) T
.

Notation "Gamma '|-' t '\in' T" := (has_type Gamma t T) (at level 40).

Ltac base_deduce_types_from_head H :=
  match type of H with
  | const_type (int_const _) _ =>
    inversion H
  | const_type (bool_const _) _ =>
    inversion H
  | const_type (op_const _) _ =>
    let H1 := fresh "H" in
    inversion H as [| | ? ? H1]; subst;
    base_deduce_types_from_head H1;
    clear H1
  | op_type _ _ =>
    inversion H; subst
  | _ => idtac                                 
  end.

Ltac deduce_types_from_head H :=
  match type of H with
  | _ |- app _ _ \in _ =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    inversion H as [| | ? ? ? ? ? H1 H2 | ]; subst;
    deduce_types_from_head H1;
    clear H1
  | _ |- con _ \in _ =>
    let H1 := fresh "H" in
    inversion H as [| | | ? ? ? H1 ]; subst;
    base_deduce_types_from_head H1;
    clear H1
  | _ => idtac
  end.

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
    discriminate H.

  + (* T_abs *)
    left.
    apply H_abs.
    
  + (* T_app *)
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

Lemma base_preservation : forall t t' T,
  empty_context |- t \in T  ->
  base_step t t'  ->
  empty_context |- t' \in T.
Proof.
  intros.
  inversion H0; subst; deduce_types_from_head H; repeat constructor; tauto.
Qed.

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

End LambdaIB.

Module LambdaIBR.

Inductive op : Type :=
  | Oplus
  | Ominus
  | Omult
  | Oeq
  | Ole
  | Onot
  | Oand
  | Oifthenelse
  | Ounitele
  | Oread
  | Owrite
  | Oalloc
  .

Definition addr: Type := nat.
  
Inductive constant : Type :=
  | int_const (n: Z): constant
  | bool_const (b: bool): constant
  | op_const (o: op): constant
  | addr_const (p: addr): constant
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> tm -> tm
  | con : constant -> tm.

Coercion var: string >-> tm.
Coercion op_const: op >-> constant.
Coercion bool_const: bool >-> constant.
Coercion int_const: Z >-> constant.
Coercion addr_const: addr >-> constant.
Coercion con: constant >-> tm.

Definition letx (x: string) (t1 t2: tm): tm :=
  app (abs x t2) t1.

Notation "'\let' x '\be' t1 '\in' t2" :=
  (letx x t1 t2) (at level 20).

Notation "t1 + t2" := (app (app Oplus t1) t2): tm_scope.
Notation "t1 - t2" := (app (app Ominus t1) t2): tm_scope.
Notation "t1 * t2" := (app (app Omult t1) t2): tm_scope.
Notation "t1 == t2" := (app (app Oeq t1) t2)
                         (at level 70, no associativity): tm_scope.
Delimit Scope tm_scope with tm.

Inductive tm_base_halt: tm -> Prop :=
  | BH_plus: forall n: Z, tm_base_halt (app Oplus n)
  | BH_minus: forall n: Z, tm_base_halt (app Ominus n)
  | BH_mult: forall n: Z, tm_base_halt (app Omult n)
  | BH_eq: forall n: Z, tm_base_halt (app Oeq n)
  | BH_le: forall n: Z, tm_base_halt (app Ole n)
  | BH_and: forall b: bool, tm_base_halt (app Oand b)
  | BH_if1: forall b: bool, tm_base_halt (app Oifthenelse b)
  | BH_if2: forall (b: bool) (t: tm), tm_base_halt (app (app Oifthenelse b) t)
  | BH_write: forall p: addr, tm_base_halt (app Owrite p)
.

Inductive tm_base_pend: tm -> Prop :=
  | BP_plus: forall n: Z, tm_base_pend (app Oplus n)
  | BP_minus: forall n: Z, tm_base_pend (app Ominus n)
  | BP_mult: forall n: Z, tm_base_pend (app Omult n)
  | BP_eq: forall n: Z, tm_base_pend (app Oeq n)
  | BP_le: forall n: Z, tm_base_pend (app Ole n)
  | BP_and_true: tm_base_pend (app Oand true)
  | BP_write: forall p, tm_base_pend (app Owrite p)
.

Inductive tm_halt: tm -> Prop :=
  | H_abs: forall x t, tm_halt (abs x t)
  | H_con: forall c, tm_halt (con c)
  | H_base: forall t, tm_base_halt t -> tm_halt t.

Inductive tm_pend: tm -> Prop :=
  | P_abs: forall x t, tm_pend (abs x t)
  | P_con: forall c, tm_pend (con c)
  | P_base: forall t, tm_base_pend t -> tm_pend t.

Definition state := list tm.

Fixpoint read_state (s: state) (p: addr): option tm :=
  match s, p with
  | t :: _, O => Some t
  | _ :: s', S p' => read_state s' p'
  | _, _ => None
  end.

Fixpoint write_state (s: state) (p: addr) (t: tm): option state :=
  match s, p with
  | _ :: s', O => Some (t :: s')
  | s0 :: s', S p' =>
      match write_state s' p' t with
      | Some s'' => Some (s0 :: s'')
      | None => None
      end
  | _, _ => None
  end.

Definition alloc_state (s: state) (t: tm): state := s ++ t :: nil.

Definition new_address (s: state): addr := length s.

Inductive base_step: tm * state -> tm * state -> Prop :=
  | BS_plus: forall (n1 n2: Z) (s: state),
      base_step (app (app Oplus n1) n2, s) (n1 + n2: tm, s)
  | BS_minus: forall (n1 n2: Z) (s: state),
      base_step (app (app Ominus n1) n2, s) (n1 - n2: tm, s)
  | BS_mult: forall (n1 n2: Z) (s: state),
      base_step (app (app Omult n1) n2, s) (n1 * n2: tm, s)
  | BS_eq_true: forall (n1 n2: Z) (s: state),
      n1 = n2 ->
      base_step (app (app Oeq n1) n2, s) (true: tm, s)
  | BS_eq_false: forall (n1 n2: Z) (s: state),
      n1 <> n2 ->
      base_step (app (app Oeq n1) n2, s) (false: tm, s)
  | BS_le_true: forall (n1 n2: Z) (s: state),
      n1 <= n2 ->
      base_step (app (app Ole n1) n2, s) (true: tm, s)
  | BS_le_false: forall (n1 n2: Z) (s: state),
      n1 > n2 ->
      base_step (app (app Ole n1) n2, s) (false: tm, s)
  | BS_not: forall (b: bool) (s: state),
      base_step (app Onot b, s) (negb b: tm, s)
  | BS_and_true: forall (b: bool) (s: state),
      base_step (app (app Oand true) b, s) (b: tm, s)
  | BS_and_false: forall (t: tm) (s: state),
      base_step (app (app Oand false) t, s) (false: tm, s)
  | BS_if_true: forall (t1 t2: tm) (s: state),
      base_step (app (app (app Oifthenelse true) t1) t2, s) (t1, s)
  | BS_if_false: forall (t1 t2: tm) (s: state),
      base_step (app (app (app Oifthenelse false) t1) t2, s) (t2, s)
  | BS_read: forall (p: addr) (s: state) (t: tm),
      read_state s p = Some t ->
      base_step (app Oread p, s) (t, s)
  | BS_write: forall (p: addr) (t: tm) (s s': state),
      write_state s p t = Some s' ->
      base_step (app (app Owrite p) t, s) (Ounitele: tm, s')
  | BS_alloc: forall (t: tm) (s: state),
      base_step (app Oalloc t, s) (new_address s: tm, alloc_state s t)
.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if string_dec x x' then s else t
  | abs x' t1 =>
      abs x' (if string_dec x x' then t1 else subst x s t1)
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | con c =>
      con c
  end.

Notation "t [ x |-> s ]" := (subst x s t) (at level 10, x at next level).

Inductive step: tm * state -> tm * state -> Prop :=
  | S_base: forall t1 t2 s1 s2,
      base_step (t1, s1) (t2, s2) ->
      step (t1, s1) (t2, s2)
  | S_beta: forall x t1 t2 s,
      tm_halt t2 ->
      step (app (abs x t1) t2, s) (t1 [ x |-> t2], s)
  | S_app1: forall t1 t1' t2 s s',
      step (t1, s) (t1', s') ->
      step (app t1 t2, s) (app t1' t2, s')
  | S_app2: forall t1 t2 t2' s s',
      tm_pend t1 ->
      step (t2, s) (t2', s') ->
      step (app t1 t2, s) (app t1 t2', s')
.

Definition is_base_halting (t: tm): bool :=
  match t with
  | app (con (op_const Oplus)) (con (int_const _)) => true
  | app (con (op_const Ominus)) (con (int_const _)) => true
  | app (con (op_const Omult)) (con (int_const _)) => true
  | app (con (op_const Oeq)) (con (int_const _)) => true
  | app (con (op_const Ole)) (con (int_const _)) => true
  | app (con (op_const Oand)) (con (bool_const _)) => true
  | app (con (op_const Oifthenelse)) (con (bool_const _)) => true
  | app
      (app (con (op_const Oifthenelse)) (con (bool_const _)))
      (con (int_const _)) => true
  | app (con (op_const Owrite)) (con (addr_const _)) => true
  | _ => false
  end.

Definition is_base_pending (t: tm): bool :=
  match t with
  | app (con (op_const Oplus)) (con (int_const _)) => true
  | app (con (op_const Ominus)) (con (int_const _)) => true
  | app (con (op_const Omult)) (con (int_const _)) => true
  | app (con (op_const Oeq)) (con (int_const _)) => true
  | app (con (op_const Ole)) (con (int_const _)) => true
  | app (con (op_const Oand)) (con (bool_const true)) => true
  | app (con (op_const Owrite)) (con (addr_const _)) => true
  | _ => false
  end.

Definition is_halting (t: tm): bool :=
  match t with
  | abs _ _ => true
  | con _ => true
  | _ => is_base_halting t
  end.

Definition is_pending (t: tm): bool :=
  match t with
  | abs _ _ => true
  | con _ => true
  | _ => is_base_pending t
  end.

Definition base_next_state (t_s: tm * state): option (tm * state) :=
  let (t, s) := t_s in
  match t with
  | app (app Oplus (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 + n2)), s)
  | app (app Ominus (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 - n2)), s)
  | app (app Omult (con (int_const n1))) (con (int_const n2)) =>
      Some (con (int_const (n1 * n2)), s)
  | app (app Oeq (con (int_const n1))) (con (int_const n2)) =>
      if Z.eq_dec n1 n2
      then Some (con (bool_const true), s)
      else Some (con (bool_const false), s)
  | app (app Ole (con (int_const n1))) (con (int_const n2)) =>
      if Z_le_gt_dec n1 n2
      then Some (con (bool_const true), s)
      else Some (con (bool_const false), s)
  | app Onot (con (bool_const b)) =>
      Some (con (bool_const (negb b)), s)
  | app (app Oand (con (bool_const true))) (con (bool_const b)) =>
      Some (con (bool_const b), s)
  | app (app Oand (con (bool_const false))) _ =>
      Some (con (bool_const false), s)
  | app (app (app Oifthenelse (con (bool_const true))) t1) _ =>
      Some (t1, s)
  | app (app (app Oifthenelse (con (bool_const false))) _) t2 =>
      Some (t2, s)
  | app Oread (con (addr_const p)) =>
      match read_state s p with
      | Some t' => Some (t', s)
      | None => None
      end
  | app (app Owrite (con (addr_const p))) t0 =>
      match write_state s p t0 with
      | Some s' => Some (con (op_const Ounitele), s')
      | None => None
      end
  | app Oalloc t0 =>
      Some (con (addr_const (new_address s)), alloc_state s t0)
  | _ => None
  end.

Definition beta_next_state (t: tm): option tm :=
  match t with
  | app (abs x t1) t2 => Some (t1 [x |-> t2])
  | _ => None
  end.

Definition core_next_state (t_s: tm * state): option (tm * state) :=
  let (t, s) := t_s in
  match beta_next_state t, base_next_state (t, s) with
  | Some t', _ => Some (t', s)
  | _, Some t_s' => Some t_s'
  | _, _ => None
  end.

Fixpoint next_state_rec (t: tm) (s: state): option (tm * state) :=
  match t with
  | app t1 t2 =>
      match next_state_rec t1 s with
      | Some (t1', s') => Some (app t1' t2, s')
      | None => if is_pending t1
                then match next_state_rec t2 s with
                     | Some (t2', s') => Some (app t1 t2', s')
                     | None => if is_halting t2
                               then core_next_state (t, s)
                               else None
                     end
                else base_next_state (t, s)
      end
  | _ => None
  end.

Definition next_state (t_s: tm * state): option (tm * state) :=
  let (t, s) := t_s in
  next_state_rec t s.

Ltac destruct_eqn t :=
  first
    [ is_var t; destruct t
    | match type of t with sumbool _ _ => destruct t end
    | destruct t eqn:?H ].

Ltac case_analysis_and_discriminiate H :=
  match type of H with
  | match ?t with _ => _ end = _ =>
      destruct_eqn t;
      match type of H with
      | false = true => discriminate H
      | None = Some _ => discriminate H
      | Some _ = Some _ => injection H as H
      | _ => idtac                                       
      end
  end.

Lemma is_base_halting_sound: forall t,
  is_base_halting t = true ->
  tm_base_halt t.  
Proof.
  intros.
  unfold is_base_halting in H.
  repeat case_analysis_and_discriminiate H; constructor.
Qed.

Lemma is_base_pending_sound: forall t,
  is_base_pending t = true ->
  tm_base_pend t.  
Proof.
  intros.
  unfold is_base_pending in H.
  repeat case_analysis_and_discriminiate H; constructor.
Qed.

Lemma is_halting_sound: forall t,
  is_halting t = true ->
  tm_halt t.  
Proof.
  intros.
  unfold is_halting in H.
  repeat case_analysis_and_discriminiate H; try constructor.
  + apply is_base_halting_sound in H; auto.
  + apply is_base_halting_sound in H; auto.
Qed.

Lemma is_pending_sound: forall t,
  is_pending t = true ->
  tm_pend t.  
Proof.
  intros.
  unfold is_pending in H.
  repeat case_analysis_and_discriminiate H; try constructor.
  + apply is_base_pending_sound in H; auto.
  + apply is_base_pending_sound in H; auto.
Qed.

Lemma base_next_state_sound: forall t_s t_s',
  base_next_state t_s = Some t_s' ->
  base_step t_s t_s'.
Proof.
  intros.
  destruct t_s as [t s], t_s' as [t' s'].
  unfold base_next_state in H.
  repeat case_analysis_and_discriminiate H; try (subst; constructor).
  + reflexivity.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
Qed.

Lemma beta_next_state_sound: forall t1 t2 t' s,
  tm_halt t2 ->
  beta_next_state (app t1 t2) = Some t' ->
  step (app t1 t2, s) (t', s).
Proof.
  intros.
  unfold beta_next_state in H0.
  repeat case_analysis_and_discriminiate H0.
  subst.
  apply S_beta, H.
Qed.

Lemma core_next_state_sound: forall t1 t2 t' s s',
  tm_halt t2 ->
  core_next_state (app t1 t2, s) = Some (t', s') ->
  step (app t1 t2, s) (t', s').
Proof.
  intros.
  unfold core_next_state in H0.
  destruct (beta_next_state (app t1 t2)) eqn:?H.
  + injection H0 as H0 H2; subst t' s'.
    apply beta_next_state_sound; tauto.
  + destruct (base_next_state (app t1 t2, s)) eqn:?H; [| discriminate H0].
    injection H0 as H0; subst p.
    apply base_next_state_sound in H2.
    apply S_base; tauto.
Qed.

Arguments base_next_state: simpl never.
Arguments beta_next_state: simpl never.
Arguments core_next_state: simpl never.

Lemma next_state_sound: forall t_s t_s',
  next_state t_s = Some t_s' ->
  step t_s t_s'.
Proof.
  intros.
  destruct t_s as [t s], t_s' as [t' s'].
  simpl in H.
  revert t' s' H; induction t; intros; simpl in H;
    [discriminate H | | discriminate H | discriminate H].
  destruct (next_state_rec t1 s) as [[? ?] |] eqn:?H in H.
  {
    apply IHt1 in H0.
    injection H as H; subst t' s'.
    apply S_app1, H0.
  }
  destruct (is_pending t1) eqn:?H in H.
  2: {
    apply base_next_state_sound in H.
    apply S_base, H.
  }
  apply is_pending_sound in H1.
  destruct (next_state_rec t2 s) as [[? ?] |] eqn:?H in H.
  {
    apply IHt2 in H2.
    injection H as H; subst t' s'.
    apply S_app2; tauto.
  }
  destruct (is_halting t2) eqn:?H in H.
  {
    apply is_halting_sound in H3.
    apply core_next_state_sound; tauto.
  }
  {
    discriminate H.
  }
Qed.

Inductive ty : Type :=
  | TBool : ty
  | TInt : ty
  | TArrow : ty -> ty -> ty
  | TUnit : ty
  | TRef : ty -> ty.

Notation "T1 ~> T2" := (TArrow T1 T2) (right associativity, at level 30).

Definition context := string -> option ty.

Definition empty_context: context := fun _ => None.

Definition context_update (Gamma : context) (x : string) (T : ty) :=
  fun x' => if string_dec x x' then Some T else Gamma x'.

Notation "x '|->' T ';' Gamma" := (context_update Gamma x T)
  (at level 100, T at next level, right associativity).

Definition state_ty := list ty.

Fixpoint addr_ty (ST: state_ty) (p: addr): option ty :=
  match ST, p with
  | T :: _, O => Some T
  | _ :: ST', S p' => addr_ty ST' p'
  | _, _ => None
  end.

Inductive op_type: op -> ty -> Prop :=
  | OT_plus: op_type Oplus (TInt ~> TInt ~> TInt)
  | OT_minus: op_type Ominus (TInt ~> TInt ~> TInt)
  | OT_mult: op_type Omult (TInt ~> TInt ~> TInt)
  | OT_eq: op_type Oeq (TInt ~> TInt ~> TBool)
  | OT_le: op_type Ole (TInt ~> TInt ~> TBool)
  | OT_not: op_type Onot (TBool ~> TBool)
  | OT_and: op_type Oand (TBool ~> TBool ~> TBool)
  | OT_if: forall T, op_type Oifthenelse (TBool ~> T ~> T ~> T)
  | OT_read: forall T, op_type Oread (TRef T ~> T)
  | OT_write: forall T, op_type Owrite (TRef T ~> T ~> TUnit)
  | OT_alloc: forall T, op_type Oalloc (T ~> TRef T)
.

Inductive const_type: state_ty -> constant -> ty -> Prop :=
  | CT_int: forall n ST, const_type ST (int_const n) TInt
  | CT_bool: forall b ST, const_type ST (bool_const b) TBool
  | CT_op: forall o ST T, op_type o T -> const_type ST (op_const o) T
  | CT_addr: forall p ST T,
      addr_ty ST p = Some T -> const_type ST (addr_const p) T
.

Inductive has_type: context -> state_ty -> tm -> ty -> Prop :=
  | T_var : forall Gamma ST x T,
      Gamma x = Some T ->
      has_type Gamma ST (var x) T
  | T_abs : forall Gamma ST x T11 T12 t12,
      has_type (x |-> T11 ; Gamma) ST t12 T12 ->
      has_type Gamma ST (abs x t12) (T11 ~> T12)
  | T_app : forall T11 T12 Gamma ST t1 t2,
      has_type Gamma ST t1 (T11 ~> T12) ->
      has_type Gamma ST t2 T11 ->
      has_type Gamma ST (app t1 t2) T12
  | T_con : forall T Gamma ST c,
      const_type ST c T ->
      has_type Gamma ST (con c) T
.

Notation "Gamma '|-' t '\in' T" := (has_type Gamma t T) (at level 40).

End LambdaIBR.

