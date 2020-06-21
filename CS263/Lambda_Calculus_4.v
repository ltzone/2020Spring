Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PL.ImpExt4.
Local Open Scope Z.
Local Open Scope string.
Local Open Scope list.

(* ################################################################# *)
(** * Lambda Expressions With References *)

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
  | Oread  (* new *)
  | Owrite (* new *)
  | Oalloc (* new *)
  .

Definition addr: Type := nat.
  
Inductive constant : Type :=
  | int_const (n: Z): constant
  | bool_const (b: bool): constant
  | op_const (o: op): constant
  | addr_const (p: addr): constant (* new *)
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

Example get_and_add :=
  abs "p" (
    \let "x" \be (app Oread "p") \in
    \let "_" \be (app (app Owrite "p") (app (app Oplus "x") 1)) \in
    "x").

Example alloc_get :=
  \let "p" \be (app Oalloc 0) \in
  app get_and_add "p".

Example alloc_get3 :=
  \let "p" \be (app Oalloc 1) \in
  \let "x" \be (app get_and_add "p") \in
  \let "y" \be (app get_and_add "p") \in
  \let "z" \be (app get_and_add "p") \in
  (100 * "x" + 10 * "y" + "z")%tm.

Print alloc_get3.

Example swap :=
  abs "p" (abs "q" (
    \let "x" \be (app Oread "p") \in
    \let "_" \be (app (app Owrite "p") (app Oread "q")) \in
    app (app Owrite "q") "x")).

Example swap12 :=
  \let "p" \be (app Oalloc 1) \in
  \let "q" \be (app Oalloc 2) \in
  \let "_" \be (app (app swap "p") "q") \in
  (10 * (app Oread "p") + app Oread "q")%tm.

Example fact3 :=
  \let "p" \be (app Oalloc (abs "x" "x")) \in
  \let "fact" \be
     (abs "x" 
       (app (app (app Oifthenelse ("x" == 0)%tm)
          1)
          ("x" * (app (app Oread "p") ("x" - 1)))%tm)) \in
  \let "_" \be (app (app Owrite "p") "fact") \in
  app "fact" 3.

Example fact4 :=
  \let "p" \be (app Oalloc (abs "x" "x")) \in
  \let "fact" \be
     (abs "x" 
       (app (app (app Oifthenelse ("x" == 0)%tm)
          1)
          ("x" * (app (app Oread "p") ("x" - 1)))%tm)) \in
  \let "_" \be (app (app Owrite "p") "fact") \in
  app "fact" 4.

(* ################################################################# *)
(** * Operational Semantics *)

Inductive tm_base_halt: tm -> Prop :=
  | BH_plus: forall n: Z, tm_base_halt (app Oplus n)
  | BH_minus: forall n: Z, tm_base_halt (app Ominus n)
  | BH_mult: forall n: Z, tm_base_halt (app Omult n)
  | BH_eq: forall n: Z, tm_base_halt (app Oeq n)
  | BH_le: forall n: Z, tm_base_halt (app Ole n)
  | BH_and: forall b: bool, tm_base_halt (app Oand b)
  | BH_if1: forall b: bool, tm_base_halt (app Oifthenelse b)
  | BH_if2: forall (b: bool) (t: tm), tm_base_halt (app (app Oifthenelse b) t)
  | BH_write: forall p: addr, tm_base_halt (app Owrite p) (* new *)
.

Inductive tm_base_pend: tm -> Prop :=
  | BP_plus: forall n: Z, tm_base_pend (app Oplus n)
  | BP_minus: forall n: Z, tm_base_pend (app Ominus n)
  | BP_mult: forall n: Z, tm_base_pend (app Omult n)
  | BP_eq: forall n: Z, tm_base_pend (app Oeq n)
  | BP_le: forall n: Z, tm_base_pend (app Ole n)
  | BP_and_true: tm_base_pend (app Oand true)
  | BP_write: forall p, tm_base_pend (app Owrite p) (* new *)
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

(* ################################################################# *)
(** * Executable Operational Semantics *)

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

Example result_1:
  clos_refl_trans step
    (alloc_get, nil)
    (0: tm, (1: tm) :: nil).
Proof.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

Example result_2:
  clos_refl_trans step
    (alloc_get3, nil)
    (123: tm, (4: tm) :: nil).
Proof.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

Example result_3:
  exists s,
  clos_refl_trans step
    (swap12, nil)
    (21: tm, s).
Proof.
  eexists.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

Example result_4:
  exists s,
  clos_refl_trans step
    (fact3, nil)
    (6: tm, s).
Proof.
  eexists.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

Example result_5:
  exists s,
  clos_refl_trans step
    (fact4, nil)
    (24: tm, s).
Proof.
  eexists.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

(* ################################################################# *)
(** * Typing *)

Inductive ty : Type :=
  | TBool : ty
  | TInt : ty
  | TArrow : ty -> ty -> ty
  | TUnit : ty
  | TRef : ty -> ty (* new *).

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

(** This system is type safe but not expressive enough for data structures
    like linked lists and binary trees. *)

(* Tue Jun 2 13:27:40 CST 2020 *)
