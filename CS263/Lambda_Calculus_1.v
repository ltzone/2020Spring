Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import PL.ImpExt4.
Local Open Scope Z.
Local Open Scope string.

(* ################################################################# *)
(** * Lambda Expressions *)

(** You can play with lambda expressions in programming languages like C++,
    Ocaml, python and also Coq. In case you do not have their compilers
    installed (or the installed version is not correct), we provide some web
    pages that you can use.

    - For C++: [ https://www.onlinegdb.com/online_c++_compiler ].

    - For Ocaml: [ https://www.jdoodle.com/compile-ocaml-online ].

    - Python: [https://www.tutorialspoint.com/execute_python_online.php].

    Here is some toy programs. You may still remember [do_it_three_times].

    // C++
    #include <functional>
    #include <iostream>

    template <typename T>
    std::function<T(T)> do_it_three_times (std::function<T(T)> f) {
        return [f](T x) { return f(f(f(x))); };
    }

    int main() {
        std::function<int(int)> add_one = [](int x) {return x + 1; };
        std::function<int(int)> square = [](int x) {return x * x; };
        std::cout << do_it_three_times (add_one) (1);
        std::cout << std::endl;
        std::cout << do_it_three_times (square) (2);
        std::cout << std::endl;
        std::cout << do_it_three_times (do_it_three_times(add_one)) (0);
        std::cout << std::endl;
        // The following line does not work for C++,
        // because do_it_three_times is a function not an object
        // std::cout << do_it_three_times (do_it_three_times) (add_one) (0);
        std::function<std::function<int(int)>(std::function<int(int)>)>
          do_it_three_times_obj =
          [](std::function<int(int)> f) {return do_it_three_times (f); };
        std::cout << do_it_three_times (do_it_three_times_obj) (add_one) (0);
        std::cout << std::endl;
    }


    (* Ocaml *)
    let do_it_three_times f x = f (f (f x)) in
    let add_one x = x + 1 in
    let square x = x * x in
    Printf.printf "%d\n" (do_it_three_times add_one 1);
    Printf.printf "%d\n" (do_it_three_times square 2);
    Printf.printf "%d\n" (do_it_three_times (do_it_three_times add_one) 0);
    Printf.printf "%d\n" (do_it_three_times do_it_three_times add_one 0);


    # Python
    do_it_three_times = lambda f : lambda x : f (f (f (x)))
    add_one = lambda x : x + 1
    square = lambda x : x * x
    print (do_it_three_times (add_one) (1))
    print "\n"
    print (do_it_three_times (square) (2))
    print "\n"
    print (do_it_three_times (do_it_three_times (add_one)) (0))
    print "\n"
    print (do_it_three_times (do_it_three_times) (add_one) (0))
    print "\n"
*)

(** Here are syntax trees of lambda expressions with integers and booleans. *)

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

(** Here, [abs] means function abstraction and [app] means function application.
*)

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

Example DITT_ex_1: tm :=
  app (app do_it_three_times add_one) 1.

Example DITT_ex_2: tm :=
  app (app do_it_three_times square) 2.

Example DITT_ex_3: tm :=
  app (app do_it_three_times (app do_it_three_times add_one)) 0.

Example DITT_ex_4: tm :=
  app (app (app do_it_three_times do_it_three_times) add_one) 0.

(* ################################################################# *)
(** * Operational Semantics *)

(** It is critical to see that lambda-calculus does not simply define math
    functions and values. It also defines how to compute. *)

(**

    - [ app (abs x t1) t2 --> t1 [x |-> t2] ].

    It is called _beta reduction_.
*)

(** Now we start to define lambda expressions' small step semantics. In a symtax
    tree of [tm], all internal nodes are [abs] nodes and [app] nodes. As we
    discussed, function abstractions will not be simplified before substitution.
    Thus the only problem that remains is: how and especially in which order to
    evaluation function applications.

    - The function part should evaluated first. In other words, if [t1] steps to
      [t1'], then [app t1 t2] steps to [app t1' t2].

    - When the function part is already evaluated (e.g. [t1] = [abs x t1'], and
      [t1] = [con (op_const Oplus)]) and the argument part needs to be evaluated
      (i.e. [tm_pend t1]), then the argument part will be evaluated. In other
      words, if [tm_pend t1] and [step t2 t2'], then [step (app t1 t2) (app t1
      t2')].

    - If both function part [t1] and argument part [t2] are evaluated, then
      [app t1 t2] will be reduced to the result of function application.

    - If the function part [t1] are evaluated and its argument part [t2] does
      not need to be evaluated, then [app t1 t2] will be directly reduced to
      this function application's result.

*)

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

Example DITT_result_1:
  clos_refl_trans step
    (app (app do_it_three_times add_one) 1)
    4.

(** Informally,

  do_it_three_times add_one =
  (fun f x => f (f (f x))) add_one 1 =>
  (fun x => add_one (add_one (add_one x))) 1 =>
  add_one (add_one (add_one 1)) =
  add_one (add_one ((fun x => x + 1) 1)) =>
  add_one (add_one (1 + 1)) =>
  add_one (add_one 2) =
  add_one ((fun x => x + 1) 2) =>
  add_one (2 + 1) =>
  add_one 3 =
  (fun x => x + 1) 3 =>
  3 + 1 =>
  4
*)

Proof.
  unfold do_it_three_times, add_one.
  etransitivity_1n.
  { apply S_app1. apply S_beta. apply H_abs. }
  simpl subst.
  etransitivity_1n.
  { apply S_beta. apply H_con. }
  simpl subst.
  etransitivity_1n.
  {
    apply S_app2; [apply P_abs |].
    apply S_app2; [apply P_abs |].
    apply S_beta.
    apply H_con.
  }
  simpl subst.
  etransitivity_1n.
  {
    apply S_app2; [apply P_abs |].
    apply S_app2; [apply P_abs |].
    apply S_base.
    apply BS_plus.
  }
  simpl Z.add.
  simpl subst.
  etransitivity_1n.
  {
    apply S_app2; [apply P_abs |].
    apply S_beta.
    apply H_con.
  }
  simpl subst.
  etransitivity_1n.
  {
    apply S_app2; [apply P_abs |].
    apply S_base.
    apply BS_plus.
  }
  simpl Z.add.
  etransitivity_1n.
  { apply S_beta. apply H_con. }
  simpl subst.
  etransitivity_1n.
  { apply S_base. apply BS_plus. }
  simpl Z.add.
  reflexivity.
Qed.

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

Example DITT_result_2:
  clos_refl_trans step
    (app (app do_it_three_times square) 2)
    256.
Proof.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl subst.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl subst.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl subst.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl Z.mul.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl subst.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl Z.mul.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl subst.
  etransitivity_1n.
  { apply next_state_sound. reflexivity. }
  simpl Z.mul.
  reflexivity.
Qed.

Example DITT_result_3:
  clos_refl_trans step
    (app (app do_it_three_times (app do_it_three_times add_one)) 0)
    9.
Proof.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

Example DITT_result_4:
  clos_refl_trans step
    (app (app (app do_it_three_times do_it_three_times) add_one) 0)
    27.
Proof.
  repeat
    (etransitivity_1n; [apply next_state_sound; reflexivity | try simpl subst]).
  reflexivity.
Qed.

(* Mon May 25 12:42:58 CST 2020 *)
