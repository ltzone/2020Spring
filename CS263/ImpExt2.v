Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.Imp.

Module Func.

Definition add {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a + g a.

Definition sub {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a - g a.

Definition mul {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a * g a.

Definition test_eq {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a = g a.

Definition test_le {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a <= g a.

Definition equiv {A: Type} (f g: A -> Z): Prop :=
  forall a, f a = g a.

Definition le {A: Type} (f g: A -> Z): Prop :=
  forall a, f a <= g a.

End Func.

Module Sets.

Definition full {A: Type}: A -> Prop := fun _ => True.

Definition empty {A: Type}: A -> Prop := fun _ => False.

Definition intersect {A: Type} (X Y: A -> Prop) := fun a => X a /\ Y a.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition equiv {A: Type} (X Y: A -> Prop): Prop :=
  forall a, X a <-> Y a.

End Sets.

Declare Scope func_scop.
Delimit Scope func_scope with Func.

Notation "f + g" := (Func.add f g): func_scope.
Notation "f - g" := (Func.sub f g): func_scope.
Notation "f * g" := (Func.mul f g): func_scope.

Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var (X: var): state -> Z := fun st => st X.

Fixpoint aeval (a : aexp) : state -> Z :=
  match a with
  | ANum n => constant_func n
  | AId X => query_var X
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.

Lemma Func_add_comm: forall {A} (f g: A -> Z),
  Func.equiv (f + g)%Func (g + f)%Func.
Proof.
(* WORKED IN CLASS *)
  intros.
  unfold Func.equiv, Func.add.
  intros.
  lia.
Qed.

(** Obviously, [Func.equiv] and [Sets.equiv] are equivalent relations, i.e. they
    are both _reflexive_ (自反的), _symmetric_ (对称的) and _transitive_
    (传递的). *)

Lemma Func_equiv_refl: forall A, Reflexive (@Func.equiv A).
Proof.
  intros.
  unfold Reflexive.
  (** Reflexive is defined in Coq standard library. We can unfold its
      definitions. *)
  unfold Func.equiv.
  intros.
  reflexivity.
Qed.

Lemma Func_equiv_sym: forall A, Symmetric (@Func.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Func.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Func_equiv_trans: forall A, Transitive (@Func.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Func.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_equiv_refl: forall A, Reflexive (@Sets.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold Sets.equiv.
  intros.
  tauto.
Qed.

Lemma Sets_equiv_sym: forall A, Symmetric (@Sets.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Sets.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_equiv_trans: forall A, Transitive (@Sets.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Sets.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_add_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.add.
Proof.
  intros.
  (** The following line exposes [Proper]'s meaning. *)
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.add.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_sub_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.sub.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.sub.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_mul_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.mul.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.mul.
  rewrite H, H0.
  reflexivity.
Qed.

(** Why using [Proper] is better than [Func_add_equiv_naive]? Coq supports
    rewriting via [Proper]! *)

Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.

Fixpoint beval (b : bexp) : state -> Prop :=
  match b with
  | BTrue       => Sets.full
  | BFalse      => Sets.empty
  | BEq a1 a2   => Func.test_eq (aeval a1) (aeval a2)
  | BLe a1 a2   => Func.test_le (aeval a1) (aeval a2)
  | BNot b1     => Sets.complement (beval b1)
  | BAnd b1 b2  => Sets.intersect (beval b1 ) (beval b2)
  end.

Module Relation_Operators.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition union {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b \/ r2 a b.

Definition intersection {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b /\ r2 a b.

Definition omega_union {A: Type} (rs: nat -> A -> A -> Prop): A -> A -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

End Relation_Operators.

Import Relation_Operators.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         intersection
           id
           (filter1 (beval (BNot b)))
  | S n' =>
            intersection
              (concat
                loop_body
                (iter_loop_body b loop_body n'))
              (filter1 (beval b))
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

(* Thu Mar 26 02:35:44 CST 2020 *)
