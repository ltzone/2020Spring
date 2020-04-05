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

Lemma Func_equiv_refl: forall A, Reflexive (@Func.equiv A).
Proof.
  intros.
  unfold Reflexive.
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

Lemma Func_test_eq_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_eq.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_eq.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_test_le_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_le.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_le.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_intersect_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A ==> @Sets.equiv A) Sets.intersect.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.intersect.
  intros A S1 S2 ? T1 T2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_complement_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A) Sets.complement.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.complement.
  intros A S1 S2 ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_complement_complement: forall A (S: A -> Prop),
  Sets.equiv (Sets.complement (Sets.complement S)) S.
Proof.
  intros.
  unfold Sets.equiv, Sets.complement.
  intros.
  tauto.
Qed.

Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.

Existing Instances Sets_equiv_refl
                   Sets_equiv_sym
                   Sets_equiv_trans
                   Func_test_eq_equiv
                   Func_test_le_equiv
                   Sets_intersect_equiv
                   Sets_complement_equiv.

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

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.

End Relation_Operators.

Import Relation_Operators.

Module Rel.

Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.

End Rel.

Lemma Rel_equiv_refl: forall A B, Reflexive (@Rel.equiv A B).
Proof.
  unfold Reflexive, Rel.equiv.
  intros.
  reflexivity.
Qed.

Lemma Rel_equiv_sym: forall A B, Symmetric (@Rel.equiv A B).
Proof.
  unfold Symmetric, Rel.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Rel_equiv_trans: forall A B, Transitive (@Rel.equiv A B).
Proof.
  unfold Transitive, Rel.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Rel_equiv_test_rel: forall A,
  Proper (@Sets.equiv A ==> @Rel.equiv A A) test_rel.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Rel.equiv, test_rel.
  intros A X Y ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Rel_equiv_concat: forall A,
  Proper (@Rel.equiv A A ==> @Rel.equiv A A ==> @Rel.equiv A A) concat.
Proof.
  unfold Proper, respectful.
  unfold Rel.equiv, concat.
  intros A X1 X2 ? Y1 Y2 ?.
  intros a c.
  unfold iff.
  split.
  + intros [b [? ?]].
    exists b.
    rewrite <- H, <- H0.
    tauto.
  + intros [b [? ?]].
    exists b.
    rewrite H, H0.
    tauto.
Qed.

Lemma Rel_equiv_union: forall A,
  Proper (@Rel.equiv A A ==> @Rel.equiv A A ==> @Rel.equiv A A) union.
Proof.
  unfold Proper, respectful.
  unfold Rel.equiv, union.
  intros A X1 X2 ? Y1 Y2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Rel_equiv_omega_union: forall A B (r1 r2: nat -> A -> B -> Prop),
  (forall n, Rel.equiv (r1 n) (r2 n)) ->
  Rel.equiv (omega_union r1) (omega_union r2).
Proof.
  unfold Rel.equiv, omega_union.
  intros.
  unfold iff; split; intros HH;
  destruct HH as [n ?]; exists n.
  + rewrite <- H.
    exact H0.
  + rewrite H.
    exact H0.
Qed.

Lemma Rel_equiv_Rel_le: forall A B (r1 r2: A -> B -> Prop),
  Rel.equiv r1 r2 <-> Rel.le r1 r2 /\ Rel.le r2 r1.
Proof.
  unfold Rel.equiv, Rel.le.
  intros.
  unfold iff at 1.
  split; intros.
  + split; intros ? ?; rewrite H; tauto.
  + destruct H.
    unfold iff; split.
    - apply H.
    - apply H0.
Qed.

Lemma union_comm: forall A B (r1 r2: A -> B -> Prop),
  Rel.equiv (union r1 r2) (union r2 r1).
Proof.
  intros.
  unfold Rel.equiv, union.
  intros.
  tauto.
Qed.

Existing Instances Rel_equiv_refl
                   Rel_equiv_sym
                   Rel_equiv_trans
                   Rel_equiv_test_rel
                   Rel_equiv_concat
                   Rel_equiv_union.

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

Lemma ceval_CSkip: ceval CSkip = id.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = concat (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Arguments ceval: simpl never.

Definition aexp_equiv (a1 a2: aexp): Prop :=
  Func.equiv (aeval a1) (aeval a2).

Lemma aexp_equiv_refl: Reflexive aexp_equiv.
Proof.
  unfold Reflexive, aexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma aexp_equiv_sym: Symmetric aexp_equiv.
Proof.
  unfold Symmetric, aexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma aexp_equiv_trans: Transitive aexp_equiv.
Proof.
  unfold Transitive, aexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma APlus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) APlus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMinus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMinus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMult_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMult.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Existing Instances aexp_equiv_refl
                   aexp_equiv_sym
                   aexp_equiv_trans
                   APlus_congr
                   AMinus_congr
                   AMult_congr.

Definition bexp_equiv (b1 b2: bexp): Prop :=
  Sets.equiv (beval b1) (beval b2).

Lemma bexp_equiv_refl: Reflexive bexp_equiv.
Proof.
  unfold Reflexive, bexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma bexp_equiv_sym: Symmetric bexp_equiv.
Proof.
  unfold Symmetric, bexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma bexp_equiv_trans: Transitive bexp_equiv.
Proof.
  unfold Transitive, bexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BEq_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BEq.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BLe_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BLe.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BAnd_congr:
  Proper (bexp_equiv ==> bexp_equiv ==> bexp_equiv) BAnd.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BNot_congr: Proper (bexp_equiv ==> bexp_equiv) BNot.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H.
  reflexivity.
Qed.

Existing Instances bexp_equiv_refl
                   bexp_equiv_sym
                   bexp_equiv_trans
                   BEq_congr
                   BLe_congr
                   BAnd_congr
                   BNot_congr.

Definition com_equiv (c1 c2: com): Prop :=
  Rel.equiv (ceval c1) (ceval c2).

Lemma com_equiv_refl: Reflexive com_equiv.
Proof.
  unfold Reflexive, com_equiv.
  intros.
  reflexivity.
Qed.

Lemma com_equiv_sym: Symmetric com_equiv.
Proof.
  unfold Symmetric, com_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma com_equiv_trans: Transitive com_equiv.
Proof.
  unfold Transitive, com_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CAss_congr: forall (X: var),
  Proper (aexp_equiv ==> com_equiv) (CAss X).
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, com_equiv, Rel.equiv.
  intros X E E' ?.
  intros st1 st2.
  rewrite ! ceval_CAss.
  unfold Func.equiv in H.
  specialize (H st1).
  rewrite H.
  reflexivity.
Qed.

Lemma CSeq_congr: Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CSeq.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CIf_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CIf.
  unfold if_sem.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.

Lemma CWhile_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c c' ?.
  rewrite ! ceval_CWhile.
  unfold loop_sem.
  apply Rel_equiv_omega_union.
  intros.
  induction n; simpl.
  + rewrite H.
    reflexivity.
  + rewrite IHn, H, H0.
    reflexivity.
Qed.

(* Fri Apr 3 20:44:09 CST 2020 *)
