(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1 and volume 2. *)

Require Import PL.Imp.
Require Import PL.ImpExt1.
Require Import PL.ImpExt2.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Import Relation_Operators.

(* ################################################################# *)
(** * Review: Programs' Denotation *)

(** In the last lecture, we learnt to define expressions' denotations.
    Specifically, an integer expression's denotation is a function from program
    states to integers, and a boolean expression's denotation is a subset of
    program states. Sometimes, we will also write [   {[  ]}   ] to describe
    expression denotation. For example, our definition of [aeval] and [beval]
    partly say:

    [[
    - {[ a1 + a2 ]} = {[ a1 ]} + {[ a2 ]}

    - {[ a1 - a2 ]} = {[ a1 ]} - {[ a2 ]}

    - {[ a1 * a2 ]} = {[ a1 ]} * {[ a2 ]}

    - {[ b1 && b2 ]} = the intersection of {[ b1 ]} and {[ b2 ]}

    - {[ ! b ]} = the complement of {[ b ]}.
    ]]

    For programs, we use binary relations between program states to represent
    their denotations.
*)

Module CEval_first_try.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).

(** Soppose [then_branch] and [else_branch] are denotations of the then-branch
and else-branch of an if-command. Here, the first clause of [union] the set of
program state pairs ([st1], [st2]) such that:
     - ([st1], [st2]) belongs to [then_branch] and [b] is true on [st1]
And similarly, the second clause of [union] the set of program state pairs
([st1], [st2]) such that:
     - ([st1], [st2]) belongs to [else_branch] and [b] is false on [st1]
The union of them is the semantics of an if-command. *)

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile _ _ => empty
  end.

(** Here, a pair [(st1, st2)] is inside the denotation of [c] if and only if
    [ceval c st1 st2] holds. The following notation and lemmas may help you
    understand. *)

Notation "'The_pair_(' st1 , st2 ')_is_in_{[' c  ]}" := (ceval c st1 st2) (at level 45, no associativity).

Lemma ceval_skip: forall st1 st2,
  The_pair_( st1 , st2 )_is_in_{[ Skip ]} <->
  st1 = st2.
Proof.
  intros.
  simpl.
  unfold id.
  tauto.
Qed.

Lemma ceval_seq: forall st1 st3 c1 c2,
  The_pair_( st1 , st3 )_is_in_{[ c1;; c2 ]} <->
  exists st2,
    The_pair_( st1 , st2 )_is_in_{[ c1 ]} /\
    The_pair_( st2 , st3 )_is_in_{[ c2 ]}.
Proof.
  intros.
  simpl.
  unfold concat.
  tauto.
Qed.

Lemma ceval_if: forall st1 st2 b c1 c2,
  The_pair_( st1 , st2 )_is_in_{[ If b Then c1 Else c2 EndIf ]} <->
  The_pair_( st1 , st2 )_is_in_{[ c1 ]} /\ beval b st1 \/
  The_pair_( st1 , st2 )_is_in_{[ c2 ]} /\ ~ beval b st1.
Proof.
  intros.
  simpl.
  unfold if_sem.
  unfold union, intersection, filter1.  
  simpl.
  unfold Sets.complement.
  tauto.
Qed.

End CEval_first_try.

(* ################################################################# *)
(** * Loops' Denotations *)

(** Loops' semantics is comparatively nontrivial. One understanding is:
    [While b Do c EndWhile] will test [b] first then either do [Skip] or execute
    [c ;; While b Do c EndWhile]. Another understanding is: a loop means
    executing the loop body zero time, one time, two times, or etc. *)

(** The first understanding is kind of self-defined. We choose the second one.
    The following recursive function defines the semantics of executing the loop
    body for exactly [n] times. In Coq, [nat] represents nature numbers. Coq
    users can write functions recursively on nature numbers. Specifically, a
    natural number [n] is either zero [O] (the "O" of Omega) or the successor of
    another natural number [n'], written as [S n']. *)

Module CEval_second_try.

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

(** In short, [iter_loop_body b loop_body n] is defined as:

    - if [n = 0], identity relation with the restriction that [b] is not true;

    - if [n = n' + 1], first do [loop_body] then do [iter_loop_body b loop_body n']
      with the restriction that [b] is true at beginning. *)

(** The union of these binary relations is exactly the meaning of [while] loops.
    The following relation operator [omega_union] defines the union of countably
    many relations. *)

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  omega_union (iter_loop_body b loop_body).

(** With [loop_sem] which is just defined, we are eventually ready to complete
    our definition of [ceval]. *)

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).

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

End CEval_second_try.

(** The next definition, which is also our final definition, shows another
    approach of describing "testing and branching". *)

Module Relation_Operators2.

Definition omega_union {A B} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.

End Relation_Operators2.

Import Relation_Operators2.

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

Notation "'The_pair_(' st1 , st2 ')_is_in_{[' c  ]}" :=
  (ceval c%imp st1 st2) (at level 45, no associativity, c at level 0).

(** The following five lemmas are only presented for Coq proofs' convenience. *)

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

(* ################################################################# *)
(** * Semantic Equivalence *)

(* ================================================================= *)
(** ** An Equivalence Between Integer Expressions *)

(** One week ago, we have defined semantic equivalence between integer
    expressions by:

    - Two expressions [a1] and [a2] are equivalent if evaluating them on [st]
      has the same result for every program state [st].

    Now, using higher-order understanding, we can restate it as follows:

    - Two expressions [a1] and [a2] are equivalent if their denotations are
      equivalent functions.

    Formally: *)

Definition aexp_equiv (a1 a2: aexp): Prop :=
  Func.equiv (aeval a1) (aeval a2).

(** It is a equivalence relation. *)

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

(** Moreover, it is a _congruence_ (同余关系). That is, the equivalence of two
    subexpressions implies the equivalence of the larger expressions in which
    they are embedded.

    The main idea is that the congruence property allows us to replace a small
    part of a large expression with an equivalent small part and know that the
    whole large expressions are equivalent _without_ doing an explicit proof
    about the non-varying parts -- i.e., the "proof burden" of a small change
    to a large expression is proportional to the size of the change, not the
    expression. *)

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

(* ================================================================= *)
(** ** An Equivalence Between Boolean Expressions *)

(** Then we will establish the theory of boolean expression's equivalence. *)

Definition bexp_equiv (b1 b2: bexp): Prop :=
  Sets.equiv (beval b1) (beval b2).

(** We need the following auxiliary lemmas. *)

Lemma Sets_equiv_refl: forall A, Reflexive (@Sets.equiv A).
Proof.
  unfold Reflexive, Sets.equiv.
  intros.
  reflexivity.
Qed.

Lemma Sets_equiv_sym: forall A, Symmetric (@Sets.equiv A).
Proof.
  unfold Symmetric, Sets.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_equiv_trans: forall A, Transitive (@Sets.equiv A).
Proof.
  unfold Transitive, Sets.equiv.
  intros.
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

Existing Instances Sets_equiv_refl
                   Sets_equiv_sym
                   Sets_equiv_trans
                   Func_test_eq_equiv
                   Func_test_le_equiv
                   Sets_intersect_equiv
                   Sets_complement_equiv.

(** Similar to integer expressions' equivalence, boolean expressions'
    equivalence is also an equivalence relation and a congruence relation. *)

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

(* ================================================================= *)
(** ** An Equivalence Between Programs *)

(** For program equivalence, we need to define equivalence between relations
    first. *)

Module Rel.

Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.

End Rel.

(** Here is its properties. *)

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

(** Then we define program equivalence and prove its properties. *)

Definition com_equiv (c1 c2: com): Prop :=
  Rel.equiv (ceval c1) (ceval c2).

(** This just says, two programs [c1] and [c2] are equivalent when [c1] turns
    [st1] to [st2] if and only if [c2] also turns [st1] to [st2], for any [st1]
    and [st2]. This relation is also an equivalence and congruence. *)

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

(** Program equivalence is the theoretical foundation of compiler optimization.
    Let's take a look at some typical examples. *)



(** For examples of general equivalence schema, let's start by looking at some
    trivial program transformations involving [Skip]: *)

Theorem skip_left : forall c,
  com_equiv
    (Skip;; c)
    c.
Proof.
  intros.
  unfold com_equiv, Rel.equiv.
  intros st1 st2.
  rewrite ceval_CSeq, ceval_CSkip.
  split; intros.
  + unfold concat, id in H.
    destruct H as [st' [? ?]].
    rewrite H.
    exact H0.
  + unfold concat, id.
    exists st1.
    split.
    - reflexivity.
    - exact H.
Qed.

(** Also, we can prove that adding a [Skip] after a command results in an
equivalent program. *)

Theorem skip_right : forall c,
  com_equiv
    (c ;; Skip)
    c.
Proof.
(* WORKED IN CLASS *)
  intros.
  unfold com_equiv, Rel.equiv.
  intros st1 st2.
  rewrite ceval_CSeq, ceval_CSkip.
  split; intros.
  + simpl in H.
    unfold concat, id in H.
    destruct H as [st' [? ?]].
    rewrite <- H0.
    exact H.
  + simpl.
    unfold concat, id.
    exists st2.
    split.
    - exact H.
    - reflexivity.
Qed.

(** Now we show that we can swap the branches of an IF if we also negate its
guard. *)

Theorem swap_if_branches : forall b e1 e2,
  com_equiv
    (If b Then e1 Else e2 EndIf)
    (If (BNot b) Then e2 Else e1 EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ! ceval_CIf.
  unfold if_sem; simpl.
  rewrite union_comm.
  rewrite Sets_complement_complement.
  reflexivity.
Qed.

(** An interesting fact about [While] commands is that any number of copies of
the body can be "unrolled" without changing meaning. Loop unrolling is a common
transformation in real compilers. *)

Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
Abort.

(** This is not easy to prove. Let's isolate it. *)

Lemma loop_sem_unrolling: forall b (R: state -> state -> Prop),
  Rel.equiv (loop_sem b R) (if_sem b (concat R (loop_sem b R)) id).
Proof.
  intros.
  unfold Rel.equiv; intros st1 st2.
  unfold iff; split; intros.
  + unfold loop_sem, omega_union in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, union.
      right; simpl.
      unfold concat, id.
      exists st2; split; [exact H | reflexivity].
    - simpl in H.
      unfold if_sem, union.
      left.
      unfold concat in H.
      unfold concat.
      destruct H as [st1' [? [st1'' [? ?]]]].
      exists st1'; split; [exact H |].
      exists st1''; split; [exact H0 |].
      unfold loop_sem, omega_union.
      exists n.
      exact H1.
  + unfold if_sem, union in H.
    unfold loop_sem, omega_union.
    destruct H.
    2: {
      exists 0%nat.
      simpl.
      unfold concat, id in H.
      destruct H as [st2' [? ?]].
      rewrite H0 in H; exact H.
    }
    unfold concat at 1 in H.
    destruct H as [st1' [? ?]].
    unfold concat in H0.
    destruct H0 as [st0 [? ?]].
    unfold loop_sem, omega_union in H1.
    destruct H1 as [n ?].
    exists (S n).
    simpl.
    unfold concat at 1.
    exists st1'; split; [exact H |].
    unfold concat.
    exists st0; split; [exact H0 | exact H1].
Qed.

Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

(* ################################################################# *)
(** * Bourbaki-Witt Theorem *)

(** For now, we have successfully proved that [loop_sem] is a fixpoint
    constructor which satisfies the recursive equation [loop_sem_unrolling].
    Remember, [x] is a fixpoint of [f] when [x = f x]. Here, [loop_sem b R] is
    a solution of the following equation:

      - [ X = (if_sem b (concat R X) id) . ]

    Our proof is actually one special case of Bourbaki-Witt fixpoint theorem. *)

(* ================================================================= *)
(** ** Partial Order *)

(** A partial order (偏序) on a set [A] is a binary relation [R] (usually written
as [<=]) which is reflexive (自反), transitive (传递), and antisymmetric (反对称).
Formally,

    forall x: A, x <= x;
    forall x y z: A, x <= y -> y <= z -> x <= z;
    forall x y: A, x <= y -> y <= x -> x = y.

The least element of [A] w.r.t. a partial order [<=] is also called bottom:

    forall x: A, bot <= x
*)

(* ================================================================= *)
(** ** Chain *)

(** A subset of elements in [A] is called a chain  w.r.t. a partial order [<=]
if any two elements in this subset are comparable. For example, if a sequence
[xs: nat -> A] is monotonically increasing:

    forall n: nat, xs n <= xs (n + 1),

then it forms a chain.

A partial order [<=] is called _complete_ if every chain has its least upper
bound [lub] and greatest lower bound [glb]. In short, the set [A] (companied
with order [<=]) is called a complete partial ordering, CPO (完备偏序集). Some text
books require chains to be nonempty. We do not put such restriction on chain's 
definition here. Thus, the empty set is a chain. Its least upper bound is the
least element of [A], in other words, [bot]. *)

(* ================================================================= *)
(** ** Monotonic and Continuous Functions *)

(** Given two CPOs [A, <=A=] and [B, <=B=], a function [F: A -> B] is called
monotonic (单调) if it preserves order. Formally,

    forall x y: A, x <=A= y -> F(x) <=B= F(y).

A function [F: A -> B] is called continuous (连续) if it preserves [lub].
Formally,

    forall xs: chain(A), lub(F(xs)) = F(lub(xs))

Here, the [lub] function on the left hand side means the least upper bound
defined by [B] and the one on the right hand side is defined by [A].

The definition of continuous does not require the preservation of [glb] becasue
CPOs are usually defined in a direction that larger elements are _more
defined_ . *)

(* ================================================================= *)
(** ** Least fixpoint *)

(** Given a CPO [A], we can always construct a sequence of elements as follows:

    bot, F(bot), F(F(bot)), F(F(F(bot))), ...

Obviously, [bot <= F(bot)] is true due to the definition of [bot]. If [F] is
monotonic, it is immediately followed by [F(bot) <= F(F(bot))]. Similarly,

    F(F(bot)) <= F(F(F(bot))), F(F(F(bot))) <= F(F(F(F(bot)))) ...

In other words, if [F] is monotonic, this sequence is a chain.

Main theorem: given a CPO [A], if it has a least element, then every monotonic
continuous function [F] has a fixpoint and the least fixpoint of [F] is:

    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

Proof.

On one hand, this least upper bound is a fixpoint:

    F (lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...]) =
    lub [F(bot), F(F(bot)), F(F(F(bot))), F(F(F(F(bot)))), ...] =
    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

The first equality is true because [F] is continuous. The second equality is
true because [bot] is less than or equal to all other elements in the sequence.

On the other hand, this fixpoint is the least one. For any other fixpoint [x],
in other words, suppose [F(x) = x]. Then,

    bot <= x

Thus,

    F(bot) <= F(x) = x

due to the fact that [F] is monotonic and [x] is a fixpoint. And so on,

    F(F(bot)) <= x, F(F(F(bot))) <= x, F(F(F(F(bot)))) <= x, ...

That means, [x] is an upper bound of [bot, F(bot), F(F(bot)), ...]. It must be
greater than or equal to

    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

QED. *)

(* ================================================================= *)
(** ** Denotation of Loops as Bourbaki-Witt Fixpoint *)

(** Our definition [loop_sem] is actually a Bourbaki-Witt fixpoint of the
recursive equation defined by [loop_recur]. In this case, set [A] is the set of
binary relations between program stats, i.e. [A := state -> state -> Prop].

The equivalence relation defined on [A] is [com_dequiv]. The partial order
defined on [A] is the subset relation, i.e. [Rel.le]. This partial ordering is a
CPO. The least upper bound, [lub], of a chain is the union of all binary
relations in the chain. Specifically, [omega_union] defines the [lub] of a
sequence of relations.

In the end, the function that maps [X] to [ if_sem b (concat R X) id) ]
is monotonic and continuous. And [loop_sem] is exactly the Bourbaki-Witt
fixpoint of this function. *)





(* Tue Mar 31 13:28:59 CST 2020 *)
