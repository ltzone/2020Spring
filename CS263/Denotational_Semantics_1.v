(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1. *)

Require Import Coq.micromega.Psatz.
Require Import PL.Imp.

(* ################################################################# *)
(** * Expression Evaluation *)

(** We have seen how a Hoare logic (axiomatic semantics) defines the relation
between the possible programs state sets before and after executing a program.
It is convenient for describing useful program specifications and verifying
them. However, it is not obvious how this semantic definition connects with
compiler implementation.

Denotational semantics (指称语义) is another style of semantic definition. It
directly defines program behavior on concrete program state, but as a
trade-off, it does not directly connect with useful program specifications. *)

(** Today we will use integer expression evaluation (整数表达式求值) to
illustrate the difference. Remember that the integer expressions of our simple
imperative language have the following grammar:

    a ::= Z
        | var
        | a + a
        | a - a
        | a * a

In Hoare logic, we talk about the property that an expressions [a]'s value
should satisfy. In denotational semantics, we directly define expressions'
evaluation result.

The following definition says, for a fixed program state [st], the value of
expression [a] is defined recursively on its syntax tree.
*)

Import Abstract_Pretty_Printing.

Module AEval_first_try.

Section AEval.

Variable st: state.
  
Fixpoint aeval (a : aexp) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

End AEval.

(** Here
- The keyword [Fixpoint] means that we defines a _recursive_ (递归) function.
- The function [aeval] defines the evaluation result of integer expressions in
  our simple imperative programming language.
- The argument announcement [st: state] says that [st] is a program state.
  Here, a program state is defined as a function from program variables to
  integers.
- The argument announcement [a: aexp] says that [a] is an integer expression.
  We follow <<Software Foundation>>'s tradition to call integer expressions
  [aexp].
- The [match] expression (Coq expression) defines how this expression (program
  expression) evaluation is defined for different kind of [a].
- [ANum n] says if [a] is a constant expression [n].
- [AId X] says if [a] is a singleton variable [X].
- [st X] says: applying function [st] on [X]. Remember, [st] is a function from
  program variables to integers.

We can use similar approaches to define the length of an integer expression.
*)

Example aeval_example1: forall (st: state) (X Y: var),
  st X = 1 ->
  st Y = 2 ->
  aeval st (X + Y) = 3.
Proof.
  intros.
  simpl.
  (** Here, the tactic [simpl] simplifies [aeval st (X + Y)] using the [aeval]'s
      definition. *)
  rewrite H, H0.
  reflexivity.
Qed.

Example aeval_example2: forall (st: state) (X Y: var),
  st X = 1 ->
  st Y = 2 ->
  aeval st (X * Y + 1) = 3.
Proof.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Example aeval_example3: forall (st: state) (X Y Z: var),
  st X = 1 ->
  st Y = 2 ->
  st Z = 4 ->
  aeval st ((X - 1) * X * X * (X + Y - Z) * Y * Y * (Y + 1)) = 0.
Proof.
  intros.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Expression Equivalence *)

(** Based on [aeval] we can define a semantic equivalence between expressions.
    That is, two expressions [a1] and [a2] are equivalent if their evaluation
    results are always the same. *)

Definition aexp_equiv (a1 a2: aexp): Prop :=
  forall st, aeval st a1 = aeval st a2.

Declare Scope DSem.
Local Open Scope DSem.

Notation "a1 '=a=' a2" :=
  (aexp_equiv (a1:aexp) (a2:aexp)) (at level 69, no associativity): DSem.

Example aexp_equiv_sample: forall (X: var),
  X + X =a= X * 2.
Proof.
  intros.
  unfold aexp_equiv.
  (** The tactic [unfold] will unfold a definition. *)
  intros.
  simpl.
  lia.
Qed.

Lemma zero_plus_equiv: forall (a: aexp),
  0 + a =a= a.
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: aexp),
  a + 0 =a= a.
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: aexp),
  a - 0 =a= a.
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: aexp),
  0 * a =a= 0.
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: aexp),
  a * 0 =a= 0.
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  ANum n + ANum m =a= ANum (n + m).
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  reflexivity.
Qed.
  
Lemma const_minus_const: forall n m: Z,
  ANum n - ANum m =a= ANum (n - m).
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  reflexivity.
Qed.
  
Lemma const_mult_const: forall n m: Z,
  ANum n * ANum m =a= ANum (n * m).
Proof.
  intros.
  unfold aexp_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

End AEval_first_try.

(* ################################################################# *)
(** * Inductive types and recursive functions *)

(** From now on, when we analyze an expression or a program, we will repeatedly
    define new concepts (like [aeval], integer expression evaluation) by
    recursion on syntax trees. Thus it is worthing spending more time to
    understand recursions better. We will use binary trees as examples here. *)

Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.

(** This definition says: a tree is either an empty tree or a tree with left
    subtree [l], root node (whose value is [v]) and right subtree [r]. We can
    define tree heights and tree sizes recursively. *)

Fixpoint tree_height (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => Z.max (tree_height l) (tree_height r) + 1
  end.

Fixpoint tree_size (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => tree_size l + tree_size r + 1
  end.

(** We can even define trees from trees. The following definition turns a tree
    left-right reversed. *)

Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.

(** For example, if [t] is the left tree, then [tree_reverse t] is the right
    tree:

         5                5
        / \              / \
       3   9            9   3
          / \          / \
         8  100      100  8
*)

Example tree_reverse_example:
  tree_reverse
    (Node (Node Leaf 3 Leaf) 5 (Node (Node Leaf 8 Leaf) 9 (Node Leaf 100 Leaf)))
  =
  Node (Node (Node Leaf 100 Leaf) 9 (Node Leaf 8 Leaf)) 5  (Node Leaf 3 Leaf).
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Structure Induction *)

(** Coq manages not only formal definitions but also formal proofs. Here, we
    will try proving some basic properties about [tree_height], [tree_size] and
    [tree_reverse]. The main proof technology is _induction_ (归纳法). *)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  intros.
  induction t.
  + (* base step *)
    simpl.
    lia.
  + (* induction step *)
    simpl.
    (** Here, we see two assumptions in the proof goal, [IHt1] and [IHt2]. The
        English abbreviation [IH] stands for _induction hypothesis_ (归纳假设).
        In this case, [IHt1] and [IHt2] are induction hypothese of left subtree
        [t1] and right subtree [t2]. *)
    lia.
Qed.

Lemma height_le_size: forall t,
  tree_height t <= tree_size t.
Proof.
  intros.
  induction t; simpl.
  (** The tactic language in Coq provide semicolon [;]. Specifically,
    [tac1 ; tac2] says do [tac1], then do [tac2] in every single proof goal
    that [tac1] generates. Semicolon is right associative. *)
  + lia.
  + pose proof size_nonneg t1.
    pose proof size_nonneg t2.
    lia.
    (** Note that [lia] can also reason about [Z.max] and [Z.min]. *)
Qed.

(** We can also define properties recursively. *)

Fixpoint tree_ele_le (ub: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_ele_le ub l /\ k <= ub /\ tree_ele_le ub r
  end.

Fixpoint tree_ele_ge (lb: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_ele_ge lb l /\ k >= lb /\ tree_ele_ge lb r
  end.

Declare Scope tree_scope.
Local Open Scope tree_scope.
Notation "t <== n" := (tree_ele_le n t) (at level 49, no associativity): tree_scope.
Notation "t >== n" := (tree_ele_ge n t) (at level 49, no associativity): tree_scope.

(** Here, [tree_ele_le n t] says every element in [t] is less than or equal to
    [n]. Similarly, [tree_ele_ge n t] says every element in [t] is greater than
    or equal to [n]. For Coq's notations, you do not need to fully understand
    them.

    Coq even allows us to write other recursive definitions based on [<==] and
    [>==]. *)

Fixpoint low2high (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => low2high l /\ l <== k /\ r >== k /\ low2high r
  end.

Fixpoint high2low (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => high2low l /\ l >== k /\ r <== k /\ high2low r
  end.

(** ... and to prove interesting properties about them. *)

Lemma reverse_low2high: forall t,
  low2high t ->
  high2low (tree_reverse t).
Proof.
  intros.
  induction t.
  + simpl.
    exact I.
  + simpl in H.
    (** We can do [simpl] in assumptions as we do in conclusions. *)
    simpl.
    (** It seems that we need some properties about [<==] and [>==] for help
        here. Let's prove them as separate lemmas. *)
Abort.

Lemma reverse_le: forall n t,
  t <== n ->
  tree_reverse t <== n.
Proof.
  intros.
  induction t; simpl.
  + exact I.
  + simpl in H.
    destruct H as [Ht1 [? Ht2]].
    split; [| split].
    (** Here, [ tac; [ tac1 | tac2 | ... | tacn] ] means running [tac] first
        which should generate [n] subgoals, and then executing [tac1], [tac2],
        ..., [tacn] on each of them respectively.
        Moreover, sometimes there may be too many subgoals. You can write
        tactics like [ tac; [ tac1 | tac2 | tac3 .. ] ]. It means running [tac]
        first, and then executing [tac1] and [tac2] one the first and the second
        subgoal, but doing [tac3] on all rest subgoals. *)
    (* WORKED IN CLASS *)
    - apply IHt2.
      exact Ht2.
    - exact H.
    - apply IHt1.
      exact Ht1.
Qed.

Lemma reverse_ge: forall n t,
  t >== n ->
  tree_reverse t >== n.
Proof.
  intros.
  induction t; simpl.
  + exact I.
  + simpl in H.
    tauto.
    (** This tactic [tauto] is a solver for propositional connectives, i.e.
        [/\], [\/], [~], [->], [True] and [False]. *)
Qed.    

Lemma reverse_low2high: forall t,
  low2high t ->
  high2low (tree_reverse t).
Proof.
(* WORKED IN CLASS *)
  intros.
  induction t; simpl.
  + exact I.
  + simpl in H.
    pose proof reverse_le v t1.
    pose proof reverse_ge v t2.
    tauto.
Qed.

Lemma reverse_involutive: forall t,
  tree_reverse (tree_reverse t) = t.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction t; simpl.
  + reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
Qed.

(* ################################################################# *)
(** * Case analysis *)

(** The following property seems stupid. But how can we prove it? *)

Lemma reverse_result_Leaf: forall t,
  tree_reverse t = Leaf ->
  t = Leaf.
Proof.
  intros.
  (** The follow [destruct] command enables us to do case analysis. Is [t] an
      empty tree? *)
  destruct t.
  (** If yes, the conclusion is already proved. *)
  + reflexivity.
  (** If no, the assumption is impossible to be true. *)
  + simpl in H.
    (** That is, if [t] is nonempty, then [tree_reverse t] is also nonempty.
        A equation like [H] cannot hold since its left hand side and right hand
        side are categorically different. The tactic [discriminate] can discover
        such contradictions. *)
    discriminate H.
Qed.

(** The following property is comparatively nontrivial. *)

Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros.
  (** In the following line, we explicitly give names to those case analysis
      results. After case analysis, the empty-tree situation is obviously a
      contradiction. *)
  destruct t as [| t1' v t2']; simpl in H.
  + discriminate H.
  (** The nonempty situation is more interesting. The hypothesis [H] says:

      -  [ Node (tree_reverse t2') v (tree_reverse t1') = Node t1 k t2. ]

      We should be able to derive the following facts from it:

      - tree_reverse t2' = t1

      - tree_reverse t1' = t2

      Coq provide the [injection] tactic for us to complete the proof.
  *)
  + injection H as ? ? ?.
    rewrite <- H, <- H0, <- H1.
    (** The symbol "!" here means to rewrite as many times as possible. *)
    rewrite ! reverse_involutive.
    reflexivity.
Qed.

(* ################################################################# *)
(** * Strengthing an Induction Hypothesis *)

(** In the end, let's define a property of tree pairs and reason about it. *)

Fixpoint same_structure (t1 t2: tree): Prop :=
  match t1, t2 with
  | Leaf, Leaf => True
  | Leaf, Node _ _ _ => False
  | Node _ _ _, Leaf => False
  | Node l1 _ r1, Node l2 _ r2 => same_structure l1 l2 /\ same_structure r1 r2
  end.

(** In this definition, we see that we are allowed to do pattern match over two
    items simultaneously. *)

Lemma same_structure_same_height: forall t1 t2,
  same_structure t1 t2 ->
  tree_height t1 = tree_height t2.
Proof.
  intros.
  (** A natural idea here is to prove the theorem by structural induction over
      [t1]. Then the induction hypothesis should tell us: [t1]'s left/right
      subtree has the same height with [t2]'s left/right subtree.*)
  induction t1.
  (** For base step, we can do case analysis over [t2]; [t2] must be empty
      according to [H]. *)
  + destruct t2.
    - reflexivity.
    - simpl in H.
      contradiction.
  +
Abort.

(** Oops! This is not what we expected! The induction hypothese should be about
    [t2]'s subtrees not [t2] itself. But why this will happen in Coq? The
    problem is that, at the point our proof script call [induction], we have
    already introduced [t2] into the context — intuitively, we have told Coq,
    "Let's consider some particular t2...". The tactic [induction t1] says: we
    are going to show the goal by induction on [t1]. That is, we are going to
    prove, for all [t1], that the proposition [tree_height t1 = tree_height t2]
    is true on that particular [t2]. In such situations, we should strength our
    induction hypothesis. *)

Lemma same_structure_same_height: forall t1 t2,
  same_structure t1 t2 ->
  tree_height t1 = tree_height t2.
Proof.
  intros.
  (** Remember that [revert] is the reverse tactic of [intros]. *)
  revert t2 H.
  induction t1 as [| l1 IHl v1 r1 IHr]; intros.
  (** The base step should be similar. *)
  + destruct t2.
    - reflexivity.
    - simpl in H.
      contradiction.
  (** The induction hypothese are different now! *)    
  + destruct t2 as [| l2 v2 r2]; simpl in H.
    { contradiction. }
    destruct H.
    (** Now, we can get IH about [t2]'s subtrees. *)
    apply IHl in H.
    apply IHr in H0.
    simpl.
    lia.
Qed.

(* ################################################################# *)
(** * Analyzing Syntax Trees *)

Module AEval_lemmas.

Import AEval_first_try.
Local Open Scope DSem.

(** Now, we are already quite familiar with recursion and structural induction.
    We will use them repeatedly when building the theory of denotational
    semantics. Let's start with a very simple definition and a very simple
    proof. *)

Fixpoint alength (a : aexp) : Z :=
  match a with
  | ANum n => 1
  | AId X => 1
  | APlus a1 a2 => (alength a1) + (alength a2) + 1
  | AMinus a1 a2  => (alength a1) + (alength a2) + 1
  | AMult a1 a2 => (alength a1) + (alength a2) + 1
  end.

Lemma alength_pos: forall a,
  alength a > 0.
Proof.
  intros.
  induction a; simpl; lia.
Qed.

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is constant when it contains no variable references. Constant
folding is an optimization that finds constant expressions and replaces them by
their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | APlus a1 a2  =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 + n2)
    | _, _ => APlus (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  | AMinus a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 - n2)
    | _, _ => AMinus (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  | AMult a1 a2  =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 * n2)
    | _, _ => AMult (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  end.

(** Here, we see that the [match] expressions in Coq are very flexible. (1) We
can apply pattern matching on not only Coq variables but also any Coq expression
whose type is inductively defined. (2) We can apply pattern matching on two
expressions at the same time. (3) We can use underscore [_] to cover default
cases. *)

Module fold_const_example.

Example ex1 : forall (X: var),
    fold_constants_aexp ((1 + 2) * X) 
  = (3 * X)%imp.
Proof. intros. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate trivial
additions, etc. -- we are focusing attention on a single optimization for the
sake of simplicity.  It is not hard to incorporate other ways of simplifying
expressions; the definitions and proofs just get longer. *)

Example fold_aexp_ex2 : forall (X: var) (Y: var),
  fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
Proof. intros. reflexivity. Qed.

End fold_const_example.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

Theorem fold_constants_aexp_sound : forall a,
  fold_constants_aexp a =a= a.
Proof.
  unfold aexp_equiv. intros.
  induction a.
  + (* ANum case *)
    simpl.
    reflexivity.
  + (* AId case *)
    simpl.
    reflexivity.
  + (* APlus case *)
    simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  + (* AMinus case *)
    simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  + (* AMult case *)
    simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
Qed.

(** After proving this soundness property, we want to prove that this
optimization really improves something. *)

Arguments Z.add: simpl never.

Lemma fold_constants_aexp_improve : forall a,
  alength (fold_constants_aexp a) <= alength a.
Proof.
  intros.
  induction a.
  + simpl.
    lia.
  + simpl.
    lia.
  + simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    simpl in IHa1;
    simpl in IHa2;
    simpl;
    lia.
  + simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    simpl in IHa1;
    simpl in IHa2;
    simpl;
    lia.
  + simpl.
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
    simpl in IHa1;
    simpl in IHa2;
    simpl;
    lia.
Qed.

(* ================================================================= *)
(** ** 32-bit Evaluation *)

Definition max32: Z := 2^31 -1.
Definition min32: Z := - 2^31.

Fixpoint signed32_eval (st: state) (a: aexp): Prop :=
  min32 <= aeval st a <= max32 /\
  match a with
  | ANum n => True
  | AId X => True
  | APlus a1 a2 => signed32_eval st a1 /\ signed32_eval st a2
  | AMinus a1 a2  => signed32_eval st a1 /\ signed32_eval st a2
  | AMult a1 a2 => signed32_eval st a1 /\ signed32_eval st a2
  end.

(** In short, [signed32_eval a st] says that evaluating [a] on state [st] is
    within the range of signed 32-bit integers (including all intermediate
    results). Now, we will show that constant-folding does not only preserve
    evaluation result but also keep evaluation process within 32-bit range. *)

Lemma fold_constants_aexp_signed32: forall st a,
  signed32_eval st a ->
  signed32_eval st (fold_constants_aexp a).
Proof.
  intros.
  induction a; simpl in H; simpl.
  + exact H.
  + exact H.
  + destruct H as [? [? ?]].
    assert (signed32_eval st (fold_constants_aexp a1 + fold_constants_aexp a2)).
    {
      simpl.
      rewrite ! fold_constants_aexp_sound.
      tauto.
    }
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
      [ simpl in *; lia | exact H2 ..].
  + destruct H as [? [? ?]].
    assert (signed32_eval st (fold_constants_aexp a1 - fold_constants_aexp a2)).
    {
      simpl.
      rewrite ! fold_constants_aexp_sound.
      tauto.
    }
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
      [ simpl in *; lia | exact H2 ..].
  + destruct H as [? [? ?]].
    assert (signed32_eval st (fold_constants_aexp a1 * fold_constants_aexp a2)).
    {
      simpl.
      rewrite ! fold_constants_aexp_sound.
      tauto.
    }
    destruct (fold_constants_aexp a1), (fold_constants_aexp a2);
      [ simpl in *; lia | exact H2 ..].
Qed.

End AEval_lemmas.

(* ################################################################# *)
(** * Additional Reading *)

(** In this lecture, we introduce structural recursion and induction, and use
    them to build theories about expression evaluation. For more information
    about recursion, induction and related Coq tactics, you can read the
    following chapters in <<Software Foundations>> Volume 1:

    - Basics
    
    - Induction

    - Lists

    - Tactics. *)


(* Mon Mar 23 23:04:46 CST 2020 *)
