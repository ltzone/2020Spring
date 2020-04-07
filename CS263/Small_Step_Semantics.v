(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1 and volume 2. *)

Require Import Coq.micromega.Psatz.
Require Import PL.Imp.
Require Import PL.ImpExt4.

(* ################################################################# *)
(** * General Idea: Small Step *)

(** Till now, we have learnt how to define a programming language's denotational
semantics. Most commonly, the denotation of a program is defined as a binary
relation between program states. Such denotational semantics are also called
big-step operational semantics -- the denotation of a program tells the result
of program execution (given the starting state), "all in one step".

Small step semantics, on the other hand, talks more about intermediate states.
It defines how a program will execute, step by step. If we use the following 
expression's evaluation process as example,

    2 + 2 + 3 * 4,

denotational semantics says:

    2 + 2 + 3 * 4 ==> 16

while small step operational semantics says:

      2 + 2 + 3 * 4
      --> 4 + 3 * 4
      --> 4 + 12
      --> 16.

In short, we will learn how to define a "small-step" relation that specifies,
for a given program, how the "atomic steps" of computation are performed. *)

(* ################################################################# *)
(** * Small Step Semantics for Expression Evaluation *)

(** It can be useful to think of this step relation of expression evaluation
as an _abstract machine_.

      - At any moment, the _state_ of the machine is an integer
        expression.

      - A _step_ of this machine is an atomic unit of computation --
        here, a single arithmetic operation or loading program variable's
        value.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done.

Given an expression [a], we can compute its value as follows:

      - Take [a] as the starting state of the machine.

      - Repeatedly use the step relation to find a sequence of
        machine states, starting with [a], where each state steps to
        the next.

      - When no more forward step is possible, "read out" the final
        state of the machine as the result of computation.

Intuitively, it is clear that the final states of the machine are always
constant expressions [Anum n] for some [n]. *)

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

(** Of course, we could define it using a Coq function instead of an inductive
predicate. Here is this alternative (but equivalent approach) approach. *)

Module Playground_Halt.

Definition aexp_halt (a: aexp): Prop :=
  match a with
  | ANum _ => True
  | _ => False
  end.

End Playground_Halt.

(** Then we define our step relation. *)

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

(** This definition seems to be super long. Let's read it part by part. But
please keep in mind that what we define here is only a single step evaluation
relation.

The first part of this definition talks about the value of a program variable:

      astep st
        (AId X) (ANum (st X)).

In short, it says: a program variable [X]'s variable is [X]'s variable and this
evaluation process has only one step.

The second part of this definition talks about how the sum of two
subexpressions are computed.

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

It says, the left side is computed first, then the right side. When both sides
are computed, the sum of them can be computed in another step.

In the theory of programming languages, such inductive definitions are also
inference rules. For example,



          -------------
           X  --> st X

           a1 --> a1'
    -----------------------
      a1 + a2 --> a1' + a2

           a2 --> a2'
    -----------------------
       n + a2 --> n + a2'

    -----------------------
      n1 + a2 --> n1 + n2
 ("+" of aexp)   ("+" of integers)

Usually, every inference rule has a horizontal line, what sits above it is
assumptions and the conclusion is below the line.

Combining all rules together, we are already able to describe the evaluation
process of some nontrivial examples. For example, when [X]'s value is 1 and
[Y]'s value is 2, [X + (3 + Y)] will be evaluated by the following steps:

    X + (3 + Y)
    --> 1 + (3 + Y)
    --> 1 + (3 + 2)
    --> 1 + 5
    --> 6.
*)

(** We can prove our examples in Coq. *)

Module Step_Example1.

Import Abstract_Pretty_Printing.

Example step_1: forall (X Y: var) (st: state),
  st X = 1 ->
  astep st (X + (3 + Y)) (1 + (3 +Y)).
Proof.
  intros.
  apply AS_Plus1.
  rewrite <- H.
  apply AS_Id.
Qed.

Example step_2: forall (Y: var) (st: state),
  st Y = 2 ->
  astep st (1 + (3 +Y)) (1 + (3 + 2)).
Proof.
  intros.
  apply AS_Plus2.
  { apply AH_num. }
  apply AS_Plus2.
  { apply AH_num. }
  rewrite <- H.
  apply AS_Id.
Qed.

Example step_3: forall (st: state),
  astep st (1 + (3 + 2)) (1 + 5).
Proof.
  intros.
  apply AS_Plus2.
  { apply AH_num. }
  apply AS_Plus.
Qed.

Example step_4: forall (st: state),
  astep st (1 + 5) 6.
Proof.
  intros.
  apply AS_Plus.
Qed.

End Step_Example1.

(** We define bool expressions' evaluation similarly. If you forget details
    about [bexp]'s inductive definition, just use [Print bexp] as a cheat
    sheet. *)

(* Print bexp. *)

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.

(** Remark: when evaluating a conjunction of two boolean expression, we use
    short circuit evaluation. That is, the right hand side will not be evaluated
    if the left hand side is false. For example, when [X]'s value is 1,
    [X <= 0 && 0 < X + 10] will be evaluated by the following steps:

    X <= 0 && 0 <= X + 10
    --> 1 <= 0 && 0 <= X + 10
    --> False && 0 <= X + 10
    --> False.
*)

Module Step_Example2.

Import Abstract_Pretty_Printing.

Example step_1: forall (X: var) (st: state),
  st X = 1 ->
  bstep st ((X <= 0) && (0 <= X + 10)) ((1 <= 0) && (0 <= X + 10)).
Proof.
  intros.
  apply BS_AndStep.
  apply BS_Le1.
  rewrite <- H.
  apply AS_Id.
Qed.

Example step_2: forall (X: var) (st: state),
  bstep st ((1 <= 0) && (0 <= X + 10)) (BFalse && (0 <= X + 10)).
Proof.
  intros.
  apply BS_AndStep.
  apply BS_Le_False.
  omega.
Qed.

Example step_3: forall (X: var) (st: state),
  bstep st (BFalse && (0 <= X + 10)) BFalse.
Proof.
  intros.
  apply BS_AndFalse.
Qed.

End Step_Example2.

(* ################################################################# *)
(** * Multi-step Relation *)

(** We can now use the single-step relations and their reflexive, transitive
    closure to formalize an entire _execution_. *)

Definition multi_astep (st: state): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: state): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

(** Intuitively, if [multi_astep st a1 a2] is true, then [a2] is an intermidiate
    result of evaluating [a1] on [st]. And [multi_bstep st b1 b2] says that [b2]
    is an intermidiate result of evaluating [b1] on [st]. Here is several
    examples.

    Remark. In these examples and our later lecture notes, we will reason about
    different properties about reflexive transitive closures. Our [Imp] library
    provide tactic supports for these proofs. These tactics include:
    
    - [induction_1n] and [induction_n1];
    
    - [transitivity_1n], [transitivity_n1], [etransitivity_1n] and
      [etransitivity_n1];

    - [unfold_with_1n] and [unfold_with_n1].

    Also, since reflexive transitive closures are reflexive and transitive,
    [Imp] libraries provide corresponding instances so that Coq's [reflexivity],
    [transitivity] and [etransitivity] can be used. You can find more detailed
    information in the additional reading part. *)

Module Example1.

Import Abstract_Pretty_Printing.

Example multi_step_ex1: forall (Y: var) (st: state),
  st Y = 2 ->
  multi_astep st (1 + (3 + Y)) (1 + 5).
  (* multi_astep st
       (APlus (ANum 1) (APlus (ANum 3) (AId Y)))
       (APlus (ANum 1) (ANum 5)) *)
Proof.
  intros.
  etransitivity_1n.
  {
    apply AS_Plus2.
    { apply AH_num. }
    apply AS_Plus2.
    { apply AH_num. }
    apply AS_Id.
  }
  (* multi_astep st
         (APlus (ANum 1) (APlus (ANum 3) (ANum (st Y))))
         (APlus (ANum 1) (ANum 5)) *)
  etransitivity_1n.
  { rewrite H.
    apply AS_Plus2.
    { apply AH_num. }
    apply AS_Plus.
  }
  reflexivity.
Qed.

Example multi_step_ex2: forall (X: var) (st: state),
  st X = 1 ->
  multi_bstep st ((X <= 0) && (0 <= X + 10)) BFalse.
Proof.
  intros.
  etransitivity_1n.
  { apply BS_AndStep. apply BS_Le1. apply AS_Id. }
  rewrite H.
  etransitivity_1n.
  { apply BS_AndStep. apply BS_Le_False. lia. }
  etransitivity_1n.
  { apply BS_AndFalse. }
  reflexivity.
Qed.

Example multi_step_ex3: forall (X: var) (st: state),
  st X = 1 ->
  multi_bstep st ((X <= 0) && (0 <= X + 10)) ((X <= 0) && (0 <= X + 10)).
Proof.
  intros.
  reflexivity.
Qed.

End Example1.

(** The multi-step relations satisfy the congruence property. For example, the
    following theorem says:

              a1 -->* a1'
        ----------------------
         a1 + a2 -->* a1' + a2

    Why? Because for every single step from [a1] to [a1'], we can construct
    a corresponding step from [a1 + a2] to [a1' + a2].

    a1   -->  b   -->  c   -->  d   -->   a1'

   a1+a2 --> b+a2 --> c+a2 --> d+a2 --> a1'+a2
*)

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

(** Remark: we could complete this proof using different induction principles
    like the style of [trans], of [trans_1n] instead of [trans_n1]. *)

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
Proof.
(** It is critical that we require [a1] to be a constant. *)
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus2.
      (** Here we go. Without the assumption [H: aexp_halt a1], we cannot
      complete our proof here. *)
      * exact H.
      * exact H0.
Qed.

(** We can prove similar properties for [AMinus], [AMult], [BEq], [BLe], [BNot]
and [BAnd]. *)

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus1.
      exact H.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult1.
      exact H.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult2.
      * exact H.
      * exact H0.
Qed.

(* ################################################################# *)
(** * Small Step Semantics for Simple Imperative Programes *)

(** The semantics of commands is more interesting. For expression evaluation,
the program states are stable. In other words, we only talked about how an
expression will be reduced to another one on a _fixed_ program state. But for
program execution, the program states are modified. Thus, a ternary relation
among the program state, the command to execute and the residue command after
one step is not expressive enough to describe programs' behavior. A quaternary
relation is needed.

Specifically, we would like to define a predicate [cstep] such that

    cstep st1 c1 st2 c2

says if the program to execute is [c1], the taking one step forward on state
[st1] may end in state [st2] while the residue command is [c2].

Traditionally, computer scientist will describe their theory in a slightly
different form. They usually treat [cstep] as a binary relation between
state-command pairs and use the following notation:

    (st1, c1) --> (st2, c2).

We will follow this style in our course, i.e. we will write

    cstep (st1, c1) (st2, c2).

Technically, this is also more convenient for us to define its reflexive
transitive closure later.
*)

(* ================================================================= *)
(** ** Definition of Program Steps *)

(** Here is our definition of small step semantics for program execution. In
    this definition, we use [(com * state)] in Coq to represent the set of
    command-program pairs. You can find more information about this Coq data
    type in the additional reading part. *)

Import Abstract_Pretty_Printing.

Local Open Scope imp.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

(** In this definition, we use two small tricks:

       - We use [Skip] as an "empty residue command".

            - An assignment command reduces to [Skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [Skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [While] command by transforming it into a
         conditional followed by the same [While].

For example,

        X ::= 1;; Y ::= 2, st1
          (* in which st1(Z) = 0 for all program variables Z *)
    --> Skip;; Y ::= 2, st2
          (* in which st2(X) = 1 and
                      st2(Z) = 0 for all other program variables Z *)
    --> Y ::= 2, st2
    --> Skip, st3
          (* in which st3(X) = 1 and
                      st3(Y) = 2 and
                      st3(Z) = 0 for all other program variables Z *)

Here is another example,

        While (0 <= X) Do X ::= X - 1 EndWhile, st1
          (* in which st1(Z) = 0 for all program variables Z *)
    --> If (0 <= X)
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st1
    --> If (0 <= 0)
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st1
    --> If BTrue
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st1
    --> X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile, st1
    --> X ::= 0 - 1;; While (0 <= X) Do X ::= X - 1 EndWhile, st1
    --> X ::= -1;; While (0 <= X) Do X ::= X - 1 EndWhile, st1
    --> Skip;; While (0 <= X) Do X ::= X - 1 EndWhile, st2
          (* in which st2(X) = -1 and
                      st2(Z) = 0 for all program variables Z *)
    --> While (0 <= X) Do X ::= X - 1 EndWhile, st2
    --> If (0 <= X)
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st2
    --> If (0 <= -1)
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st2
    --> If BFalse
        Then X ::= X - 1;; While (0 <= X) Do X ::= X - 1 EndWhile
        Else Skip
        EndIf, st2
    --> Skip, st2
*)

(* ================================================================= *)
(** ** Multi-step Relation *)

(** Similar to the small step semantics for expression evaluation, the
    multi-step relation for [cstep] also has its own congruence property. We
    prove two typical ones here. *)

Definition multi_cstep: com * state -> com * state -> Prop :=
  clos_refl_trans cstep.

Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (c1 ;; c2, st1) (c1';; c2, st1').
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply CS_SeqStep.
      exact H.
Qed.

Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (If b Then c1 Else c2 EndIf, st)
    (If b' Then c1 Else c2 EndIf, st).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_IfStep.
      exact H.
Qed.

(* ################################################################# *)
(** * Additional Reading: Pairs as Coq Data Type *)

Module Playground_Pair.

(** In Coq, product types are defined as the follow polymorphic inductive type.
This declaration can be read: "There is just one way to construct an A-B pair:
by applying the constructor [pair] to two arguments of type [A] and [B]." *)

Inductive prod (A B : Type) : Type :=
| pair (a : A) (b : B).

Arguments pair {A} {B} _ _.

Notation "( a , b )" := (pair a b).

Notation "A * B" := (prod A B) : type_scope.

Check (pair 3 5).

(** Here are simple functions for extracting the first and second components of a pair. *)

Definition fst {A B: Type} (p : A * B) : A :=
  match p with
  | pair x y => x
  end.

Definition snd {A B: Type} (p : A * B) : B :=
  match p with
  | pair x y => y
  end.

Example fst_example:
  fst (3, 5) = 3.
Proof. reflexivity. Qed.

(** Note that the pair notation can also be used in pattern matching. *)

Definition swap_pair {A B: Type} (p : A * B): B * A :=
  match p with
  | (x,y) => (y,x)
  end.

(** Let's try to prove a few simple facts about pairs. If we state things in a
slightly peculiar way, we can complete proofs with just reflexivity (and its
built-in simplification): *)

Theorem surjective_pairing' : forall (n m : Z),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. intros. reflexivity.  Qed.

(** Here, we can see the effect of [simpl]. *)
Theorem surjective_pairing'_alter : forall (n m : Z),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. intros. simpl. reflexivity.  Qed.

(** But [reflexivity] is not enough if we state the lemma in a more natural
way: *)

Theorem surjective_pairing_stuck : forall (p : Z * Z),
  p = (fst p, snd p).
Proof.
  intros.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** We have to expose the structure of [p] so that [simpl] can perform
the pattern match in [fst] and [snd].  We can do this with [destruct]. *)

Theorem surjective_pairing : forall (p : Z * Z),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall {A B: Type} (p : A * B),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall {A B: Type} (p : A * B),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Playground_Pair.

(** These definitions about pairs are all built in Coq's standard library. *)

Print prod.
  (* Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B *)

Check fst.
  (* fst : ?A * ?B -> ?A *)

Check fst.
  (* snd : ?A * ?B -> ?B *)

(* ################################################################# *)
(** * Additional Reading: Imp Support For Reflexive Transitive Closure *)

(** We already know that three different definitions of reflexive transitive
    closures are equivalent. If we define a multi-step relation using 
    [clos_refl_trans] but want to prove related properties via an equivalent
    transformation to [clos_refl_trans_1n], we can use [unfold_with_1n].
    Here is an example: *)

Example multi_congr_APlus1_demo1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  unfold_with_1n multi_astep.
  intros.
  induction H.
  + apply rt1n_refl.
  + eapply rt1n_trans_1n.
    - apply AS_Plus1.
      exact H.
    - apply IHclos_refl_trans_1n.
Qed.

(** We provide similar support for [clos_refl_trans_n1]. *)

Example multi_congr_APlus1_demo2: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  unfold_with_n1 multi_astep.
  intros.
  induction H.
  + apply rtn1_refl.
  + eapply rtn1_trans_n1.
    - apply AS_Plus1.
      exact H.
    - apply IHclos_refl_trans_n1.
Qed.

(** If you just want to do [clos_refl_trans_1n]'s induction principle, you can
    use [induction_1n]. *)

Example multi_congr_APlus1_demo3: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_1n H.
  +
Abort.

(** We know that [multi_astep] must be reflexive since it is defined by a
    reflexive transitive closure. We can use [reflexivity] here. *)

Example multi_congr_APlus1_demo3: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_1n H.
  + reflexivity.
  + etransitivity_1n.
    2: { apply IHrt. }
    econstructor. exact H.
Abort.

(** Here, if we directly use transitivity via intemidiate state [a1 + a2], we
    have to prove in Coq that

    - multi_astep st (a0 + a2) (a1 + a2)

    - multi_astep st (a1 + a2) (a1' + a2)

    Then, for the first target, we will use [rt_step] to complete the proof. It
    is inconvenient. Using a transitivity of [rt_trans_1n]'s style is better.
    [Imp] library provides [transitivity_1n]. *)

Example multi_congr_APlus1_demo3: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_1n H.
  + reflexivity.
  + transitivity_1n (a1 + a2)%imp.
    - apply AS_Plus1.
      exact H.
    - apply IHrt.
Qed.

(** If you do not want to manually provide an intermediate state, you can use
    [etransitivity_1n]. *)

Example multi_congr_APlus1_demo4: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_1n H.
  + reflexivity.
  + etransitivity_1n.
    - apply AS_Plus1.
      exact H.
    - apply IHrt.
Qed.

(** [Imp] provides similar supports via [induction_n1], [transitivity_n1] and
    [etransitivity_n1]. *)

Example multi_congr_APlus1_demo5: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + transitivity_n1 (a1' + a2)%imp.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

Example multi_congr_APlus1_demo6: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

(** In the end, we discuss a technique issue of doing manual induction in Coq.
    We will use [multi_congr_CSeq] as an example here. *)

Theorem multi_congr_CSeq_again: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (c1 ;; c2, st1) (c1';; c2, st1').
Proof.
  (** This time, we will use [unfold_with_n1] and try to use the induction
      principle of [clos_refl_trans_n1] manually to complete the proof. *)
  unfold_with_n1 multi_cstep.
  intros.
  induction H.
  + (** Oops, Coq does not generate a proof goal as we expected. *)
Abort.

(** The problem here is, Coq's induction tactic on inductive predicates
requires that predicate takes only Coq variables as its argument. Any other
internal structures are not allowed, or else necessary information might be
lost. In the case above, we do induction over:

    H: clos_refl_trans_n1 cstep (c1, st1) (c1', st1')

In this hypothesis, [(c1, st1)] and [(c1', st1')] are not simple Coq variables.
Thus, Coq cannot find a common pattern between big proof trees and small proof
trees, which causes problems in manual induction. Coq provides the [remember]
tactic for necessary transitions. *)

Theorem multi_congr_CSeq_again: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (c1 ;; c2, st1) (c1';; c2, st1').
Proof.
  unfold_with_n1 multi_cstep.
  intros.
  remember (c1, st1) as cst eqn:H0.
  remember (c1', st1') as cst' eqn:H1.
  (** These two commands say: use [cst] and [cst'] to represent those two
  pairs. And use two equalities [H0] and [H1] to record this replacement. *)
  revert c1 st1 c1' st1' H0 H1; induction H.
  + intros.
    (** This branch corresponds to the case that
    [[
        multi_cstep (c1, st1) (c1', st1')
    ]]
    is true because of reflexivity.
    The [subst] will find [H0: x = (c1, st1)] and replace every occurrence of
    [x] with [(c1, st1)]. *)
    subst.
    (** Now, [H1] says
    [[
         pair c1 st1 = pair c1' st1'
    ]]
    and [pair] is a constructor for product type. Since all constructors are
    injective, we can achieve [c1 = c1'] and [st1 = st1']. *)
    injection H1 as ?H ?H.
    subst.
    apply rtn1_refl.
  + intros.
    (** This branch corresponds to the case that
    [[
        multi_cstep (c1, st1) (c1', st1')
    ]]
    is true because there exists another pair [c1'', st''], such that
    [[
        multi_cstep (c1, st1) (c1'', st1'')
        cstep (c1'', st1'') (c1', st1')
    ]]
    holds.
    *)
    subst.
    destruct y as [c1'' st1''].
    eapply rtn1_trans_n1.
    - apply CS_SeqStep.
      exact H.
    - apply IHclos_refl_trans_n1.
      * reflexivity.
      * reflexivity.
Qed.

(** Of course, manually work-around of using [remember], [revert], [subst] and
    [injection] is inconvenient. [Imp]'s [induction_n1] does that for you. *)

(* Tue Apr 7 03:46:01 CST 2020 *)
