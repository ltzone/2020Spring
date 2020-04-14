Require Import PL.Imp2.

(* ################################################################# *)
(** * Review: Hoare Logic *)

Module HoareLogic.

(** In the first couple of lectures of this course, we learnt using Hoare
logic to prove program correctness. Here is the set of Hoare logic proof
rules.*)

Import Concrete_Pretty_Printing.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} = {[ E [X |-> x] ]} }}.

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

End HoareLogic.

(** This time, we are going to study the meta properties of the logic ranther
than only use it. For example, we wonder whether the program behavior defined
by Hoare logic is the same as the one defined by denotational semantics.
Here is a formalization of syntactic definitions related to Hoare logic. You
may compare this version with the one in the [Imp] library; they are only a
little bit different. *)

Import Abstract_Pretty_Printing.

(* ================================================================= *)
(** ** Assertion Language *)

(** Logical variables are used together with universal quantifiers and
existential quantifiers. In order to formalize the assertions language, we use
logical variables' identifiers to distinguish them, i.e. we just call then the
0th logical variable, 1st logical variable, 2nd logical variable etc. *)

Definition logical_var: Type := nat.

(** Logical variables may appear in program expressions to represent a special
constant. For example, in the forward assignment rule, the postcondition is

    EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]}.

In this assertion [X |-> x] describes the action of replacing [X] with constant
expression [x]. One possible definition of _variable expressions'_ (可变表达式) syntax tree is as follows. *)

Module Variable_Expression_Attempt.

Inductive aexp' : Type :=
  | ANum' (n : Z)
  | AId' (X : var)
  | ALid (x: logical_var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp').

End Variable_Expression_Attempt.

(** In reality, we need more expressiveness. For example, in order to prove

    {[Y]} = {[X]} * 2 + 1 |-- EXISTS z, {[(Y + 1) - 2 * z]} = 0

we would like to prove result of instantiating the existentially quantified
variable [z] with [ {[X]} + 1 ]. Specifically, the derivation above immediately
follows the statement below:

    {[Y]} = {[X]} * 2 + 1 |-- {[(Y + 1) - 2 * ({[X]} + 1) ]} = 0.

In this statement, [(Y + 1) - 2 * ({[X]} + 1)] represents the following syntax tree:

       -
     /   \
    /     \
   +       *
  / \     / \
 /   \   /   \
Y    1   2 {[X]} + 1

in which the right most leaf is a constant whose value is [{[X]} + 1]. We use
Coq's mutually inductive type to define such syntax trees. *)

Inductive aexp' : Type :=
  | ANum' (t : term)
  | AId' (X: var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp')
with term : Type :=
  | TNum (n : Z)
  | TId (x: logical_var)
  | TDenote (a : aexp')
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term).

(** Here, an integer term in assertions can be a constant, a program expression's
value, the sum of two subterms, the subtraction of two subterms or the
multiplication of two terms. Also, we define variable bool expressions based on
variable integer expressions. *)

Inductive bexp' : Type :=
  | BTrue'
  | BFalse'
  | BEq' (a1 a2 : aexp')
  | BLe' (a1 a2 : aexp')
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').

(** The following are some notations for pretty printing. It is worth noticing
those [Coercion] statements. A coercion from type [A] to type [B] allows Coq to
treat a value of type [A] as a value of type [B] when necessary. For example,
[Coercion ANum'] means [ANum' t] can be written as [t] for convenience. *)

Coercion ANum' : term >-> aexp'.
Coercion AId' : var >-> aexp'.
Bind Scope vimp_scope with aexp'.
Bind Scope vimp_scope with bexp'.
Delimit Scope vimp_scope with vimp.

Notation "x + y" := (APlus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x - y" := (AMinus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x * y" := (AMult' x y) (at level 40, left associativity) : vimp_scope.
Notation "x <= y" := (BLe' x y) (at level 70, no associativity) : vimp_scope.
Notation "x == y" := (BEq' x y) (at level 70, no associativity) : vimp_scope.
Notation "x && y" := (BAnd' x y) (at level 40, left associativity) : vimp_scope.
Notation "'!' b" := (BNot' b) (at level 39, right associativity) : vimp_scope.

Coercion TNum : Z >-> term.
Coercion TId: logical_var >-> term.
Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%vimp)) (at level 30, no associativity) : term_scope.

(** Of course, every normal expression is a variable expression. *)

Fixpoint ainj (a: aexp): aexp' :=
  match a with
  | ANum n        => ANum' (TNum n)
  | AId X         => AId' X
  | APlus a1 a2   => APlus' (ainj a1) (ainj a2)
  | AMinus a1 a2  => AMinus' (ainj a1) (ainj a2)
  | AMult a1 a2   => AMult' (ainj a1) (ainj a2)
  end.

Fixpoint binj (b : bexp): bexp' :=
  match b with
  | BTrue       => BTrue'
  | BFalse      => BFalse'
  | BEq a1 a2   => BEq' (ainj a1) (ainj a2)
  | BLe a1 a2   => BLe' (ainj a1) (ainj a2)
  | BNot b1     => BNot' (binj b1)
  | BAnd b1 b2  => BAnd' (binj b1) (binj b2)
  end.

(** The following two lines of [Coercion] definition say that Coq will treat
[a] as [ainj b] and treat [b] a s [binj b] automatically when a variable
expression is needed. *)

Coercion ainj: aexp >-> aexp'.
Coercion binj: bexp >-> bexp'.

Module example.

Example coercion_ex: ainj (APlus (ANum 0) (ANum 1)) = APlus' (ANum' 0) (ANum' 1).
Proof.
(** The left hand side is actually not a normal expression, but a variable
expression too. The [Coercion] definition tells Coq to hide that [ainj] when
printing it out, *)
  simpl.
  reflexivity.
Qed.

End example.

(** Next, we define the syntax tree of assertions. *)

Inductive Assertion : Type :=
  | AssnLe (t1 t2 : term)
  | AssnLt (t1 t2 : term)
  | AssnEq (t1 t2 : term)
  | AssnDenote (b: bexp')
  | AssnOr (P1 P2 : Assertion)
  | AssnAnd (P1 P2 : Assertion)
  | AssnImpl (P1 P2 : Assertion)
  | AssnNot (P: Assertion)
  | AssnExists (x: logical_var) (P: Assertion)
  | AssnForall (x: logical_var) (P: Assertion).

Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (AssnLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (AssnLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x = y" := (AssnEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (AssnDenote ((b)%vimp)) (at level 30, no associativity) : assert_scope.
Notation "P1 'OR' P2" := (AssnOr P1 P2) (at level 76, left associativity) : assert_scope.
Notation "P1 'AND' P2" := (AssnAnd P1 P2) (at level 74, left associativity) : assert_scope.
Notation "P1 'IMPLY' P2" := (AssnImpl P1 P2) (at level 74, left associativity) : assert_scope.
Notation "'NOT' P" := (AssnNot P) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' P " := (AssnExists x ((P)%assert)) (at level 77,  right associativity) : assert_scope.
Notation "'FORALL' x ',' P " := (AssnForall x ((P)%assert)) (at level 77, right associativity) : assert_scope.

(** Based on these definitions, we are already able to write assertions and
triples. *)

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c%imp Q) (at level 90, c at next level).

Module Assertion_Triple_Example.

Definition X: var := 0%nat.
Definition Y: var := 1%nat.
Definition TEMP: var := 99%nat.
Definition n: logical_var := 0%nat.
Definition m: logical_var := 1%nat.
Definition k: logical_var := 2%nat.
Definition q: logical_var := 3%nat.

Definition assertion_ex1: Assertion :=
  {[X]} = n AND {[Y]} = m.

Definition assertion_ex2: Assertion :=
  EXISTS q, {[X]} * k + q = m AND 0 <= q AND q < k.

Definition triple_ex: hoare_triple :=
  {{ {[X]} = n AND {[Y]} = m }}
  TEMP ::= X;;
  X ::= Y;;
  Y ::= TEMP
  {{ {[X]} = m AND {[Y]} = n }}.

End Assertion_Triple_Example.

(* ================================================================= *)
(** ** Syntactic Substitution *)

(** In order to formulate Hoare logic proof rules, we need to formalize
_syntactic substition_ of program variables. Here we define the result of
replacing [X] with [E]. Since integer variable expressions and integer terms
are defined as mutually inductive types, this substitution should be defined
as mutual recursion. *)

Fixpoint aexp_sub (X: var) (E: aexp') (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_sub X E t)
    | AId' X' =>
         if Nat.eq_dec X X'
         then E
         else AId' X'
    | APlus' a1 a2 => APlus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMinus' a1 a2 => AMinus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMult' a1 a2 => AMult' (aexp_sub X E a1) (aexp_sub X E a2)
    end
with term_sub (X: var) (E: aexp') (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x => TId x
    | TDenote a => TDenote (aexp_sub X E a)
    | TPlus t1 t2 => TPlus (term_sub X E t1) (term_sub X E t2)
    | TMinus t1 t2 => TMinus (term_sub X E t1) (term_sub X E t2)
    | TMult t1 t2 => TMult (term_sub X E t1) (term_sub X E t2)
    end.

Fixpoint bexp_sub (X: var) (E: aexp') (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_sub X E a1) (aexp_sub X E a2)
    | BLe' a1 a2 => BLe' (aexp_sub X E a1) (aexp_sub X E a2)
    | BNot' b => BNot' (bexp_sub X E b)
    | BAnd' b1 b2 => BAnd' (bexp_sub X E b1) (bexp_sub X E b2)
    end.

(** The definition till now is trivial. But we must be very careful when
defining substitution in assertions. A naive attempt will not work. *)

Module Assertion_Sub_Attempt.

Fixpoint assn_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (assn_sub X E P1) (assn_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (assn_sub X E P1) (assn_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (assn_sub X E P1) (assn_sub X E P2)
    | AssnNot P      => AssnNot (assn_sub X E P)
    | AssnExists x P => AssnExists x (assn_sub X E P)
    | AssnForall x P => AssnForall x (assn_sub X E P)
    end.

End Assertion_Sub_Attempt.

(** What's wrong? Consider the following substitution,

    (Exists x, {[X]} = x + 1) [X |-> x]

Theoretically, the correct substition result should be:

    (Exists x, {[X]} = x + 1) [X |-> x]    ===>
    (Exists y, {[X]} = y + 1) [X |-> x]    ===>
    Exists y, x = y + 1.

But the definition above says:

    (Exists x, {[X]} = x + 1) [X |-> x]    ===>
    Exists x, x = x + 1

which does not make sense. The lesson that we learnt from this failure is that
we need to define logical variable's renaming first. *)

Fixpoint aexp_rename (x y: logical_var) (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_rename x y t)
    | AId' X => AId' X
    | APlus' a1 a2 => APlus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMinus' a1 a2 => AMinus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMult' a1 a2 => AMult' (aexp_rename x y a1) (aexp_rename x y a2)
    end
with term_rename (x y: logical_var) (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    | TDenote a => TDenote (aexp_rename x y a)
    | TPlus t1 t2 => TPlus (term_rename x y t1) (term_rename x y t2)
    | TMinus t1 t2 => TMinus (term_rename x y t1) (term_rename x y t2)
    | TMult t1 t2 => TMult (term_rename x y t1) (term_rename x y t2)
    end.

Fixpoint bexp_rename (x y: logical_var) (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_rename x y a1) (aexp_rename x y a2)
    | BLe' a1 a2 => BLe' (aexp_rename x y a1) (aexp_rename x y a2)
    | BNot' b => BNot' (bexp_rename x y b)
    | BAnd' b1 b2 => BAnd' (bexp_rename x y b1) (bexp_rename x y b2)
    end.

Fixpoint assn_rename (x y: logical_var) (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2    => AssnLe (term_rename x y t1) (term_rename x y t2)
    | AssnLt t1 t2    => AssnLt (term_rename x y t1) (term_rename x y t2)
    | AssnEq t1 t2    => AssnEq (term_rename x y t1) (term_rename x y t2)
    | AssnDenote b    => AssnDenote (bexp_rename x y b)
    | AssnOr P1 P2    => AssnOr (assn_rename x y P1) (assn_rename x y P2)
    | AssnAnd P1 P2   => AssnAnd (assn_rename x y P1) (assn_rename x y P2)
    | AssnImpl P1 P2  => AssnImpl (assn_rename x y P1) (assn_rename x y P2)
    | AssnNot P       => AssnNot (assn_rename x y P)
    | AssnExists x' P => if Nat.eq_dec x x'
                         then AssnExists x' P
                         else AssnExists x' (assn_rename x y P)
    | AssnForall x' P => if Nat.eq_dec x x'
                         then AssnForall x' P
                         else AssnForall x' (assn_rename x y P)
    end.

(** Also, we need to find a logical variable which is not yet used. This is
easy -- we just choose the largest used variable index's successor. *)

Fixpoint aexp_max_var (a: aexp'): logical_var :=
    match a with
    | ANum' t => term_max_var t
    | AId' X => O
    | APlus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMinus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMult' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    end
with term_max_var (t: term): logical_var :=
    match t with
    | TNum n => O
    | TId x => x
    | TDenote a => aexp_max_var a
    | TPlus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMinus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMult t1 t2 => max (term_max_var t1) (term_max_var t2)
    end.

Fixpoint bexp_max_var (b: bexp'): logical_var :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BLe' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BNot' b => bexp_max_var b
    | BAnd' b1 b2 => max (bexp_max_var b1) (bexp_max_var b2)
    end.

Fixpoint assn_max_var (d: Assertion): logical_var :=
    match d with
    | AssnLe t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnLt t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnDenote b    => bexp_max_var b
    | AssnOr P1 P2    => max (assn_max_var P1) (assn_max_var P2)
    | AssnAnd P1 P2   => max (assn_max_var P1) (assn_max_var P2)
    | AssnImpl P1 P2  => max (assn_max_var P1) (assn_max_var P2)
    | AssnNot P       => assn_max_var P
    | AssnExists x' P => max x' (assn_max_var P)
    | AssnForall x' P => max x' (assn_max_var P)
    end.

Definition new_var (P: Assertion) (E: aexp'): logical_var :=
  S (max (assn_max_var P) (aexp_max_var E)).

(** Now we need to determine whether a renaming is necessary in substition.
Consider a substition of the following form (where logical variable [x] may
appear in [P]):

    (EXISTS x, P) [X |-> E].

Do we need a renaming from [x] to some unused variable [y]? It depends on
whether [x] occurs in [E]. The following function computes the number of [x]'s
occurrence in [E]. *)

Fixpoint aexp_occur (x: logical_var) (a: aexp'): nat :=
    match a with
    | ANum' t => term_occur x t
    | AId' X => O
    | APlus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMinus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMult' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    end
with term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TNum n => O
    | TId x' => if Nat.eq_dec x x' then S O else O
    | TDenote a => aexp_occur x a
    | TPlus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMinus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMult t1 t2 => (term_occur x t1) + (term_occur x t2)
    end.

(** Eventually, we can define syntactic substition in assertions. *)

Fixpoint rename_all (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe t1 t2
    | AssnLt t1 t2   => AssnLt t1 t2
    | AssnEq t1 t2   => AssnEq t1 t2
    | AssnDenote b   => AssnDenote b
    | AssnOr P1 P2   => AssnOr (rename_all E P1) (rename_all E P2)
    | AssnAnd P1 P2  => AssnAnd (rename_all E P1) (rename_all E P2)
    | AssnImpl P1 P2 => AssnImpl (rename_all E P1) (rename_all E P2)
    | AssnNot P      => AssnNot (rename_all E P)
    | AssnExists x P => match aexp_occur x E with
                        | O => AssnExists x (rename_all E P)
                        | _ => AssnExists
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    | AssnForall x P => match aexp_occur x E with
                        | O => AssnForall x (rename_all E P)
                        | _ => AssnForall
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    end.

Fixpoint naive_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (naive_sub X E P1) (naive_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (naive_sub X E P1) (naive_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (naive_sub X E P1) (naive_sub X E P2)
    | AssnNot P      => AssnNot (naive_sub X E P)
    | AssnExists x P => AssnExists x (naive_sub X E P)
    | AssnForall x P => AssnForall x (naive_sub X E P)
    end.

Definition assn_sub (X: var) (E: aexp') (P: Assertion): Assertion :=
  naive_sub X E (rename_all E P).

Notation "P [ X |-> E ]" := (assn_sub X E ((P)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a [ X |-> E ]" := (aexp_sub X E ((a)%vimp)) (at level 10, X at next level) : vimp_scope.

(** In logic text books, substitution in a quantifed assertion is defined as
renaming first followed by recursive substitution. In formally,

    (EXISTS x, P) [X |-> E]    ===>
    EXISTS y, P [x |-> y] [X |-> E]

in which [y] is an unused logical variable. Our definition of [assn_sub] is not
that natural comparing this traditional approach. We write this definition like
only in order to fit Coq's requirement of structure recursion. *)

(* ================================================================= *)
(** ** Hoare logic's Proof System *)

(** In logic studies, a set of proof rules, which can be used compositionally
in reasoning, is called a _proof system_ (推理系统), or a logic. A Hoare triple is
called _provable_ (可证) if we can prove it in the Hoare logic within finite
steps. Thus, "provable" can be defined in Coq as an inductive predicate. *)

Module Attempt1.

Inductive provable: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}}) ->
      provable ({{Q}} c2 {{R}}) ->
      provable ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable ({{ P AND {[b]} }} c {{P}}) ->
      provable ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_fwd : forall P (X: var) E (x: logical_var),
      provable (
        {{ P }}
        X ::= E
        {{ EXISTS x, P [X |-> x] AND
                     {[X]} = {[ E [X |-> x] ]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }}).
(*
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}}).
*)

End Attempt1.

(** The formalization attempt above does not work very well because we have not
defined _assertion derivation_ yet.  In fact, different logics for assertion
derivation correspond to different Hoare logics even if all proof rules other
than the consequence rule remain the same. Coq enable us to express this idea
by defining a parameterized Hoare logic, the parameter [D] below represents
the derivation relation between two assertions. *)

Module Attempt2.

Inductive provable (D: Assertion -> Assertion -> Prop): hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable D ({{P}} c1 {{Q}}) ->
      provable D ({{Q}} c2 {{R}}) ->
      provable D ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable D ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable D ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable D ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable D ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable D ({{ P AND {[b]} }} c {{P}}) ->
      provable D ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_fwd : forall P (X: var) E (x: logical_var),
      provable D (
        {{ P }}
        X ::= E
        {{ EXISTS x, P [X |-> x] AND
                     {[X]} = {[ E [X |-> x] ]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable D ({{ P [ X |-> E] }} X ::= E {{ P }})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      D P P' -> (* P |-- P' *)
      provable D ({{P'}} c {{Q'}}) ->
      D Q' Q -> (* Q' |-- Q *)
      provable D ({{P}} c {{Q}}).

End Attempt2.

(** We use Coq's type class to turn on notations for assertion derivation.
*)

Class FirstOrderLogic: Type := {
  FOL_provable: Assertion -> Prop
}.

Definition derives {T: FirstOrderLogic} (P Q: Assertion): Prop :=
  FOL_provable (P IMPLY Q).

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}}) ->
      provable ({{Q}} c2 {{R}}) ->
      provable ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable ({{ P AND {[b]} }} c {{P}}) ->
      provable ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}}).

(** Also, we choose to pick the backward assignment rule but not to include the
forward assignment rule here. We will show that it is not a harmful design
choice -- these two assignment rules can be derived from each other. *)

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

(* ################################################################# *)
(** * Hoare Triples' Semantic Meaning Via Denotations *)

(** In Hoare logic, we use a Hoare triple

    {{P}} c {{Q}}

to represent: if the beginning state satisfies [P] and [c]'s execution
terminates, the ending state will always satisfy [Q]. This property can also
be described using the denotational semantics.

Remember, logical variables may occur in assertions. Thus, when we define the
satisfaction relation, it is a relation between program states and assertions
under a specific _assignment_ (指派) of logical variables. *)

Definition Lassn: Type := logical_var -> Z.

Definition Lassn_update (La: Lassn) (x: logical_var) (v: Z): Lassn :=
  fun y => if (Nat.eq_dec x y) then v else La y.

(** In summary, an _interpretation_ (解释) of program variables and logical
variables is a pair of program state and logical variable assignment. *)

Definition Interp: Type := state * Lassn.

Definition Interp_Lupdate (J: Interp) (x: logical_var) (v: Z): Interp :=
  (fst J, Lassn_update (snd J) x v).

(** We first define the meaning (or the denotations) of variable expressions.*)

Fixpoint aexp'_denote (J: Interp) (a: aexp'): Z :=
    match a with
    | ANum' t => term_denote J t
    | AId' X => (fst J) X
    | APlus' a1 a2 => aexp'_denote J a1 + aexp'_denote J a2
    | AMinus' a1 a2 => aexp'_denote J a1 - aexp'_denote J a2
    | AMult' a1 a2 => aexp'_denote J a1 * aexp'_denote J a2
    end
with term_denote (J: Interp) (t: term): Z :=
    match t with
    | TNum n => n
    | TId x => (snd J) x
    | TDenote a => aexp'_denote J a
    | TPlus t1 t2 => term_denote J t1 + term_denote J t2
    | TMinus t1 t2 => term_denote J t1 - term_denote J t2
    | TMult t1 t2 => term_denote J t1 * term_denote J t2
    end.

Fixpoint bexp'_denote (J: Interp) (b: bexp'): Prop :=
    match b with
    | BTrue' => True
    | BFalse' => False
    | BEq' a1 a2 => aexp'_denote J a1 = aexp'_denote J a2
    | BLe' a1 a2 => (aexp'_denote J a1 <= aexp'_denote J a2)%Z
    | BNot' b => ~ bexp'_denote J b
    | BAnd' b1 b2 => bexp'_denote J b1 /\ bexp'_denote J b2
    end.

Fixpoint satisfies (J: Interp) (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2 => (term_denote J t1 <= term_denote J t2)%Z
    | AssnLt t1 t2 => (term_denote J t1 < term_denote J t2)%Z
    | AssnEq t1 t2 => (term_denote J t1 = term_denote J t2)%Z
    | AssnDenote b => bexp'_denote J b
    | AssnOr P1 P2 => (satisfies J P1) \/ (satisfies J P2)
    | AssnAnd P1 P2 => (satisfies J P1) /\ (satisfies J P2)
    | AssnImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | AssnNot P => ~ (satisfies J P)
    | AssnExists x P => exists v, satisfies (Interp_Lupdate J x v) P
    | AssnForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

(** We can prove that these two definitions coincide with [aeval] and [beval]
on normal expressions. *)

Lemma aeval_aexp'_denote: forall st La a,
  aeval a st = aexp'_denote (st, La) (ainj a).
Proof.
  intros.
  induction a; simpl.
  + reflexivity.
  + reflexivity.
  + unfold Func.add.
    rewrite IHa1, IHa2.
    reflexivity.
  + unfold Func.sub.
    rewrite IHa1, IHa2.
    reflexivity.
  + unfold Func.mul.
    rewrite IHa1, IHa2.
    reflexivity.
Qed.

Lemma beval_bexp'_denote: forall st La b,
  beval b st <-> bexp'_denote (st, La) (binj b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + unfold Sets.complement.
    tauto.
  + unfold Sets.intersect.
    tauto.
Qed.

(** Based on these definitions, we can state the semantic meaning of Hoare
triples. *)

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity).

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q =>
      forall La st1 st2,
        (st1, La) |== P -> ceval c st1 st2 -> (st2, La) |== Q
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

(** Intuitively, a Hoare triple is _valid_ (有效) if it is true on all possible
assignment. *)

(** Traditionally, a single turnstile "|--" is used to represent a proof-theory
related concept, like "provable" and "derivable". But a double turnstile "|=="
is used to represent a semantic concept like "satisfaction relation", "valid"
and "consequence relation". *)

(* ################################################################# *)
(** * Hoare Logic Versus Denotational Semantics *)

(** Comparing with the denotational semantics, Hoare logic is a more coarse
grained description of program behavior. It is natural to ask whether they are
indeed equivalent. This equivalence property is called the soundness and
completeness of Hoare logic. *)

Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |-- {{ P }} c {{ Q }} ->
    |== {{ P }} c {{ Q }}.

Definition hoare_complete (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |== {{ P }} c {{ Q }} ->
    |-- {{ P }} c {{ Q }}.

(** Remember, we are not talking about one Hoare logic but a series of Hoare
logics. Every different first order logic for assertion derivation defines a
different Hoare logic. Thus, we would ask more specifically: for what kind of
assertion derivation logics, their corresponding Hoare logics are sound and
complete? A short answer is:

    - if the assertion derivation logic is sound, the
      corresponding Hoare logic is sound;
    
    - if the assertion language is expressive enough and
      the assertion derivation logic is complete, the
      corresponding Hoare logic is complete.
*)



(* Tue Apr 14 11:45:42 CST 2020 *)
