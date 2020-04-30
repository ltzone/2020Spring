(** Remark. Some material in this lab is from << Software Foundation >> volume
    1. *)

Require Import Coq.Lists.List.
Require Import PL.Imp3.

(* ################################################################# *)
(** * Lists in Coq *)

(** An inductive definition of _lists_ of numbers: *)

Module Playground1.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check (cons Z 3 (nil Z)).

  (* cons Z 3 (nil Z) : list Z *)

Check (cons Z 2 (cons Z 1 (nil Z))).

  (* cons Z 2 (cons Z 1 (nil Z)) : list Z *)

Module ImpList.

Import Concrete_Pretty_Printing.

Local Instance X: var := new_var().

Check (cons aexp 2 (cons aexp X (nil aexp))).

  (* cons aexp 2 (cons aexp X (nil aexp)) : list aexp *)

Check (cons aexp (X + 1)%imp (cons aexp (X * X)%imp (nil aexp))).

  (* cons aexp (X + 1)%imp (cons aexp (X * X)%imp (nil aexp))
     : list aexp *)

End ImpList.

Check (cons (list Z) (cons Z 2 (cons Z 1 (nil Z))) (nil (list Z))).

  (* cons (list Z) (cons Z 2 (cons Z 1 (nil Z))) (nil (list Z))
     : list (list Z) *)

(** We can avoid writing type arguments in most cases by telling Coq _always_
to infer the type argument(s) of a given function. The [Arguments] directive
specifies the name of the function (or constructor) and then lists its argument
names, with curly braces around any arguments to be treated as implicit. (If
some arguments of a definition don't have a name, as is often the case for
constructors, they can be marked with a wildcard pattern [_].) *)

Arguments nil {X}.
Arguments cons {X} _ _.

Check (cons 2 (cons 1 nil)).

  (* cons 2 (cons 1 nil) : list Z *)

Check (cons (cons 2 (cons 1 nil)) nil).

  (* cons (cons 2 (cons 1 nil)) nil : list (list Z) *)

(** Some notation for lists to make our lives easier: *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(** It is not necessary to understand the details of these
    declarations, but here is roughly what's going on in case you are
    interested.  The [right associativity] annotation tells Coq how to
    parenthesize expressions involving multiple uses of [::] so that,
    for example, the next three declarations mean exactly the same
    thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** The [length] function calculates the length of a list. *)

Fixpoint length {X : Type} (l : list X) : Z :=
  match l with
  | nil => 0
  | cons _ l' => length l' + 1
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** The [app] function concatenates (appends) two lists. *)

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

(** Since [app] will be used extensively in what follows, it is
    again convenient to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** Induction on Lists *)

(** We have learnt Coq's structural induction tactic in Coq. We can use it on
    lists. *)

(** **** Exercise: 1 star, standard (app_assoc)  *)

Theorem app_assoc : forall A (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

Fixpoint rev {A} (l: list A) : list A :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [rev] *)

(** Now, for something a bit more challenging than the proofs
    we've seen so far, let's prove that reversing a list does not
    change its length.  Our first attempt gets stuck in the successor
    case... *)

Theorem rev_length_firsttry : forall A (l : list A),
  length (rev l) = length l.
Proof.
  intros. induction l.
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl.
    (* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and state it as a separate
    lemma. *)

(** **** Exercise: 1 star, standard (app_length)  *)
Theorem app_length : forall A (l1 l2 : list A),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. lia.
Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [list]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall A (l : list A),
  length (rev l) = length l.
Proof.
  intros. induction l.
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length. simpl. lia.
Qed.

(** **** Exercise: 1 star, standard (app_nil_r)  *)
Theorem app_nil_r : forall A (l : list A),
  l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (rev_app_distr)  *)
Theorem rev_app_distr: forall A (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (rev_involutive)  *)
Theorem rev_involutive : forall A (l : list A),
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr.
    rewrite IHl. reflexivity.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Map *)

(** [Map] is a higher-order function. *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ] and returns
the list [ [f n1, f n2, f n3,...] ], where [f] has been applied to each element
of [l] in turn.  For example: *)

Definition minustwo (x: Z): Z := x - 2.

Example test_map1: map minustwo [7;5;7] = [5;3;5].
Proof. reflexivity.  Qed.

Example test_map2:
    map (fun n => [n - 1; n + 1]) [2;1;5] = [[1;3];[0;2];[4;6]].
Proof. reflexivity.  Qed.

Theorem map_app : forall (A B : Type) (f : A -> B) (l l' : list A),
  map f (l ++ l') = map f l ++ map f l'.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

(** **** Exercise: 1 star, standard (map_rev)  *)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite map_app.
    rewrite IHl. reflexivity.
Qed.
(** [] *)

(** An even more powerful higher-order function is called [fold_right]. *)

Fixpoint fold_right {X Y: Type} (f: X->Y->Y) (b: Y) (l: list X): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold_right f b t)
  end.

(** Intuitively, the behavior of the [fold_right] operation is to insert
a given binary operator [f] between every pair of elements in a given list. For
example, [ fold plus [1;2;3;4] ] intuitively means [1+2+3+4]. To make this
precise, we also need a "starting element" that serves as the initial second
input to [f].  So, for example,

       fold_right plus 0 [1;2;3;4]

    yields

       1 + (2 + (3 + (4 + 0))).
*)

Example fold_example1 :
  fold_right Z.mul 1 [1;2;3;4] = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold_right app [] [[1];[];[2;3];[4]] = [1;2;3;4].
Proof. reflexivity. Qed.

Example fold_example3 :
  fold_right (fun f x => f x) nil [cons 1; cons 2; app [3; 4]; cons 5]
= [1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold_right (fun x l' => f x :: l') nil l.

(** **** Exercise: 1 star, standard (fold_map_correct)  *)
Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold fold_map in *. simpl. rewrite IHl.
    reflexivity.
Qed.
(** [] *)

End Playground1.

(** Most of these definitions and lemmas are already built in Coq's standard
    library. *)

Import ListNotations.

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [even]) can be thought of
as a _property_ -- i.e., it defines a subset of [nat], namely those numbers for
which the proposition is provable. In the same way, a two-argument proposition
can be thought of as a _relation_ -- i.e., it defines a set of pairs for which
the proposition is provable.

Besides defining a relation by describing the specific function mapping from
element pairs to [Prop], we can also define it inductively in Coq. *)

Module Playground2.
Local Open Scope nat.
  
(** One useful example is the "less than or equal to" relation on natural
numbers. The following definition should be fairly intuitive. It says that
there are two ways to give evidence that one number is less than or equal to
another: either observe that they are the same number, or give evidence that
the first is less than or equal to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n: nat) : le n n
  | le_S (n m: nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Like [cons], [nil], [S] and [O] in the inductive definitions of [lists] and
[nat], [le_n_n] and [le_S] in this definition are also called constructors.

We can [apply] the constructors to prove [<=] goals (e.g., to show that [3<=3]
or [3<=6]), and we can use [inversion] to extract information from [<=]
hypotheses. *)

(** WARNING: here, decimal numbers like [0], [3], [15], etc. are treated as
natural numbers [nat], not integer [Z]. It is different from other material of
this course because we import different files from standard library. When those
decimals were by-default treated as [Z], write [0%nat], [3%nat], [15%nat], etc.
to let Coq know that it is a natural number *)

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le3 : forall n: nat,
  n <= 0 -> n = 0.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem test_le4 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros.
  inversion H.
  inversion H2.
Qed.

Theorem test_le5 : forall n m: nat,
  n <= S m -> n = S m \/ n <= m.
Proof.
  intros.
  inversion H.
  + left.
    reflexivity.
  + right.
    exact H2.
Qed.

(** You might feel those equalities quite annoying. The [subst] tactic may be
useful. Specifically, [subst x] replace [x] with [E] everywhere if [x = E] is
an assumption. *)

Theorem test_le5' : forall n m: nat,
  n <= S m -> n = S m \/ n <= m.
Proof.
  intros.
  inversion H.
  + subst n.
    left.
    reflexivity.
  + subst n0.
    subst m0.
    right.
    exact H2.
Qed.

(** Or, just [subst] with no arguments will do all possible substitions. *)
Theorem test_le5'' : forall n m: nat,
  n <= S m -> n = S m \/ n <= m.
Proof.
  intros.
  inversion H; subst.
  + left.
    reflexivity.
  + right.
    exact H2.
Qed.

(** Also, we can do induction over an assumption which is about an inductively
defined predicate. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0.
  - apply H.
  - apply le_S.
    apply IHle.
    exact H.
Qed.

(** Here are a number of facts about the [<=] relation. *)

(** **** Exercise: 3 stars, standard (le_exercises)  *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* intros. 
  remember (S n) as n'. remember (S m) as m'.
  induction H.
  - subst. injection Heqm'. intros. subst. apply le_n.
  - subst.  *)  
  revert n H.
  induction m;intros.
  - inversion H. apply le_n. inversion H2.
  - inversion H;subst.
    + apply le_n.
    + apply IHm in H2.
      apply le_S.
      apply H2.
Qed.
(** [] *)

End Playground2.

(** A list is a _subsequence_ of another list if all of the elements in the
first list occur in the same order in the second list, possibly with some extra
elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].
*)

Inductive subseq {A: Type} : list A -> list A -> Prop :=
  | sub_nil  l : subseq [] l
  | sub_take x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | sub_skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2).

(** **** Exercise: 1 star, standard (subseq_refl)  *)
Theorem subseq_refl : forall (A: Type) (l : list A), subseq l l.
Proof.
  intros.
  induction l.
  - apply sub_nil.
  - apply sub_take. apply IHl.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (subseq_app)  *)
Theorem subseq_app : forall (A: Type) (l1 l2 l3 : list A),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply sub_nil.
  - simpl. apply sub_take. apply IHsubseq.
  - simpl. apply sub_skip. apply IHsubseq.
Qed.
(** Hint: remember to use [simpl] to simplify expressions when necessary. *)
(** [] *)

(** **** Exercise: 3 stars, standard (subseq_map)  *)
Theorem subseq_map : forall (A B: Type) (f: A -> B) (l1 l2: list A),
  subseq l1 l2 ->
  subseq (map f l1) (map f l2).
Proof.
  intros. induction H;intros;simpl.
  - apply sub_nil.
  - apply sub_take. apply IHsubseq.
  - apply sub_skip. apply IHsubseq.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (subseq_trans)  *)
Theorem subseq_trans : forall (A: Type) (l1 l2 l3 : list A),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros A l1 l2 l3 S12 S23. revert l1 S12.
  (** Here, we need a stronger induction hypotheses. *)
  induction S23 as [|x l2 l3 |x l2 l3];intros;simpl.
  - inversion S12;subst. apply sub_nil.
  - inversion S12;subst.
    { apply sub_nil. }
    { apply sub_take. apply IHS23. apply H1. }
    { apply sub_skip. apply IHS23. apply H1. }
  - apply sub_skip. apply IHS23. apply S12.
Qed.
(** [] *)

(* Thu Apr 30 00:22:48 CST 2020 *)
