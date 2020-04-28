Require Import Coq.Lists.List.
Require Import PL.Imp3.
Import OneBinRel_FOL.
Local Open Scope FOL.

(* ################################################################# *)
(** * Review *)

(** In a logic, a statement is _provable_ (可证) if we can derive it from proof
    rules. A statement is _valid_ (有效) if it is always true according a
    semantic definition. We say a logic is _sound_ (可靠) if all provable
    statements are valid. We say a logic is _complete_ (完全) if all valid
    statements are provable.  We have proved that our Hoare logic is sound
    and/or complete if the underlying logic for assertion derivation is sound
    and/or complete. *)

(* ################################################################# *)
(** * FOL Completeness: The definition *)

Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.

(** This definition of completeness is also called weak completeness. What is
strong completeness instead? *)

Definition derive (Gamma: prop -> Prop) (P: prop): Prop :=
  exists l, Forall Gamma l /\ |-- fold_right PImpl P l.

Notation "Gamma  |--  P" := (derive Gamma P) (at level 90, no associativity): FOL_scope.

(** Here, [Forall Gamma l] says that all elements in [l] are elements in
[Gamma]. Here is the definition of [Forall] in Coq standard library.
Intuitively, if propositions [Gamma] derive [P], there is one [Gamma]'s finite
subset, such that the conjunction of this subset implies [P]. *)

Print Forall.

(** If [derive] is a generalization of [provable], then [entail] is a
generalization of [valid]. *)

Definition entail (Gamma: prop -> Prop) (P: prop): Prop :=
  forall J, (forall Q, Gamma Q -> J |== Q) -> J |== P.

Notation "Gamma  |=  P" := (entail Gamma P) (at level 90, no associativity): FOL_scope.

(** In logic, if a set of propositions [Gamma] entails [P], we say that [P] is
a consequence (语义后承) of [Gamma]. The double turnstile symbol is usually
overloaded in logic text books. Here is its different meaning.

    - [J |== P], in which [J] is an interpretation and [P] is a
      proposition. It says [J] satisfies [P], or [satisfies J P]
      in our Coq definition;

    - [|== P], in which [P] is a proposition. It says that [P] is
      valid. In other words, for any [J], [J |== P];

    - [J |== Gamma], in which [J] is an interpretation and [Gamma]
      is a set of propositions. It says that [J] satisfies every
      proposition in [Gamma];

    - [Gamma |== P], in which [Gamma] is a set of propositions and
      [P] is one single proposition. It says that [P] is a consequence
      of [Gamma].

In this course, we only use [ |== ] for the first two notation definitions but
use [ |= ] for the last one.

After defining [derive] and [entail], we are ready to state the strong
completeness property. *)

Definition strongly_complete: Prop :=
  forall Gamma P,
    Gamma |= P -> Gamma |-- P.

(** Obvious, if a logic is strongly complete, it must be complete. To prove
this theorem, we only need to let the proposition set [Gamma] to be empty. In
Coq, an empty set is defined by "no element is in it". *)

Definition Empty_pset: prop -> Prop := fun P => False.

(** It is easy to prove that an empty set derives an assertion [P] if and only
if this assertion [P] is provable. *)

Lemma Empty_derive_spec: forall P, Empty_pset |-- P <-> |-- P.
Proof.
  intros.
  split; intros.
  + destruct H as [l [? ?]].
    inversion H; subst.
    - simpl in H0.
      exact H0.
    - unfold Empty_pset in H1.
      destruct H1.
  + exists nil.
    split.
    - apply Forall_nil.
    - simpl.
      exact H.
Qed.

(** Also, being a consequence of the empty proposition set is equivalent with
being valid. *)

Lemma Empty_entail_spec: forall P, Empty_pset |= P <-> |== P.
Proof.
  intros.
  unfold entail, valid.
  unfold Empty_pset.
  firstorder.
Qed.

Theorem strong_completeness_is_stronger: strongly_complete -> complete.
Proof.
  unfold strongly_complete, complete.
  intros SC.
  specialize (SC Empty_pset).
  intros.
  apply Empty_derive_spec.
  apply Empty_entail_spec in H.
  apply SC.
  apply H.
Qed.

(* ################################################################# *)
(** * Important FOL theorems *)

(** We directly state the following theorems and omit proofs. Interested
students can try proving them as exercises. *)

Lemma IMPLY_refl: forall P, |-- P IMPLY P.
Admitted.

Lemma IMPLY_trans: forall P Q R, |-- P IMPLY Q -> |-- Q IMPLY R -> |-- P IMPLY R.
Admitted.

Lemma IMPLY_swap: forall P Q R, |-- P IMPLY Q IMPLY R -> |-- Q IMPLY P IMPLY R.
Admitted.

Lemma EM_assu: forall P Q, |-- P IMPLY Q -> |-- NOT P IMPLY Q -> |-- Q.
Admitted.

Lemma FORALL_rename: forall P (x y: logical_var),
  prop_free_occur y P = O ->
  |-- (FORALL x, P) IMPLY (FORALL y, P [x |-> y]).
Admitted.

Lemma PEq_trans: forall t1 t2 t3,
  |-- t1 = t2 IMPLY t2 = t3 IMPLY t1 = t3.
Admitted.

Lemma derive_assu: forall (Gamma: prop -> Prop) P,
  Gamma P ->
  Gamma |-- P.
Admitted.

Definition pset_included (Gamma Gamma': prop -> Prop): Prop :=
  forall P, Gamma P -> Gamma' P.

Lemma derive_expand: forall Gamma Gamma' P,
  pset_included Gamma Gamma' ->
  Gamma |-- P ->
  Gamma' |-- P.
Admitted.

Definition pset_snoc (Gamma: prop -> Prop) (P: prop): prop -> Prop :=
  fun Q => Gamma Q \/ P = Q.

Notation "Gamma ':;' P" := (pset_snoc Gamma P) (at level 81, left associativity): FOL_scope.

Lemma deduction_theorem: forall Gamma P Q,
  Gamma:; P |-- Q <-> Gamma |-- P IMPLY Q.
Admitted.

Lemma derive_modus_ponens: forall Gamma P Q,
  Gamma:; P |-- Q ->
  Gamma |-- P ->
  Gamma |-- Q.
Admitted.

Lemma derive_NOT_NOT: forall Gamma P,
  Gamma |-- P <-> Gamma |-- NOT NOT P.
Admitted.

Lemma derive_EXISTS_intros: forall Gamma P Q x,
  (forall R, (Gamma:; Q) R -> prop_free_occur x R = O) ->
  Gamma:; P |-- Q ->
  Gamma:; EXISTS x, P |-- Q.
Admitted.

Lemma PRel_congr: forall Gamma t1 t2 t3 t4,
  Gamma:; t1 = t2:; t3 = t4:; PRel t1 t3 |-- PRel t2 t4.
Admitted.

(* ################################################################# *)
(** * Proof By Contraposition: Satisfiability and Consistency *)

(** We prove strong completeness by contraposition. In other words, we prove
that, if [P] is not derivable from [Gamma] then [P] is not a consequence of
[Gamma]. The negation of [derive] and [entail] are strongly connected with two
other concepts: consistent (一致) and satisfiable (可满足). *)

Definition consistent (Gamma: prop -> Prop): Prop :=
  ~ (Gamma |-- PFalse).

(** A proposition set is consistent if we cannot derive false from it. For any
[Gamma] and [P], [Gamma] do not derive [P] if and only if [Gamma] and [NOT P]
are consistent. *)

Lemma not_derive_spec: forall Gamma P,
  ~ (Gamma |-- P) <-> consistent (Gamma:; (NOT P)).
Proof.
  intros.
  unfold consistent.
  rewrite deduction_theorem.
  pose proof derive_NOT_NOT Gamma P.
  unfold PNot.
  unfold PNot in H.
  tauto.
Qed.

(** A proposition set is satisfiable if there is an interpretation that satisfies
all propositions in the set. For any [Gamma] and [P], [P] is not [Gamma]'s
consequence if and only if [Gamma] and [NOT P] are satisfiable. *)

Definition satisfiable (Gamma: prop -> Prop): Prop :=
  exists J, forall P, Gamma P -> J |== P.

Lemma not_entail_spec: forall Gamma P,
  ~ (Gamma |= P) <-> satisfiable (Gamma:; (NOT P)).
Proof.
  intros.
  unfold satisfiable, entail.
  split; intros.
  + apply not_all_ex_not in H.
    (* not_all_ex_not
         : forall (U : Type) (P : U -> Prop),
           ~ (forall n : U, P n) -> exists n : U, ~ P n
    *)
    destruct H as [J ?].
    assert ((forall Q : prop, Gamma Q -> J |== Q) /\ ~ (J |== P)).
    { tauto. }
    clear H.
    destruct H0.
    exists J.
    unfold pset_snoc.
    intros.
    destruct H1.
    - apply H.
      exact H1.
    - subst P0.
      simpl.
      tauto.
  + unfold not.
    intros.
    destruct H as [J ?].
    specialize (H0 J).
    assert (forall Q : prop, Gamma Q -> J |== Q).
    {
      intros.
      apply H.
      unfold pset_snoc.
      tauto.
    }
    assert (~ (J |== P)).
    {
      assert ((Gamma:; NOT P) (NOT P)).
      { unfold pset_snoc. right. reflexivity. }
      specialize (H _ H2).
      simpl in H.
      tauto.
    }
    tauto.
Qed.

(** Thus, in order to build completeness, it suffices to prove that every
consistent set is satisfiable. *)

Lemma proof_by_contraposition:
  (forall Gamma, consistent Gamma -> satisfiable Gamma) ->
  strongly_complete.
Proof.
  intros.
  unfold strongly_complete.
  intros Gamma P.
  assert (~ (Gamma |-- P) -> ~ (Gamma |= P)); [| tauto].
  intros.
  apply not_derive_spec in H0.
  apply not_entail_spec.
  apply H.
  exact H0.
Qed.

(* ################################################################# *)
(** * Henkin Style Proof and Maximal Consistent Set *)

(** The following part of our proof is of a famous proof style for logic
completeness, the Henkin style proof. It contains two steps: (1) expanding a
consistent set of propositions to a _maximal consistent set_ (MCS) (极大一致集); and
(2) constructing an interpretation (usually called _canonical model_) (典范模型)
that satisfies all propositions in the MCS. *)

Definition maximal_consistent (Gamma: prop -> Prop): Prop :=
  consistent Gamma /\
  (forall Gamma', pset_included Gamma Gamma' ->
                  consistent Gamma' ->
                  pset_included Gamma' Gamma).

(** In a simplest Henkin style proof, MCS is enough for canonical model
construction. For first order logics's completeness, we need to use maximal
consistent set with witnesses. *)

Definition witnessed (Gamma: prop -> Prop): Prop :=
  forall (x: logical_var) (P: prop),
    Gamma (EXISTS x, P) ->
    exists (t: term), Gamma (P [ x |-> t ]).

(** Here is the proof skeleton of our Henkin style proof. *)

Lemma Henkin_FOL:
  (forall Gamma, consistent Gamma ->
     exists Gamma',
       maximal_consistent Gamma' /\
       witnessed Gamma' /\
       (satisfiable Gamma' -> satisfiable Gamma)) ->
  (forall Gamma,
     maximal_consistent Gamma ->
     witnessed Gamma ->
     satisfiable Gamma) ->
  (forall Gamma, consistent Gamma -> satisfiable Gamma).
Proof.
  intros.
  specialize (H Gamma H1).
  destruct H as [Gamma' [? [? ?]]].
  specialize (H0 Gamma' H H2).
  pose proof H3 H0.
  exact H4.
Qed.

(* ################################################################# *)
(** * Lindenbaum Lemma: Constructing MCS with witness *)

(** In this part, we prove: if [Gamma] is consistent, we can "expand" it to a
witnessed MCS. The construction here is not real expansion. Remark: suppose
[Gamma'] is an expansion of [Gamma], then we immediately know that: if [Gamma']
is satisfiable, then [Gamma] is satisfiable. *)

(* ================================================================= *)
(** ** Step 1. *)

(** Let [Gamma(0)] be the renaming result of [Gamma]. Specifically, every
proposition [P'] in [Gamma(0)] corresponds to a proposition [P] in [Gamma].
{P'] is the resulting of replacing the [n]-th variable with the [2n + 1]-th
variable for all [n].

Thus, [Gamma] is satisfiable if and only if [Gamma(0)] is satisfiable. Also,
since [Gamma] is consistent, [Gamma(0)] is also consistent. Moreover, variables
with even indices do not occur in [Gamma(0)]'s elements. *)

(* ================================================================= *)
(** ** Step 2. *)

(** Obviously, first order propositions are countable. Suppose they are

    P(1), P(2), ...

We construct

    Gamma(1), Gamma(2), ...

in order. Specifically, for every natural number [n], we construct [Gamma(n+1)]
from [Gamma(n)] according to the following rules:

    - case a. if [Gamma(n):; P(n+1)] is consistent and
                 [P(n+1)] has a form of [EXISTS x. Q], then
              let [Gamma(n+1)] be [Gamma(n) :; Q[x |-> y] :; P(n+1)]
              in which [y] is a variable that does not occur in
              [Gamma(n)] or [P(n+1)].

    - case b. if [Gamma(n):; P(n+1)] is consistent and
                 [P(n+1)] does not have a form of [EXISTS x. Q], then
              let [Gamma(n+1)] be [Gamma(n):; P(n+1)].

    - case c. if [Gamma(n):; P(n+1)] is inconsistent, then
              let [Gamma(n+1)] be [Gamma(n)].

First of all, such construction is legal (especially case a). Because for every
natural number [n], [Gamma(n)] only uses finite number of variables with even
indices.

Moreover, this sequence of proposition sets satisfies the following properties:

    - [Gamma(n)] is consistent for all [n];

    - [P(n)] is an element of [Gamma(m)] if and only if [P(n)] is in
      [Gamma(n)] for any [n < m];

    - [Gamma(0)] is a subset of [Gamma(n)] for all [n].

We can prove them by induction over [n]. Almost all of these proof steps are
trivial. The only interesting case is the following one:

    - Suppose [Gamma(n):; P(n+1)] is consistent and [P(n+1) = EXISTS x. Q].
      Prove that [Gamma(n) :; Q[x |-> y] :; P(n+1)] is also consistent in which
      [y] is a variable that does not occur in [Gamma(n)] or [P(n+1)].

We prove it by contradiction. If it were not consistent, then

    Gamma(n) :; Q[x |-> y] :; EXISTS x. Q |-- PFalse.

Since [|-- Q [x |-> y] IMPLY EXISTS x. Q], we have

    Gamma(n) :; Q [x |-> y] |-- PFalse.

But [y] does not appear in [Gamma(n)]. So,

    Gamma(n) :; EXISTS y. Q [x |-> y] |-- PFalse.

It is equivalent to say:

    Gamma(n) :; EXISTS x. Q |-- PFalse.

This contradicts with the fact that [Gamma(n):; P(n+1)] is consistent. *)

(* ================================================================= *)
(** ** Step 3 *)

(** Let [Gamma'] be the union of all [Gamma(n)]'s. Now, let's check whether
[Gamma'] is indeed an MCS with witnesses.

First, [Gamma'] is consistent. If not, there is a finite subset of it which can
derive false. Formally, we can find [P(n(1)), P(n(2)), ..., P(n(k))] such that,

    P(n(1)) IMPLY P(n(2)) IMPLY  ... IMPLY P(n(k)) IMPLY PFalse

is provable. Without loss of generality, we can assume that

    n(1) < n(2) < ... < n(k).

Thus, these [k] propositions must all be [Gamma(n(k))]'s elements! So,

    Gamma(n(k)) |-- PFalse

which contradicts with the fact that [Gamma(n(k))] is consistent.

Second, adding any more proposition to [Gamma'] makes it inconsistent. Suppose
[P(n)] is not an element of [Gamma']. We know that [P(n)] must not be an
element of [Gamma(n)]. Thus, [Gamma(n-1) :; P(n)] is inconsistent. Since
[Gamma':; P(n)] is a superset of it, [Gamma':; P(n)] is also inconsistent.

Third, [Gamma'] is witnessed. Suppose [P(n) = EXISTS x. Q] is an element of
[Gamma']. Then according to the construction of [Gamma(n)] there must be an
logical variable [y] such that [Q [ x |-> y] ] is an element of [Gamma']. *)

(* ================================================================= *)
(** ** Summary *)

(** Now, we have shown that [Gamma'] is witnessed and maximally consistent.
Also, it is a superset of [Gamma(0)] by definition. Thus, if [Gamma'] is
satisfiable, [Gamma(0)] is satisfiable, which is equivalent to say that [Gamma]
is satisfiable. *)

(* ################################################################# *)
(** * Canonical Model Construction and Truth Lemma *)

(** We first state and prove two important properties of MCS.

Property 1. A maximally consistent set [Gamma] is always closed under the
[derive] relation. This is obvious. Suppose [Gamma |-- P]. Since [Gamma] is
consistent, i.e. [Gamma |-/- PFalse], we know that [Gamma :; P |-/- PFalse].
But any expansion of [Gamma] is inconsistent. Thus, [P] must be an element of
[Gamma].

Property 2. If [Gamma] is maximally consistent and [P] is a proposition, exact
one of [P] and [NOT P] are in [Gamma]. This is also obvious. On one hand, if
both [P] and [NOT P] are in [Gamma], [Gamma] must be inconsistent since

    |-- NOT P IMPLY P IMPLY PFalse.

On the other hand, if neither [P] nor [NOT P] is in [Gamma], we know

    Gamma :; P |-- PFalse

by the definition of _maximal_ consistency. It tells us, [P IMPLY PFalse], i.e.
[NOT P], is an element of [Gamma] (according to the deduction theorem and the
fact that [Gamma] is derive-closed). This contradicts with the fact that
[NOT P] is not in [Gamma].

Now, we are ready to prove:

    - Given [Gamma] which is witnessed and maximally consistent, we can
      construct an interpretation [J] satisfying all propositions in [Gamma].

We construct this interpretation step by step and prove the satisfaction
relation in the end. *)

(* ================================================================= *)
(** ** Constructing the domain *)

(** First, we claim that the pairs of variables [x, y] such that [x == y] is
a proposition in [Gamma] forms an equivalent relation. Then, we define the
domain [D] to be the equivalent classes of this relation. *)

(* ================================================================= *)
(** ** Constructing the relation symbol's interpretation *)

(** We define the relation symbol [PRel]'s interpretation [Rel] as follows.
Suppose [x*] and [y*] are two equivalent classes in the domain [D]. The pair
[x*, y*] is an element of [Rel] if and only if [PRel x y] is a proposition in
[Gamma]. Here [x] and [y] represent elements of [x*] and [y*].

It is critical that [Rel] is well defined. In fact, if [x1 == x2], [y1 == y2]
and [PRel x1 y1] are elements of [Gamma], [PRel x2 y2] must be its element
too. *)

(* ================================================================= *)
(** ** Constructing variables' interpretation *)

(** We simply let [La] be the function that [La(x) = x*]. Here, [x*] represents
the equivalent class in [D] such that [x] is in it. *)

(* ================================================================= *)
(** ** Truth lemma *)

(** We prove by induction over [P]'s syntax tree that [P] is an element of
[Gamma] if and only if [J = (D, Rel, La) ] satisfies [P].

Case 1: [P] is [x1 == x2].

[P] is an element of [Gamma] if and only if [x1] and [x2] are in the same
equivalent class in [D], which is equivalent to say that [x1] and [x2] has the
same denotation in [J].

Case 2: [P] is [PRel x1 x2].

It is obvious by [Rel]'s definition.

Case 3: [P] is [PFalse].

On one hand, [PFalse] cannot be [Gamma]'s element since it is consistent. On
the other hand, [PFalse] is not satisfied by any interpretation, including [J].

Case 4. [P] is [P1 IMPLY P2].

By semantic definition, [J] satisfies [P1 IMPLY P2] if and only if [J] does not
satisfy [P1] or [J] satisfies [P2]. By induction hypothesis, it is equivalent
to say that [P1] is not an element of [Gamma] or [P2] is an element of [Gamma].

    - If [P1] is not an element of [Gamma], [NOT P1] must be an element of
      [Gamma]. Thus, [P1 IMPLY P2] is also an element of [Gamma].
    - If [P2] is an element of [Gamma], obviously, [P1 IMPLY P2] is also an
      element of [Gamma].
    - If [P1] is an element of [Gamma] and [P2] is not an element of [Gamma],
      then [NOT P2] must be an element of [Gamma]. Thus, [NOT (P1 IMPLY P2)] is
      also an element of [Gamma] which means [P1 IMPLY P2] is not in [Gamma].

This tells us that [P1 IMPLY P2] is in [Gamma] if and only if [P1] is not in
[Gamma] or [P2] is in [Gamma].

Case 5. [P] is [FORALL x. P1].

On one hand, suppose [FORALL x. P1] is an element [Gamma]. We know that for any
variable [y], [ P1 [x |-> y] ] will also be [Gamma]'s element. By induction
hypothesis, [J] satisfies [ P1 [x |-> y] ]. Thus, no matter what value in [D]
is reassigned to the interpretation of [x], the new interpration will satisfy
[P1]. So, [J] satisfies [FORALL x. P1].

On the other hand, suppose [FORALL x. P1] is not an element [Gamma]. Then,
[EXISTS x, NOT P1] will be an element of [Gamma]. According to the fact that
[Gamma] is witnessed, there must exist a variable [y] such that
[ NOT P1 [x |-> y] ] is in [Gamma]. Thus [ P1 [x |-> y] ] is not an element
of [Gamma]. By induction hypothesis, [J] does not satisfy [ P1 [x |-> y] ].
So,

    ( D, Rel, La [x |-> y*] ) |=/= P1

which tells us that [J] does not satisfy [FORALL x. P1]. *)

(* ################################################################# *)
(** * Summary *)

(** FOL's completeness (weak completeness) can be established by the follwoing
    steps.

    - Reducing weak completeness to strong completeness. Here, strong
      completeness means: if [P] is a consequence of [Gamma], then [P] is
      derivable from [Gamma].

    - Reducing "consequence => derivable" to "consistent => satisfiable". This
      reduction step is done via proof by contradiction.

    - Proving that every consistent set can be expanded to a witnessed maximally
      consistent set. This construction is called Lindenbaum construction.

    - Proving that every witnessed maximally consistent set is satisfiable. This
      conclusion is called truth lemma. It is proved by induction over
      propositions' syntax trees.

    It is worth noticing that this completeness theorem only says FOL is strong
    enough to prove properties of logic connectives. In other words, function
    symbols and relational symbols can be arbitrarily explained. Thus, we cannot
    say that our logic is strong enough to establish all properties about
    arithmetics. In fact, no logic is strong enough to achieve that --- this is
    Godel's incompleteness theorem. *)

(* Tue Apr 28 00:57:34 CST 2020 *)
