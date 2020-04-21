Require Import PL.Imp3.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Weakest Precondition *)

(** A Hoare logic is complete if all valid Hoare triples are provable. *)

Definition hoare_complete (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |== {{ P }} c {{ Q }} ->
    |-- {{ P }} c {{ Q }}.

(** The general idea of proving Hoare logic completeness is to prove those
Hoare triples with weakest preconditions are provable. Specifically, an
assertion [P] is called the weakest precondition of [c] and [Q] if Hoare triple

    {{P}} c {{Q}}

is valid and for any other [P'], if [{{P'}} c {{Q}}] is valid, then

    P' IMPLY P

is valid. Again, remember that an assertion is called valid if it is satisfied
on all interpreations. *)

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition wp' (P: Assertion) (c: com) (Q: Assertion): Prop :=
  (|== {{ P }} c {{ Q }}) /\
  (forall P', (|== {{ P' }} c {{ Q }}) -> FOL_valid  (P' IMPLY P)).

(** Although this definition above is very natural, we can actually be more
specific on what this weakest precondition should be. *)

Definition wp (P: Assertion) (c: com) (Q: Assertion): Prop :=
  forall st La,
    (st, La) |== P <->
    (forall st', ceval c st st' -> (st', La) |== Q).

(** This definition says: a beginning state [st] satisfies [P] if and only if
all possible ending states of executing [c] will satisfy [Q]. This definition
directly defines what interpreations satisfy [P]. Of course, it is consistent
will our previous definition. *)

Lemma wp_wp': forall P c Q,
  wp P c Q -> wp' P c Q.
Proof.
  intros.
  unfold wp in H; unfold wp'.
  split.
  + unfold valid.
    intros.
    specialize (H st1 La).
    firstorder.
  + intros.
    unfold FOL_valid; simpl.
    intros.
    destruct J as [st La].
    rewrite H.
    unfold valid in H0.
    specialize (H0 La st).
    pose proof classic ((st, La) |== P').
    destruct H1; [right | left; exact H1].
    firstorder.
Qed.

(** Hoare logic's completeness proof needs two important lemmas:

    - expressiveness: for any [c] and [Q], there is an assertion
      to express the weakest precondition of [c] and [Q];

    - if [P] expresses the weakest precondition of [c] and [Q],
      then [ {{ P }} c {{ Q }} ] is provable.

Here are their formal statement. *)

Definition expressive: Prop :=
  forall c Q, exists P, wp P c Q.

Definition wp_provable (T: FirstOrderLogic): Prop :=
  forall P c Q, wp P c Q -> |-- {{ P }} c {{ Q }}.

(** We show that, if there two properties hold, the Hoare logic is complete
given the fact that the assertion derivation logic itself is complete. *)

Definition FOL_complete (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_valid P -> FOL_provable P.

Proposition Hoare_complete_main_proof: forall T: FirstOrderLogic,
  expressive ->
  wp_provable T ->
  FOL_complete T ->
  hoare_complete T.
Proof.
  intros.
  unfold hoare_complete.
  intros P' c Q ?.
  (** First, by expressiveness, there is an assertion [P] which can
  express [c] and [Q]'s weakest precondition. *)
  unfold expressive in H.
  specialize (H c Q).
  destruct H as [P ?].
  (** Next, by the fact that all triples with weakest preconditions
  are provable, we know that [ {{ P }} c {{ Q }} ] is provable. *)
  unfold wp_provable in H0.
  specialize (H0 _ _ _ H).
  (** Now, by the definition of "weakest_pre", we know that [P'] is
  semantically stronger than [P]. *)
  apply wp_wp' in H.
  unfold wp' in H.
  destruct H.
  apply H3 in H2; clear H H3.
  (** Since we assume that the first order logic [T] is complete, we
  know that [P' |-- P] from the fact that [P' IMPLY P] is valid. *)
  assert (P' |-- P).
  {
    unfold FOL_complete in H1.
    unfold derives.
    apply H1.
    exact H2.
  }
  clear H2.
  (** In the end, we complete our Hoare logic proof using the consequence
  rule. *)
  assert (Q |-- Q).
  {
    unfold FOL_complete in H1.
    unfold derives.
    apply H1.
    unfold FOL_valid.
    intros; simpl.
    tauto.
  }
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + exact H2.
Qed.

(* ################################################################# *)
(** * Proof of Expressiveness *)

(** We prove this lemma by induction over the syntax tree of [c]. *)

(* ================================================================= *)
(** ** If [c = Skip] *)

(** We are going to prove that: for any assertion [Q], there is another
assertion [P] such that [P] is [c] and [Q]'s weakest precondition.

Let [P] be [Q]. Then for given [st] and [La], it is obvious that

    (st, La) |== P

is equivalent to

    forall st', ceval c st st' -> (st, La) |== Q

since [c = Skip] and [P = Q]. *)

(* ================================================================= *)
(** ** If [c = X ::= E] *)

(** The conclusion can be easily proved if we let [P] be

    Q [X |-> E].
*)

(* ================================================================= *)
(** ** If [c = c1 ;; c2] *)

(** IH1: for any assertion [Q], there is another assertion [P] such that [wp P
c1 Q].

IH2: for any assertion [Q], there is another assertion [P] such that [wp P c2
Q].

We are going to prove that: for any assertion [Q], there is another assertion [P] such that [wp P c Q].

For a fixed postcondition [Q] of [c], let [Q0] be [c2] and [Q]'s weakest
precondition and let [P] be [c1] and [Q0]'s weakest precondition (they must
exist according to IH). And we know that for any [st] and [La],

    (st, La) |== P iff for any st', if ceval c1 st st', then (st', La) |== Q0;
    (st, La) |== Q0 iff for any st', if ceval c2 st st', then (st', La) |== Q.

Combining them together, we have

    (st, La) |== P iff for any st' st'',
       if ceval c1 st st' and ceval c2 st' st'', then (st'', La) |== Q.

Thus, [wp P (c1;;c2) Q]. *)

(* ================================================================= *)
(** ** If [c = If b Then c1 Else c2 EndIf *)

(** IH1: for any assertion [Q], there is another assertion [P] such that [wp P
c1 Q].

IH2: for any assertion [Q], there is another assertion [P] such that [wp P c2
Q].

We are going to prove that: for any assertion [Q], there is another assertion [P] such that [wp P c Q].

For a fixed postcondition [Q] of [c], let [P1] be [c1] and [Q]'s weakest
precondition and let [P2] be [c2] and [Q]'s weakest precondition (they must
exist according to IH). And we know that for any [st] and [La],

    (st, La) |== P1 iff for any st', if ceval c1 st st', then (st', La) |== Q;
    (st, La) |== P2 iff for any st', if ceval c2 st st', then (st', La) |== Q.

Let [P] be [ P1 AND {[b]} OR P2 AND NOT {[b]} ]. Now, given an interpretation
[(st, La)], it satisfies [P] if and only if one of the following is true:

    (st, La) |== P1 and beval b st
    (st, La) |== P2 and (beval b st) is not true.

According to how [P1] and [P2] are introduced, we know [P] is a weakest
precondition of [c] and [Q], i.e. [wp P c Q]. *)

(* ================================================================= *)
(** ** If [c = While b Do c1 EndWhile] *)

(** This is the most difficult case. We want to find a weakest precondition of
[c] and [Q], with the help from induction hypothesis (IH) is: for any assertion
[Q'], there is another assertion [P'] such that [wp P' c1 Q'].

By the definition of [wp], we want to find an assertion [P] such that:

    (st(0), La) |== P if and only if
      for any natural number n,
        for any program states st(1), ..., st(n),
        if for any 0 <= i < n,
             (A) beval b st(i)
             (B) ceval c1 st(i) st(i+1)
        then either (beval b st(n)) or (st(n), La) |== Q.

We know that only finite program variables can be mentioned in [Q] and [c].
Suppose they are [X1], [X2], ..., [Xm]. Then we can restate the criterion
above -- [P] should be (informally):

      for any natural number n,
        for any integers x(0,1), x(0,2), ..., x(0,m),
                         x(1,1), x(1,2), ..., x(1,m),
                         x(2,1), x(2,2), ..., x(2,m),
                         ...
                         x(n,1), x(n,2), ..., x(n,m),
        if
        (1) {[ X1 ]} == x(0,1) AND ... AND {[ Xm ]} == x(0, m) AND
        (2) for any i, if 0 <= i < n, then
              (2.1) b [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]
              (2.2) IH(X1 = x(i + 1, 1) AND ... AND Xm = x(i + 1, m))
                      [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]
              (2.3) NOT IH(False) [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]
        then either
        (3) b [ X1 |-> x(n, 1); ...; Xm |-> x(n, m) ]; or
        (4) Q [ X1 |-> x(n, 1); ...; Xm |-> x(n, m) ].

In this informal statement, we use [x(i,1), x(i,2), ..., x(i,m)] to represent
all program variables' values after [i] iterations. Property (1) says that
[(st, La)] agree with the description of [x(0,1), x(0,2), ..., x(0,m)].
Property (2.1) says that the loop condition is true after the first [i]
iterations. Property (2.2) says: if the loop body of [i+1]th iteration
terminates, its ending state is the one described by [x(i+1,1), ..., x(i+1,m)].
Eventually, property (2.3) says: if the loop body of [i+1]th iteration will
terminate.

Noticing that this is almost an assertion, except for one thing -- the dynamic
sized quantification over integers [x]s. This problem can be solved by Godel's
beta predicate. *)

(* ================================================================= *)
(** ** Godel Beta Predicate *)

(** The Godel beta predicate [Beta(a,b,i,x)] is defined as:

    x = a mod (1 + (i+1) * b)

According to The Chinese remainder theorem, for any natural number [n] and
natural number sequence [x(0)], [x(1)], ..., [x(n)], there always exist [a] and
[b] such that for any [0 <= i <= n],

    Beta(a, b, i, y) if and only if y = x(i).

That means, any quantification over sequences can be represented by a
combination of a fixed number of normal quantification and the Godel beta
predicate. For example, the following two statement are equivalent:

    for any natural numbers n, x(0), x(1), ..., x(n),
      if for any i, 0 <= i < n, x(i) <= x(i+1) holds,
      then x(n) satisfies property R

and

    for any natural numbers n, a, b,
      if:
         for any i, x and x',
           if 0 <= i < n, Beta(a, b, i, x) and Beta(a, b, i+1, x')
           then x < x'
      then:
         for any x,
           if Beta(a, b, n, x) then x satisfies property P.

Using this method, we can easily state loops' weakest preconditions in our
assertion language.

This proves the expressiveness lemma. *)

(* ################################################################# *)
(** * Establishing Triples With Weakest Precondtions *)

(** In this part, we prove that if [P] is [c] and [Q]'s weakest precondition,
then the Hoare triple is provable. Noticing that the assertion [P] is not
necessarily the weakest precondition constructed by the expressiveness lemma,
we argue about all possible triples such that [wp P c Q] holds.

Again, we prove this lemma by induction over the syntax tree of [c]. *)

(* ================================================================= *)
(** ** If [c = Skip] *)

(** If [P] is a weakest precondition of [c] and [Q], we know that [P] is
actually equivalent with [Q]. Thus, [ P IMPLY Q ] is a valid first order
proposition. By the assertion derivation logic's completeness, we know that
[ P |-- Q] which is immediately followed by [ |-- {{ P }} c {{ Q }} ] according
to the consequence rule. *)

(* ================================================================= *)
(** ** If [c = X ::= E] *)

(** The proof is similar. *)

(* ================================================================= *)
(** ** If [c = c1 ;; c2] *)

(** The proof is similar. *)

(* ================================================================= *)
(** ** If [c = If b Then c1 Else c2 EndIf *)

(** The proof is similar. *)

(* ================================================================= *)
(** ** If [c = While b Do c1 EndWhile] *)

(** This is the only interesting case! Suppose [wp P c Q]. We know:

    for any st and La,
      (st, La) |== P if and only if
      for any st', if (ceval c st st'), then (st', La) |== Q.

Now, consider the weakest precondition of [c1] and [P]. We claim that
[ P AND {[ b ]} ] is stronger than weakest preconditions of [c1] and [P].

For fixed [st] and [La], if

    (st, La) |== P AND {[ b ]}

then for any [st']

    if (ceval c st st'), then (st', La) |== Q.

Since [b] is true on [st], we know that for any [st'] and [st''],

    if (ceval c1 st st') and (ceval c st' st''), then (st'', La) |== Q.

This is equivalent to say: for any [st'],

    if (ceval c1 st st') then for any st'',
       if (ceval c st' st''), then (st'', La) |== Q.

By the fact that [wp P c Q], we conclude that for any [st'],

    if (ceval c1 st st') then (st', La) |== P.

Now, suppose [P'] is a weakest precondtion of [c] and [P] (by expressiveness
lemma, it must exist). What we just proved means that [(P AND {[ b ]}) IMPLY P']
is a valid assertion. By the first order logic's completeness,

    P AND {[b]} |-- P'.

By induction hypothesis:

    |-- {{ P' }} c1 {{ P }}.

Then by the consequence rule:

    |-- {{ P AND {[ b ]} }} c1 {{ P }}.

Thus,

    |-- {{ P }} c {{ P AND NOT {[ b ]} }}.

At the same time, due to [wp P c Q], it is obvious that if [(st, La) |== P AND
NOT {[ b ]}] on some interpretation [(st, La)], then [(st, La) |== Q]. In other
words, [ (P AND NOT {[ b ]}) IMPLY Q ] is valid. Thus,

    P AND NOT {[ b ]} |-- Q.

So,

    |-- {{ P }} c {{ Q }}.

This proves that all triples with weakest preconditions are provable. *)

(* Tue Apr 21 11:15:40 CST 2020 *)
