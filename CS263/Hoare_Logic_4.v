Require Import PL.Imp.

Import Assertion_S.
Import Assertion_S_Tac.
Import Concrete_Pretty_Printing.


(* ################################################################# *)
(** * Program correctness proof in Coq *)

Module Axiomatic_semantics_demo.

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

(** Having one between the following two assignment rules is enough. *)
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

End Axiomatic_semantics_demo.

Module div_mod_dec_again.
Import Axiomatic_semantics.

(** Coq proof time! Now, we are able to prove a nicer Hoare triple with simpler
hypothese. *)

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

Hypothesis derivation1: forall m n: Z,
  0 <= m AND {[X]} = m AND {[Y]} = 0 |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]}.

Hypothesis derivation2: forall m n: Z,
  EXISTS z, n * {[Y]} + z = m AND 0 <= z AND n <= z AND {[X]} = z - n |--
  n * {[Y]} + {[X]} + n = m AND 0 <= {[X]}.

Hypothesis derivation3: forall m n: Z,
  EXISTS z, n * z + {[X]} + n = m AND 0 <= {[X]} AND {[Y]} = z + 1 |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]}.

Hypothesis derivation4: forall m n: Z,
  n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n.

Fact div_mod_dec_correct: forall m n: Z,
       {{ 0 <= m }}
       X ::= m;;
       Y ::= 0;;
       While n <= X Do
         X ::= X - n;;
         Y ::= Y + 1
       EndWhile
       {{ n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n }}.
Proof.
  intros.

(** Originally, if we want to use [apply] to prove this Hoare triple in the
backward direction, we have to feed it an argument, indicating what the middle
condition [Q] in [hoare_seq] represents. But if we use [eapply] instead of
[apply], we do not need to provide that argument. Mainly, [eapply hoare_seq]
says, we will apply this proof rule [hoare_seq] without knowing what [Q] is,
and we will know what that [Q] should be later. *)
  eapply hoare_seq.

(** As you can see, the unknown argument is marked as [?Q] which appear both in
the first proof goal and the second proof goal. Now, we use [hoare_asgn_fwd] to
solve the first proof goal. It will instantiate [?Q]. *)
  { apply hoare_asgn_fwd. }

  assert_subst.
  assert_simpl.
(** After eliminating the first assignment command using [hoare_seq] and
[hoare_asgn_fwd], we see the substitution symbol and the existential quantifier
in our precondition. Our library [PL.Imp] provided the two tactics to simplify
such assertions. *)

  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.

  apply hoare_consequence with
    (n * {[Y]} + {[X]} = m AND 0 <= {[X]})%assert
    (n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[ n <= X ]} )%assert.
  1: { apply (derivation1 m n). }
  2: { apply derivation4. }

  apply hoare_while.
  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.

  eapply hoare_consequence.
  + apply derivation2.
  + apply hoare_asgn_fwd.
  + assert_subst.
    assert_simpl.
    apply derivation3.  
Qed.

(** It is worth mentioning the proof style in the Coq proof script above. In
short, bullets (+, -, *, ++, --, **, etc.) and proof blocks ("{" and "}") can be
used to illustrate proof structures. Usually, they are used for two different
purposes. If two or more subgoals are equally complicated, we would prefer to
use bullets to list their proofs parallelly. If one branch among all subgoals
is the main proof target and the other proof goals are just side steps, we would
prefer to use proof blocks. *)

(** Now we try to prove the same Hoare triple again with forward proof style. *)
Fact div_mod_dec_correct_again: forall m n: Z,
       {{ 0 <= m }}
       X ::= m;;
       Y ::= 0;;
       While n <= X Do
         X ::= X - n;;
         Y ::= Y + 1
       EndWhile
       {{ n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n }}.
Proof.
  intros.

  pose proof hoare_asgn_fwd
               (n * {[Y]} + {[X]} = m AND
                0 <= {[X]} AND {[n <= X]})%assert
               X (X - n).
(** These two tactics [assert_subst] and [assert_simpl] can also simplify
assertions in assumptions *)
  assert_subst in H.
  assert_simpl in H.

  pose proof hoare_asgn_fwd
               (n * {[Y]} + {[X]} + n = m AND 0 <= {[X]})%assert
               Y (Y + 1).
  assert_subst in H0.
  assert_simpl in H0.

  pose proof hoare_consequence _ _ _ _ _
               (derivation2 m n) H0 (derivation3 m n).
  pose proof hoare_seq _ _ _ _ _ H H1.
  clear H H0 H1.

(** It is unfortunate that we cannot achieve a Hoare triple for the while loop
here using [H2] and [hoare_while] because the assertion that loop condition is
true

    {[n <= X]}

has been simplified into [ n <= {[X]} ]. Thus, we [assert] the triple that we
want to prove. *)
  assert ({{n * {[Y]} + {[X]} = m AND 0 <= {[X]}}} While n <= X Do (X ::= X - n);; Y ::= Y + 1 EndWhile {{n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]}}}).
(** After [assert], we first prove the asserted triple. *)
  {
    apply hoare_while.
    assert_simpl.
    exact H2.
  }
  clear H2.
(** We then prove the original proof goal with an extra assumption---the
asserted triple [H]. *)
  pose proof hoare_asgn_fwd
               (0 <= m)%assert
               X
               m.
  assert_subst in H0.
  assert_simpl in H0.

  pose proof hoare_asgn_fwd
               (0 <= m AND {[X]} = m)%assert
               Y
               0.
  assert_subst in H1.
  assert_simpl in H1.

  pose proof hoare_consequence _ _ _ _ _
               (derivation1 m n) H (derivation4 m n).
  pose proof hoare_seq _ _ _ _ _ H1 H2.
  pose proof hoare_seq _ _ _ _ _ H0 H3.
  exact H4.
Qed.

End div_mod_dec_again.

(* ################################################################# *)
(** * Derived proof rules and programmable proof tactics *)

Module derived_rules.

Import Assertion_S_Rules.
Import Axiomatic_semantics.

(** We know that an assertion can always derive itself. This property is called
[derives_refl] in our [Imp] library. *)

Check derives_refl.
  (* : forall P : Assertion, P |-- P *)

(** Using it, we can derive two specialized consequence rule. The first one is a
single-sided consequence rule for preconditions. *)

Corollary hoare_consequence_pre: forall P P' Q c,
  P |-- P' ->
  {{ P' }} c {{ Q }} ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + apply derives_refl.
Qed.

(** Similarly, we have a single-sided consequence rule for postconditions
as well. *)

Corollary hoare_consequence_post: forall P Q Q' c,
  {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + exact H.
  + exact H0.
Qed.

(** Since we prove these two rules from primary rules, we call them _derived
rules_ (导出规则). There are other derived proof rules. They can be useful for
some special situations. The following rule is a weaker version of [hoare_if]
(we have shown why it is weak in our previous lectures). We can derive it from
our primary [hoare_if] rule now. But this proof is based on the following
properties of [AND]. *)

Check AND_left1.
  (* : forall P Q R : Assertion,
       P |-- R -> P AND Q |-- R *)

Check AND_left2.
  (* : forall P Q R : Assertion,
       Q |-- R -> P AND Q |-- R *)

Corollary hoare_if_weak : forall P Q b c1 c2,
  {{P}} c1 {{Q}} ->
  {{P}} c2 {{Q}} ->
  {{P}} If b Then c1 Else c2 EndIf {{Q}}.
Proof.
  intros.
  apply hoare_if.
  + eapply hoare_consequence_pre.
    2: { exact H. }
    apply AND_left1.
    apply derives_refl.
  + eapply hoare_consequence_pre.
    2: { exact H0. }
    apply AND_left1.
    apply derives_refl.
Qed.

(** Also, we have seen a lot of examples, in which we use [hoare_seq] and
[hoare_asgn_fwd] together when the first command is an assignment. We can pack
them together: *)

Corollary hoare_asgn_seq: forall P `(X: var) E c Q,
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }} c {{ Q }} ->
  {{ P }} X ::= E ;; c {{ Q }}.
Proof.
  intros.
  eapply hoare_seq.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

(** What if the assignment is the only command? We have also seen a combination
of [hoare_asgn_fwd] and [hoare_consequence]. *)

Corollary hoare_asgn_conseq: forall P `(X: var) E Q,
  EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} |-- Q ->
  {{ P }} X ::= E {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence_post.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

(** These derived rule can make Coq formalized proofs shorter; and more
importantly, they help to describe how we understand Hoare logic proofs. We do
not apply proof rules one by one in our mind, we use proof rule "combos"
instead. Now, let's redo our proofs about swapping. *)

Local Instance X: var := new_var().
Local Instance Y: var := new_var().
Local Instance TEMP: var := new_var().

(* FILL IN HERE *)

Fact swaping_correct:
  forall x y: Z,
       {{ {[X]} = x AND {[Y]} = y }}
       TEMP ::= X;;
       X ::= Y;;
       Y ::= TEMP
       {{ {[X]} = y AND {[Y]} = x }}.
Proof.
(* WORKED IN CLASS *)
  intros.
  apply hoare_asgn_seq.
  assert_subst.
  assert_simpl.
  apply hoare_asgn_seq.
  assert_subst.
  assert_simpl.

  eapply hoare_consequence_pre.
  { apply der1. }
  apply hoare_asgn_conseq.
  assert_subst.
  assert_simpl.

  apply der2.
Qed.

End derived_rules.

(* ################################################################# *)
(** * Decorated program as informal Hoare logic proof *)

(** The beauty of Hoare Logic is that it is _compositional_ （可组合的）: the
structure of proofs exactly follows the structure of programs. This suggests
that we can record the essential ideas of a proof by "decorating" a program with
appropriate assertions on each of its commands. *)

(** In <<software foundation>>, such informal proofs are called _decorated
programs_. In other text books or programming language literature, they are
also called _annotated programs_ or _commented programs_ (带注释程序）. *)

(** Here are two sample decorated programs. *)

(** Sample 1

  /* 0 <= m */
  X ::= m;;
  Y ::= 0;;
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    Y ::= Y + 1
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n */.
*)

(** Sample 2

  /* 0 <= m */
  X ::= m;;
  /* EXISTS x, 0 <= m AND {[X]} = m */
  /* 0 <= m AND {[X]} = m */
  Y ::= 0;;
  /* EXISTS y, 0 <= m AND {[X]} = m AND {[Y]} = 0 */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    /* EXISTS x, n * {[Y]} + {[x]} = m AND
         0 <= {[x]} AND {[n <= x]} AND {[X]} = {[x - n]} */
    /* EXISTS x, n * {[Y]} + x = m AND
         0 <= x AND n <= x AND {[X]} = x - n */
    /* n * {[Y]} + {[X]} + n = m AND 0 <= {[X]} */
    Y ::= Y + 1
    /* EXISTS y, n * {[y]} + {[X]} + n = m AND
         0 <= {[X]} AND {[Y]} = {[y + 1]} */
    /* EXISTS y, n * y + {[X]} + n = m AND
         0 <= {[X]} AND {[Y]} = y + 1 */
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n */.
*)

(* ################################################################# *)
(** * Exercises *)

(** **** Exercise: 3 stars, standard (remainder_only)  *)

Module remainder_only.
Import Axiomatic_semantics.

Local Instance X: var := new_var().

(** In the this task, you can write hypothese about assignment commands without
proving them. *)

(* FILL IN HERE *)

Fact remainder_only_correct: forall m n: Z,
    {{ 0 <= m }}
    X ::= m;;
    While n <= X Do
      X ::= X - n
    EndWhile
    {{ (EXISTS q, n * q + {[X]} = m) AND 0 <= {[X]} AND NOT {[n <= X]} }}.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)

End remainder_only.

(** **** Exercise: 2 stars, standard (reduce_to_zero_alter1)  

    You are only allowed write assertion derivations as hypotheses in this
exercise. *)
Module reduce_to_zero_alter1.
Import Axiomatic_semantics.
Import derived_rules.

Local Instance X: var := new_var().

(** Hint: the following decorated program shows a proof skeleton.

       /* True */
       While !(X <= 0) Do
         /* True AND {[ !(X <= 0) ]} */
         /* True */
         X ::= X - 1
         /* EXISTS x, True AND {[X]} = {[x - 1]} */
         /* True */
       EndWhile
       /* True AND NOT {[ !(X <= 0) ]} */
       /* {[X]} <= 0 */.
*)

(* FILL IN HERE *)

Fact reduce_to_zero_correct:
       {{ True }}
       While !(X <= 0) Do
         X ::= X - 1
       EndWhile
       {{ {[X]} <= 0 }}.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)
End reduce_to_zero_alter1.

(** **** Exercise: 3 stars, standard (reduce_to_zero_alter2)  

    You are only allowed write assertion derivations as hypotheses in this
exercise. *)
Module reduce_to_zero_alter2.
Import Axiomatic_semantics.
Import derived_rules.

Local Instance X: var := new_var().

(* FILL IN HERE *)

Fact reduce_to_zero_correct:
       {{ 0 <= {[X]} }}
       While !(X <= 0) Do
         X ::= X - 1
       EndWhile
       {{ {[X]} = 0 }}.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)
End reduce_to_zero_alter2.

(* Thu Mar 12 04:30:38 CST 2020 *)
