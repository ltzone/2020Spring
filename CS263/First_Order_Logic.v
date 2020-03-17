(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1 and volume 2. *)

Require Import Coq.micromega.Psatz.
Require Import PL.Imp.
Require Import PL.ImpExt1.

Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.
Import Axiomatic_semantics.
Import derived_rules.

(* ################################################################# *)
(** * Review *)

(** Till now, we used a simple imperative programming language (指令式程序语言) as an
example to introduce the following concept:
- assertions (including syntactic substitution and assertion derivation)
- Hoare triples
- axiomatic semantics.

Also we have learnt how to use Hoare logic to prove a program correct. We
learnt to do it both on paper and in Coq. Moreover, we learnt to use decorated
programs to illustrate basic ideas in such proofs.

For Coq usage, we learnt the following tactics:
- rewrite
- intros
- apply
- pose proof
- exact
- eapply
- assert.
*)

Module reduce_to_zero.

(* ################################################################# *)
(** * Assertion entailment *)

(** For now, we still have to assume the correctness of some assertion
derivation. *)

(** The question is: do we really need to put derivation into hypothesis?
Can we prove them instead? The answer is yes. *)

Local Instance X: var := new_var().

Fact derivation_example:
  0 < {[X]} |-- 0 <= {[X]}.
Proof.
  (** Obviously, this proof goal is equivalent to say: for any integer [x], if
  [0 < x] then [0 <= x]. The following tactic [entailer] provided by our [Imp]
  library apply this transition for us. *)
  entailer.

  (** Now, we know that we should use "intros" to drag this universally
  quantified variable [X'] above the line. *)
  intros.

  (** Oops, it does more!! But that is reasonable. Proving [A -> B] (reads "[A]
  implies [B]" is equivalent with proving [B] with assumption [A]. We know that
  this proof goal is true. But at this position, what we have already learnt
  cannot help us much. The following tactic "lia" is to solve Linear Integer
  Arithmetic systems. Let's try it. *)
  lia.
Qed.

Lemma der1:
  0 <= {[X]} AND NOT {[! (X <= 0)]} |-- {[X]} = 0.
Proof.
  entailer.
  intros.

  (** The symbol "/\" (see the assumption [H]) represents "and" in Coq and the
  symbol "~" represents negation or "not". Let's see whether [lia] can handle
  conjunctions in assumptions. *)
  lia.

  (** Bingo! *)
Qed.

(** Now we have got both hypotheses proved. *)

End reduce_to_zero.

(** Coq also provide an automatic verification tactic for Non-linear Integer
Arithmetics, [nia]. It supports ring operations on integers (plus, minus and
multiplication). However, it is not a complete solver, i.e. it may fail to prove
a provable fact. Here are two examples in which [nia] succeeds. *)

Goal forall x y: Z, (x + 1) * y < y + x * y + 1.
Proof.
  intros.
  nia.
Qed.

(** In principle, [nia] knows to use commutative-ring equations (commutativity
and associativity of sum and multiplication, and the distributive law) and
to apply linear comparisons. *)

Goal forall x y: Z, (x + 1) * (x + 1) >= 0.
Proof.
  intros.
  nia.
Qed.

(** For non-linear inequalities, [nia] may succeed. *)

Goal forall x y: Z, (x + y) * (x + y) >= 0.
Proof.
  intros.
  Fail nia.
Abort.

(** ... and may fail as well. *)

(* ################################################################# *)
(** * Proving True *)

Module reduce_to_zero_der.

Local Instance X: var := new_var().

(** We do not need to derive [True] from anything else. It is by itself true. *)
Lemma der1:
  True AND {[! (X <= 0)]} |-- True.
Proof.
  entailer.
  intros.

  (** In Coq, [I] is a proof of [True]. Whenever you want to prove [True], use
  [exact I]. *)
  exact I.
Qed.

End reduce_to_zero_der.

(* ################################################################# *)
(** * Conjunction *)

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Lemma True2: True /\ True.
Proof.
  split.
  + exact I.
  + exact I.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_exercise :
  forall n m : Z, n + 2*m = 0 -> 2*n + m = 0 -> n = 0 /\ True.
Proof.
  intros.
  split.
  + lia.
  + exact I.
Qed.

(** To use a conjunctive hypothesis to help prove something else, we use the
[destruct] tactic. *)

Lemma and_example2 :
  forall n m : Z, n = 0 /\ (True -> m = 0) -> n + m = 0.
Proof.
  intros.
  destruct H.
  pose proof H0 I.
  lia.
Qed.

Lemma and_example2' :
  forall n m : Z, n = 0 /\ (True -> m = 0) -> n + m = 0.
Proof.
  intros.
  destruct H as [Hn H].
  pose proof H I as Hm.
  lia.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.

(** **** Exercise: 2 stars, standard (and_assoc)  *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros.
  destruct H as [HP [HQ HR]].
  repeat split.
  { exact HP. }
  { exact HQ. }
  { exact HR. }
Qed.

(** [] *)

(* ################################################################# *)
(** * Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is. *)

Lemma or_example :
  forall n m : Z, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros.
  destruct H.
  - rewrite H.
    lia.
  - rewrite H.
    lia.
Qed.

Lemma or_example2 :
  forall P Q R: Prop, (P -> R) -> (Q -> R) -> (P \/ Q -> R).
Proof.
  intros.
  destruct H1 as [HP | HQ].
  - apply H.
    exact HP.
  - pose proof H0 HQ.
    exact H1.
Qed.

(** Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma or_introl : forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  left.
  exact H.
Qed.

Lemma or_intror : forall A B : Prop, B -> A \/ B.
Proof.
  intros.
  right.
  exact H.
Qed.

(** **** Exercise: 1 star, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros.
  destruct H as [HP|HQ].
  - right. exact HP.
  - left. exact HQ.
Qed.

(** [] *)

(* ################################################################# *)
(** * Implication *)

(** If conjunction and disjunction are treated as important connectives in
logic, then implication must be foundamental. And we have actually used it for
many times. We have learnt how to prove the following one:*)

Theorem modus_ponens: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  pose proof H0 H.
  exact H1.
Qed.

(** But we can also prove it in alternative ways. *)

Theorem modus_ponens_alter1: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  revert H.
  exact H0.
Qed.

Theorem modus_ponens_alter2: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  specialize (H0 H).
  exact H0.
Qed.

(* ################################################################# *)
(** * Falsehood and Negation *)

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [contradiction] to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros.
  contradiction.
Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** The tactic [contradiction] also works if both [P] and [~P] appear
    in the proof context. *)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros.
  destruct H.
  contradiction.
Qed.

(** Besides the fact that [P] and [~P] cannot be both true, one of them must be
    true. This principle is called law of excluded middle, and is named
    [classic] in Coq. *)

Check classic.
  (* : forall P : Prop, P \/ ~ P *)

Theorem double_neg_elim : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros.
  pose proof classic P.
  destruct H0.
  + exact H0.
  + contradiction.
Qed.

Theorem not_False :
  ~ False.
Proof.
  (* WORKED IN CLASS *)
  pose proof classic False.
  destruct H.
  + contradiction.
  + exact H.
Qed.

Theorem double_neg_intro : forall P : Prop,
  P -> ~ ~ P.
Proof.
  (* WORKED IN CLASS *)
  intros.
  pose proof classic (~ P).
  destruct H0.
  + contradiction.
  + exact H0.
Qed.

(* ################################################################# *)
(** * Existential Quantification *)

(** To say that there is some [x] such that some property [P] holds of [x], we
write [exists x, P] in Coq and write [EXISTS x, P] in our assertion language.
To prove a statement of the form [exists x, P], we must show that [P] holds for
some specific choice of value for [x], known as the _witness_ of the existential. 
This is done in two steps: First, we explicitly tell Coq which witness [t] we
have in mind by invoking the tactic [exists t]. Then we prove that [P] holds
after all occurrences of [x] are replaced by [t]. *)

Lemma four_is_even : exists n, 4 = n + n.
Proof.
  exists 2.
  omega.
Qed.

Lemma six_is_not_prime: exists n, 2 <= n < 6 /\ exists q, n * q = 6.
Proof.
  exists 2.
  split.
  + omega.
  + exists 3.
    omega.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in Coq, we
    can [destruct] it *)

Theorem exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
(* WORKED IN CLASS *)
  intros.
  destruct H.
  exists (2 + x).
  omega.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
(* WORKED IN CLASS *)
  intros.
  destruct H as [x [HP HQ]].
  split.
  + exists x.
    exact HP.
  + exists x.
    exact HQ.
Qed.

(** Notice that the reverse direction of this theorem is not true. For example,
there obviously exists at least one even number and one odd number but there is
not number which is both even and odd. *)

Module sample_derivation.

Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.

Local Instance X: var := new_var().

Fact der: forall (m n: Z),
  0 <= m AND {[X]} = m |--
  EXISTS q, n * q + {[X]} = m AND 0 <= {[X]}.
Proof.
(* WORKED IN CLASS *)
  intros.
  entailer.
  intros.
  exists 0.
  lia.
Qed.

End sample_derivation.

(* ################################################################# *)
(** * Universal Quantification *)

(** The Coq tactic support for universal quantification is very similar to
implication's. In short, we use [pose proof] (or [specialize]) for universal
quantification in assumptions and we use [intros] for universal quantification
in a conclusion. Also, [apply] can be used for writing backward proofs.*)

Lemma forall_comm: forall (P: Z -> Z -> Prop),
  (forall x y, P x y) ->
  (forall y x, P x y).
Proof.
  intros.
  apply H.
Qed.

Lemma forall_example1: forall (P Q: Z -> Z -> Prop),
  P 0 1 ->
  (forall x y, P x y -> Q x y) ->
  Q 0 1.
Proof.
  intros.
  pose proof H0 0 1 H.
  exact H1.
Qed.

Lemma forall_example2: forall (P Q: Z -> Z -> Prop),
  P 0 1 ->
  (forall x y, P x y -> Q x y) ->
  Q 0 1.
Proof.
  intros.
  specialize (H0 0 1 H).
  exact H0.
Qed.

Lemma forall_example3: forall (P Q: Z -> Z -> Prop),
  P 0 1 ->
  (forall x y, P x y -> Q x y) ->
  Q 0 1.
Proof.
  intros.
  apply H0.
  exact H.
Qed.

Lemma forall_example4: forall (P Q: Z -> Z -> Prop),
  P 0 1 ->
  (forall x y, P x y -> Q x y) ->
  Q 0 1.
Proof.
  intros.
  apply H0 in H.
  exact H.
Qed.

(** **** Exercise: 1 star, standard (dist_not_exists)  

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  intros C.
  destruct C as [x Hx].
  specialize (H x).
  contradiction.
Qed.

(** [] *)

(* ################################################################# *)
(** * First Order Logic for Assertion Derivation *)

Module assertion_FOL.

(** The [Imp] library also supports first order logic proof directly, i.e., in
order to verify assertion derivation, you can choose not to reduce it to normal
Coq propositions. The following proof rules are provided for you. *)

Check AND_left1.
  (* : forall P Q R : Assertion,
       P |-- R -> P AND Q |-- R *)

Check AND_left2.
  (* : forall P Q R : Assertion,
       Q |-- R -> P AND Q |-- R *)

Check AND_right.
  (* : forall P Q R : Assertion,
       P |-- Q -> P |-- R -> P |-- Q AND R *)

Check OR_left.
  (* : forall P Q R : Assertion,
       P |-- R -> Q |-- R -> P OR Q |-- R *)

Check OR_right1.
  (* : forall P Q R : Assertion,
       P |-- Q -> P |-- Q OR R *)

Check OR_right2.
  (* : forall P Q R : Assertion,
       P |-- R -> P |-- Q OR R *)

Check CONTRA.
  (* : forall P Q : Assertion, P AND NOT P |-- Q *)

Check LEM.
  (* : forall P Q : Assertion, P |-- Q OR NOT Q *)

Check True_right.
  (* : forall P : Assertion, P |-- True *)

Check False_left.
  (* : forall P : Assertion, False |-- P *)

Check EXISTS_left.
  (* : forall P (Q : Assertion),
       (forall x : Z, P x |-- Q) ->
       EXISTS x, P x |-- Q *)

Check EXISTS_right.
  (* : forall (P : Assertion) Q (x : Z),
       P |-- Q x -> P |-- EXISTS x, Q x *)

Check FORALL_left.
  (* : forall P (Q : Assertion) (x : Z),
       P x |-- Q -> FORALL x0, P x0 |-- Q *)

Check FORALL_right.
  (* : forall (P : Assertion) Q,
       (forall x : Z, P |-- Q x) ->
       P |-- FORALL x, Q x *)

Check derives_refl.
  (* : forall P : Assertion, P |-- P *)

Check derives_trans.
  (* : forall P Q R : Assertion,
       P |-- Q -> Q |-- R -> P |-- R *)

Local Instance X: var := new_var().

Fact example: 0 <= {[ X ]} AND {[ X ]} < 100 |-- {[ X ]} < 100 AND 0 <= {[ X ]}.
Proof.
  apply AND_right.
  + apply AND_left2.
    apply derives_refl.
  + apply AND_left1.
    apply derives_refl.
Qed.

End assertion_FOL.
  
(** The following example is about the slow division program. We will show
different proof techniques in this example. *)

Module slow_div.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

Lemma derivation1: forall m n: Z,
  0 <= m AND {[X]} = m AND {[Y]} = 0 |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]}.
Proof.
  intros.
  entailer.
  intros.
  nia.
Qed.

Lemma derivation2: forall m n: Z,
  EXISTS z, n * {[Y]} + z = m AND 0 <= z AND n <= z AND {[X]} = z - n |--
  n * {[Y]} + {[X]} + n = m AND 0 <= {[X]}.
Proof.
  intros.
  apply EXISTS_left.
  intros.
  entailer.
  intros.
  lia.
Qed.

Lemma derivation3: forall m n: Z,
  EXISTS z, n * z + {[X]} + n = m AND 0 <= {[X]} AND {[Y]} = z + 1 |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]}.
Proof.
  intros.
  entailer.
  intros.
  destruct H as [k ?].
  nia.
Qed.

Lemma derivation4: forall m n: Z,
  n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} |--
  n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n.
Proof.
  intros.
  apply AND_right.
  + apply AND_left1.
    apply derives_refl.
  + apply AND_left2.
    entailer.
    intros.
    lia.
Qed.

Fact slow_div_correct: forall m n: Z,
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
  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.
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

End slow_div.

(* Tue Mar 17 01:26:50 CST 2020 *)
