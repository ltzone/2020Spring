Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Open Scope Z.

(* ################################################################# *)
(** * Hoare Logic *)

(** In the last lecture, we introduced a denotational semantics and a small
step semantics for a programming language with possible run time error and
nondeterministic behavior. This time, we complete this part of material by
a Hoare logic for it. *)

(* ================================================================= *)
(** ** The meaning of a Hoare triple *)

(** Originally, we use a Hoare triple [ {{ P }} c {{ Q }} ] to claim: if
command [c] is started in a state satisfying assertion [P], and if [c]
eventually terminates, then the ending state will satisfy assertion [Q]. Now,
since run-time-error and nondeterminism are taken into consideration, we
modify its meaning as follows:

      - If command [c] is started in a state satisfying assertion [P],
        its execution is always safe. In addition, if it terminates, the
        ending state should satisfy [Q].

There are two key points in this statement. (1) As long as the precondition
holds, the execution is run-time-error free, no matter what choices are made at
every nondeterministic point. (2) As long as the precondition holds and the
execution terminates, the ending state satisfies the postcondition, no matter
what choices are made at every nondeterministic point. *)

(* ================================================================= *)
(** ** Unchanged rules *)

(** It might be surprising that some Hoare logic proof rules do not need to be
changed even though we modify Hoare triple's meaning.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

We can check them one by one and see whether they are actually sound. *)

(* ================================================================= *)
(** ** Rules with evaluation *)

(** Assignment commands, if commands and while commands are all related to
expression evaluation. In the following proof rules, an assertion with form
[Safe(E)] says "evaluating [E] is safe".

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P AND Safe(b) }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  P |-- Safe(b) ->
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_asgn_fwd : forall P (X: var) E,
  {{ P AND Safe(E) }}
      X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} == {[ E [X |-> x] ]} }}.

Axiom hoare_asgn_bwd : forall P (X: var) E,
  {{ P [ X |-> E] AND Safe(E) }} X ::= E {{ P }}.

Those additional conjuncts in preconditions are necessary because Hoare triples
ensure safe execution now. *)

(* ################################################################# *)
(** * Type Safe Language *)

(** Run time errors are harmful. Typical run-time-errors caused by careless
coding includes arithmetic error, dangling pointer, no initialized value etc.
For decades, computer scientist attempts to design programming languages that
is safe by syntax. Consider the following expressions. *)

Definition var: Type := nat.

Definition state: Type := var -> Z.

Open Scope Z.

Inductive mexp : Type :=
  | MNum (n : Z)
  | MId (X : var)
  | MPlus (a1 a2 : mexp)
  | MMinus (a1 a2 : mexp)
  | MMult (a1 a2 : mexp)
  | MTrue
  | MFalse
  | MEq (a1 a2 : mexp)
  | MLe (a1 a2 : mexp)
  | MNot (b : mexp)
  | MAnd (b1 b2 : mexp)
.

(** Here, boolean operators and integer operators are allowed to appear in one
single expression. For casting between integers and boolean values, we assume:

      - boolean values will be cast to 0 and 1 when necessary;

      - integers cannot be treated as booleans.

Based on these assumptions, we can formalize its denotational semantics as
follows: *)

Inductive val: Type :=
| Vint (n: Z)
| Vbool (b: bool).

Definition val2Z (v: val): Z :=
  match v with
  | Vint n => n
  | Vbool true => 1
  | Vbool false => 0
  end.

Inductive meval : mexp -> state -> val -> Prop :=
  | E_MNum n st:
      meval (MNum n) st (Vint n)
  | E_MId X st:
      meval (MId X) st (Vint (st X))
  | E_MPlus (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MPlus e1 e2) st (Vint (val2Z v1 + val2Z v2))
  | E_MMinus (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MMinus e1 e2) st (Vint (val2Z v1 - val2Z v2))
  | E_MMult (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MMult e1 e2) st (Vint (val2Z v1 * val2Z v2))
  | E_MTrue st:
      meval MTrue st (Vbool true)
  | E_MFalse st:
      meval MFalse st (Vbool false)
  | E_MEqTrue (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 = val2Z v2) :
      meval (MEq e1 e2) st (Vbool true)
  | E_MEqFalse (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 <> val2Z v2) :
      meval (MEq e1 e2) st (Vbool false)
  | E_MLeTrue (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 < val2Z v2) :
      meval (MLe e1 e2) st (Vbool true)
  | E_MLeFalse (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 >= val2Z v2) :
      meval (MLe e1 e2) st (Vbool false)
  | E_MNot (e: mexp) (b: bool) st
      (H1 : meval e st (Vbool b)):
      meval (MNot e) st (Vbool (negb b))
  | E_MAnd (e1 e2: mexp) (b1 b2: bool) st
      (H1 : meval e1 st (Vbool b1))
      (H2 : meval e2 st (Vbool b2)):
      meval (MAnd e1 e2) st (Vbool (andb b1 b2))
      .

(** Also, we can define its small step semantics as follows. *)

Inductive mexp_halt: mexp -> Prop :=
  | MH_num : forall n, mexp_halt (MNum n)
  | MH_true: mexp_halt MTrue
  | MH_false: mexp_halt MFalse.

Inductive bool2Z_step: mexp -> mexp -> Prop :=
  | BZS_True: bool2Z_step MTrue (MNum 1)
  | BZS_False: bool2Z_step MFalse (MNum 0).

Inductive mstep : state -> mexp -> mexp -> Prop :=
  | MS_Id : forall st X,
      mstep st
        (MId X) (MNum (st X))

  | MS_Plus1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MPlus a1 a2) (MPlus a1' a2)
  | MS_Plus2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MPlus a1 a2) (MPlus a1 a2')
  | MS_Plus3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MPlus a1 a2) (MPlus a1' a2)
  | MS_Plus4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MPlus (MNum n1) a2) (MPlus (MNum n1) a2')
  | MS_Plus : forall st n1 n2,
      mstep st
        (MPlus (MNum n1) (MNum n2)) (MNum (n1 + n2))

  | MS_Minus1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MMinus a1 a2) (MMinus a1' a2)
  | MS_Minus2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MMinus a1 a2) (MMinus a1 a2')
  | MS_Minus3 : forall st a1 a1' a2,                   (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MMinus a1 a2) (MMinus a1' a2)
  | MS_Minus4 : forall st n1 a2 a2',                   (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MMinus (MNum n1) a2) (MMinus (MNum n1) a2')
  | MS_Minus : forall st n1 n2,
      mstep st
        (MMinus (MNum n1) (MNum n2)) (MNum (n1 - n2))

  | MS_Mult1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MMult a1 a2) (MMult a1' a2)
  | MS_Mult2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MMult a1 a2) (MMult a1 a2')
  | MS_Mult3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MMult a1 a2) (MMult a1' a2)
  | MS_Mult4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MMult (MNum n1) a2) (MMult (MNum n1) a2')
  | MS_Mult : forall st n1 n2,
      mstep st
        (MMult (MNum n1) (MNum n2)) (MNum (n1 * n2))

  | MS_Eq1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MEq a1 a2) (MEq a1' a2)
  | MS_Eq2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MEq a1 a2) (MEq a1 a2')
  | MS_Eq3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MEq a1 a2) (MEq a1' a2)
  | MS_Eq4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MEq (MNum n1) a2) (MEq (MNum n1) a2')
  | MS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      mstep st
        (MEq (MNum n1) (MNum n2)) MTrue
  | MS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      mstep st
        (MEq (MNum n1) (MNum n2)) MFalse

  | MS_Le1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MLe a1 a2) (MLe a1' a2)
  | MS_Le2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MLe a1 a2) (MLe a1 a2')
  | MS_Le3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MLe a1 a2) (MLe a1' a2)
  | MS_Le4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MLe (MNum n1) a2) (MLe (MNum n1) a2')
  | MS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      mstep st
        (MLe (MNum n1) (MNum n2)) MTrue
  | MS_Le_False : forall st n1 n2,
      n1 > n2 ->
      mstep st
        (MLe (MNum n1) (MNum n2)) MFalse

  | MS_NotStep : forall st b1 b1',
      mstep st
        b1 b1' ->
      mstep st
        (MNot b1) (MNot b1')
  | MS_NotTrue : forall st,
      mstep st
        (MNot MTrue) MFalse
  | MS_NotFalse : forall st,
      mstep st
        (MNot MFalse) MTrue

  | MS_AndStep : forall st b1 b1' b2,
      mstep st
        b1 b1' ->
      mstep st
       (MAnd b1 b2) (MAnd b1' b2)
  | MS_AndTrue : forall st b,
      mstep st
       (MAnd MTrue b) b
  | MS_AndFalse : forall st b,
      mstep st
       (MAnd MFalse b) MFalse.

(** Till now, everything is not very interesting. We have learnt how to define
denotational semantics and small step semantics of expression evaluation with
potential run time error.

But this time, we can do more. We can determine whether an expression can be
safely evaluated only by its syntax -- it does not depent on the program state.

The following function is a decision procedure. *)

Inductive type_check_result:Type :=
| TCR_int
| TCR_bool
| TCR_illegal.

Fixpoint type_check (m: mexp): type_check_result :=
  match m with
  | MNum _
  | MId _          =>

        TCR_int

  | MPlus m1 m2
  | MMinus m1 m2
  | MMult m1 m2    =>

        match type_check m1, type_check m2 with
        | TCR_illegal, _ => TCR_illegal
        | _, TCR_illegal => TCR_illegal
        | _, _           => TCR_int
        end

  | MTrue
  | MFalse         =>

        TCR_bool

  | MEq m1 m2
  | MLe m1 m2      =>

        match type_check m1, type_check m2 with
        | TCR_illegal, _ => TCR_illegal
        | _, TCR_illegal => TCR_illegal
        | _, _           => TCR_bool
        end

  | MNot m1        =>

        match type_check m1 with
        | TCR_bool => TCR_bool
        | _        => TCR_illegal
        end

  | MAnd m1 m2     =>

        match type_check m1, type_check m2 with
        | TCR_bool, TCR_bool => TCR_bool
        | _, _               => TCR_illegal
        end

  end
.

(** That means, we can check whether an [mexp] expression is legal in
compilation time. *)

(* ################################################################# *)
(** * Progress *)

(** How to justify that every [mexp] expression that passes [type_check] is
safe to evaluate? There are two important theorems: _progress_ and
_preservation_.

"Progress" says every [mexp] that passes [type_check] will either take a step
to evaluate or is already a constant. *)

Lemma mexp_halt_fact: forall m,
  mexp_halt m ->
  exists n, bool2Z_step m (MNum n) \/ m = MNum n.
Proof.
  intros.
  inversion H; subst.
  + exists n.
    right.
    reflexivity.
  + exists 1.
    left.
    apply BZS_True.
  + exists 0.
    left.
    apply BZS_False.
Qed.

Lemma mexp_halt_bool_fact: forall m,
  mexp_halt m ->
  type_check m = TCR_bool ->
  m = MTrue \/ m = MFalse.
Proof.
  intros.
  inversion H; subst.
  + simpl in H0.
    discriminate H0.
  + left.
    reflexivity.
  + right.
    reflexivity.
Qed.

Theorem Progress: forall m st,
  type_check m <> TCR_illegal ->
  (exists m', mstep st m m') \/ mexp_halt m.
Proof.
  intros.
  induction m.
  + right.
    apply MH_num.
  + left.
    exists (MNum (st X)).
    apply MS_Id.
  + assert (type_check m1 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H0 in H.
      apply H; reflexivity.
    }
    assert (type_check m2 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H1 in H.
      destruct (type_check m1); apply H; reflexivity.
    }
    specialize (IHm1 H0).
    specialize (IHm2 H1).
    clear H H0 H1.
    destruct IHm1 as [[m1' ?] |].
    {
      left.
      exists (MPlus m1' m2).
      apply MS_Plus1.
      exact H.
    }
    destruct IHm2 as [[m2' ?] |].
    {
      left.
      exists (MPlus m1 m2').
      apply MS_Plus2.
      - exact H.
      - exact H0.
    }
    apply mexp_halt_fact in H.
    destruct H as [n1 [? | ?]].
    {
      left.
      exists (MPlus (MNum n1) m2).
      apply MS_Plus3.
      - exact H0.
      - exact H.
    }
    subst m1.
    apply mexp_halt_fact in H0.
    destruct H0 as [n2 [? | ?]].
    {
      left.
      exists (MPlus (MNum n1) (MNum n2)).
      apply MS_Plus4.
      exact H.
    }
    {
      subst m2.
      left.
      exists (MNum (n1 + n2)).
      apply MS_Plus.
    }
  + assert (type_check m1 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H0 in H.
      apply H; reflexivity.
    }
    assert (type_check m2 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H1 in H.
      destruct (type_check m1); apply H; reflexivity.
    }
    specialize (IHm1 H0).
    specialize (IHm2 H1).
    clear H H0 H1.
    destruct IHm1 as [[m1' ?] |].
    {
      left.
      exists (MMinus m1' m2).
      apply MS_Minus1.
      exact H.
    }
    destruct IHm2 as [[m2' ?] |].
    {
      left.
      exists (MMinus m1 m2').
      apply MS_Minus2.
      - exact H.
      - exact H0.
    }
    apply mexp_halt_fact in H.
    destruct H as [n1 [? | ?]].
    {
      left.
      exists (MMinus (MNum n1) m2).
      apply MS_Minus3.
      - exact H0.
      - exact H.
    }
    subst m1.
    apply mexp_halt_fact in H0.
    destruct H0 as [n2 [? | ?]].
    {
      left.
      exists (MMinus (MNum n1) (MNum n2)).
      apply MS_Minus4.
      exact H.
    }
    {
      subst m2.
      left.
      exists (MNum (n1 - n2)).
      apply MS_Minus.
    }
  + assert (type_check m1 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H0 in H.
      apply H; reflexivity.
    }
    assert (type_check m2 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H1 in H.
      destruct (type_check m1); apply H; reflexivity.
    }
    specialize (IHm1 H0).
    specialize (IHm2 H1).
    clear H H0 H1.
    destruct IHm1 as [[m1' ?] |].
    {
      left.
      exists (MMult m1' m2).
      apply MS_Mult1.
      exact H.
    }
    destruct IHm2 as [[m2' ?] |].
    {
      left.
      exists (MMult m1 m2').
      apply MS_Mult2.
      - exact H.
      - exact H0.
    }
    apply mexp_halt_fact in H.
    destruct H as [n1 [? | ?]].
    {
      left.
      exists (MMult (MNum n1) m2).
      apply MS_Mult3.
      - exact H0.
      - exact H.
    }
    subst m1.
    apply mexp_halt_fact in H0.
    destruct H0 as [n2 [? | ?]].
    {
      left.
      exists (MMult (MNum n1) (MNum n2)).
      apply MS_Mult4.
      exact H.
    }
    {
      subst m2.
      left.
      exists (MNum (n1 * n2)).
      apply MS_Mult.
    }
  + right.
    apply MH_true.
  + right.
    apply MH_false.
  + assert (type_check m1 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H0 in H.
      apply H; reflexivity.
    }
    assert (type_check m2 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H1 in H.
      destruct (type_check m1); apply H; reflexivity.
    }
    specialize (IHm1 H0).
    specialize (IHm2 H1).
    clear H H0 H1.
    destruct IHm1 as [[m1' ?] |].
    {
      left.
      exists (MEq m1' m2).
      apply MS_Eq1.
      exact H.
    }
    destruct IHm2 as [[m2' ?] |].
    {
      left.
      exists (MEq m1 m2').
      apply MS_Eq2.
      - exact H.
      - exact H0.
    }
    apply mexp_halt_fact in H.
    destruct H as [n1 [? | ?]].
    {
      left.
      exists (MEq (MNum n1) m2).
      apply MS_Eq3.
      - exact H0.
      - exact H.
    }
    subst m1.
    apply mexp_halt_fact in H0.
    destruct H0 as [n2 [? | ?]].
    {
      left.
      exists (MEq (MNum n1) (MNum n2)).
      apply MS_Eq4.
      exact H.
    }
    {
      subst m2.
      left.
      destruct (Z.eq_dec n1 n2).
      - exists MTrue.
        apply MS_Eq_True.
        exact e.
      - exists MFalse.
        apply MS_Eq_False.
        exact n.
    }
  + assert (type_check m1 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H0 in H.
      apply H; reflexivity.
    }
    assert (type_check m2 <> TCR_illegal).
    {
      simpl in H.
      intro.
      rewrite H1 in H.
      destruct (type_check m1); apply H; reflexivity.
    }
    specialize (IHm1 H0).
    specialize (IHm2 H1).
    clear H H0 H1.
    destruct IHm1 as [[m1' ?] |].
    {
      left.
      exists (MLe m1' m2).
      apply MS_Le1.
      exact H.
    }
    destruct IHm2 as [[m2' ?] |].
    {
      left.
      exists (MLe m1 m2').
      apply MS_Le2.
      - exact H.
      - exact H0.
    }
    apply mexp_halt_fact in H.
    destruct H as [n1 [? | ?]].
    {
      left.
      exists (MLe (MNum n1) m2).
      apply MS_Le3.
      - exact H0.
      - exact H.
    }
    subst m1.
    apply mexp_halt_fact in H0.
    destruct H0 as [n2 [? | ?]].
    {
      left.
      exists (MLe (MNum n1) (MNum n2)).
      apply MS_Le4.
      exact H.
    }
    {
      subst m2.
      left.
      destruct (Z_le_gt_dec n1 n2).
      - exists MTrue.
        apply MS_Le_True.
        exact l.
      - exists MFalse.
        apply MS_Le_False.
        exact g.
    }
  + assert (type_check m = TCR_bool).
    {
      simpl in H.
      destruct (type_check m).
      - exfalso; apply H; reflexivity.
      - reflexivity.
      - exfalso; apply H; reflexivity.
    }
    assert (type_check m <> TCR_illegal).
    {
      rewrite H0; intro.
      discriminate H1.
    }
    specialize (IHm H1).
    clear H H1.
    destruct IHm as [[m' ?] | ?].
    {
      left.
      exists (MNot m').
      apply MS_NotStep.
      exact H.
    }
    pose proof mexp_halt_bool_fact _  H H0.
    destruct H1; subst.
    {
      left.
      exists MFalse.
      apply MS_NotTrue.
    }
    {
      left.
      exists MTrue.
      apply MS_NotFalse.
    }
  + assert (type_check m1 = TCR_bool).
    {
      simpl in H.
      destruct (type_check m1).
      - exfalso; apply H; reflexivity.
      - reflexivity.
      - exfalso; apply H; reflexivity.
    }
    assert (type_check m1 <> TCR_illegal).
    {
      rewrite H0; intro.
      discriminate H1.
    }
    specialize (IHm1 H1).
    clear H H1 IHm2.
    destruct IHm1 as [[m1' ?] | ?].
    {
      left.
      exists (MAnd m1' m2).
      apply MS_AndStep.
      exact H.
    }
    pose proof mexp_halt_bool_fact _  H H0.
    destruct H1; subst.
    {
      left.
      exists m2.
      apply MS_AndTrue.
    }
    {
      left.
      exists MFalse.
      apply MS_AndFalse.
    }
Qed.

(* ################################################################# *)
(** * Preservation *)

(** "Preservation" says: if an [mexp] type checks then it will only step to
type-checked another expression. *)

Lemma bool2Z_step_fact: forall m1 m2,
  bool2Z_step m1 m2 ->
  type_check m1 = TCR_bool /\ type_check m2 = TCR_int.
Proof.
  intros.
  inversion H; subst.
  + split; reflexivity.
  + split; reflexivity.
Qed.

Lemma Preservation_aux: forall st m1 m2,
  mstep st m1 m2 ->
  type_check m1 <> TCR_illegal ->
  type_check m1 = type_check m2.
Proof.
  intros.
  rename H0 into TC.
  induction H.
  + simpl in TC.
    simpl.
    reflexivity.
  + assert (type_check a1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + assert (type_check a2 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H1 in TC.
      destruct (type_check a1); apply TC; reflexivity.
    }
    specialize (IHmstep H1).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H0.
    destruct H0.
    rewrite H0, H1.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H.
    destruct H.
    rewrite H, H0.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check a1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + assert (type_check a2 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H1 in TC.
      destruct (type_check a1); apply TC; reflexivity.
    }
    specialize (IHmstep H1).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H0.
    destruct H0.
    rewrite H0, H1.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H.
    destruct H.
    rewrite H, H0.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check a1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + assert (type_check a2 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H1 in TC.
      destruct (type_check a1); apply TC; reflexivity.
    }
    specialize (IHmstep H1).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H0.
    destruct H0.
    rewrite H0, H1.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H.
    destruct H.
    rewrite H, H0.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check a1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + assert (type_check a2 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H1 in TC.
      destruct (type_check a1); apply TC; reflexivity.
    }
    specialize (IHmstep H1).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H0.
    destruct H0.
    rewrite H0, H1.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H.
    destruct H.
    rewrite H, H0.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check a1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + assert (type_check a2 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H1 in TC.
      destruct (type_check a1); apply TC; reflexivity.
    }
    specialize (IHmstep H1).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H0.
    destruct H0.
    rewrite H0, H1.
    reflexivity.
  + simpl.
    apply bool2Z_step_fact in H.
    destruct H.
    rewrite H, H0.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check b1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
  + assert (type_check b1 <> TCR_illegal).
    {
      simpl in TC.
      intro.
      rewrite H0 in TC.
      apply TC; reflexivity.
    }
    specialize (IHmstep H0).
    simpl.
    rewrite IHmstep.
    reflexivity.
  + simpl.
    simpl in TC.
    destruct (type_check b).
    - exfalso. apply TC. reflexivity.
    - reflexivity.
    - reflexivity.
  + simpl.
    simpl in TC.
    destruct (type_check b).
    - exfalso. apply TC. reflexivity.
    - reflexivity.
    - exfalso. apply TC. reflexivity.
Qed.

Theorem Preservation: forall st m1 m2,
  mstep st m1 m2 ->
  type_check m1 <> TCR_illegal ->
  type_check m2 <> TCR_illegal.
Proof.
  intros.
  pose proof Preservation_aux _ _ _ H H0.
  rewrite <- H1.
  exact H0.
Qed.

(* Tue May 19 13:37:57 CST 2020 *)
