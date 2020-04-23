Require Import PL.Imp3.
Import Assertion_D.
Import Abstract_Pretty_Printing.

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

Definition FOL_complete (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_valid P -> FOL_provable P.

(* ################################################################# *)
(** * Choices of Proof Rules *)

(** We have roved the soundness and completeness of Hoare logic, if its
    underlying assertion derivation logic is sound and complete.

    Now it is time to ask: is the set of Hoare logic proof rules our unique
    choice? For example, can we choose the forward assignment rule instead of
    the backward one? Are other useful proof rules better candidates? In order
    to answer these questions, the key point is whether other proof rules also
    preserves Hoare triples' validity. We will show some preservation proof and
    demonstrate the relation between these candidates and our Hoare logic.

    We assume that the underlying FOL is sound and complete. *)

Section HoareLogic.

Variable T: FirstOrderLogic.

Hypothesis T_sound: FOL_sound T.

Hypothesis T_complete: FOL_complete T.

(** A sound and complete FOL has some basic properties. *)

Theorem TrivialFOL_complete_der: forall P Q,
  FOL_valid (P IMPLY Q) ->
  P |-- Q.
Proof.
  intros.
  apply T_complete, H.
Qed.

Theorem TrivialFOL_sound_der: forall P Q,
  P |-- Q ->
  FOL_valid (P IMPLY Q).
Proof.
  intros.
  apply T_sound, H.
Qed.

Theorem derives_refl: forall P, P |-- P.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  unfold FOL_valid.
  intros.
  simpl.
  tauto.
Qed.

Theorem AND_derives: forall P1 Q1 P2 Q2,
  P1 |-- P2 ->
  Q1 |-- Q2 ->
  P1 AND Q1 |-- P2 AND Q2.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  apply TrivialFOL_sound_der in H.
  apply TrivialFOL_sound_der in H0.
  unfold FOL_valid.
  unfold FOL_valid in H.
  unfold FOL_valid in H0.
  intros.
  specialize (H J).
  specialize (H0 J).
  simpl.
  simpl in H.
  simpl in H0.
  tauto.
Qed.

(* ================================================================= *)
(** ** Soundness of the forward assignment rule *)

(** We need some additional properties about syntactic substitution in our
proof. *)

Check aexp_sub_spec.

(* aexp_sub_spec:
  forall st1 st2 La (a: aexp') (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  aexp'_denote (st1, La) (a [X |-> E]) = aexp'_denote (st2, La) a. *)

Check no_occ_satisfies.

(* no_occ_satisfies: forall st La P x v,
  assn_free_occur x P = O ->
  ((st, La) |== P <-> (st, Lassn_update La x v) |== P). *)

Check Assertion_sub_spec.

(* Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P). *)

(** The soundness proof is straightforwad. *)

Lemma hoare_asgn_fwd_sound : forall P (X: var) (x: logical_var) (E: aexp),
  assn_free_occur x P = O ->
  |== {{ P }}
        X ::= E
      {{ EXISTS x, P [X |-> x] AND
                   {[X]} = {[ E [X |-> x] ]} }}.
Proof.
  unfold valid.
  intros.
  simpl in H1.
  destruct H1.
  pose proof aeval_aexp'_denote st1 La E.
  simpl.
  exists (st1 X).
  assert (forall Y : var, X <> Y -> st2 Y = st1 Y).
  {
    intros.
    rewrite H2 by tauto.
    reflexivity.
  }
  clear H2; rename H4 into H2.
  split.
  + unfold Interp_Lupdate.
    simpl.
    apply Assertion_sub_spec with st1.
    - simpl.
      unfold Lassn_update.
      destruct (Nat.eq_dec x x).
      * reflexivity.
      * exfalso; apply n; reflexivity.
    - exact H2.
    - apply no_occ_satisfies.
      * exact H.
      * exact H0.
  + unfold Interp_Lupdate; simpl.
    erewrite aexp_sub_spec; [| | exact H2].
    - rewrite <- aeval_aexp'_denote in H3.
      rewrite <- aeval_aexp'_denote.
      exact H1.
    - simpl.
      unfold Lassn_update.
      destruct (Nat.eq_dec x x).
      * reflexivity.
      * exfalso; apply n; reflexivity.
Qed.

(* ================================================================= *)
(** ** Soundness of sequential composition's associativity *)

Import Relation_Operators.

(** We first prove that [(c1;;c2);;c3] is equivalent with [c1;;(c2;;c3)] via
    the denotational semantics. *)

Lemma concat_assoc: forall R1 R2 R3: state -> state -> Prop,
  Rel.equiv
    (concat (concat R1 R2) R3)
    (concat R1 (concat R2 R3)).
Proof.
  unfold Rel.equiv, concat.
  intros; split; intros.
  + destruct H as [b' [[a' [? ?]] ?]].
    exists a'.
    split; [tauto |].
    exists b'.
    tauto.
  + destruct H as [a' [? [b' [? ?]]]].
    exists b'.
    split; [| tauto].
    exists a'.
    tauto.
Qed.

Lemma seq_assoc : forall c1 c2 c3,
  com_equiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  unfold com_equiv.
  rewrite ! ceval_CSeq.
  apply concat_assoc.
Qed.

(** Based on this, we can prove its Hoare logic counterpart sound. *)

Lemma seq_assoc_sound : forall P c1 c2 c3 Q,
  |== {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |== {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
Proof.
  unfold valid.
  intros.
  pose proof seq_assoc c1 c2 c3.
  unfold com_equiv, Rel.equiv in H.
  split; intros.
  + specialize (H0 La st1 st2).
    apply H0.
    - exact H1.
    - apply H.
      exact H2.
  + specialize (H0 La st1 st2).
    apply H0.
    - exact H1.
    - apply H.
      exact H2.
Qed.

(* ================================================================= *)
(** ** Deriving single-sided consequence rules *)

(** Recall that if a proof rule can be derived from primary rules, it is called
a derived rule. For example, we can derive the single side consequence rule
from the two sided version. Remark: [TrivialFOL] is implicitly claimed as the
underlying logic for assertion derivation here. Coq does this automatically
because [FirstOrderLogic] is a type class and [TrivialFOL] is one of its
instances. Coq does such auto filling for all type classes' instances. *)

Lemma hoare_consequence_pre: forall P P' c Q,
  P |-- P' ->
  |-- {{ P' }} c {{ Q }} ->
  |-- {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + apply derives_refl.
    (** Here, we use the fact that the underlying FOL is [TrivialFOL]. *)
Qed.

Lemma hoare_consequence_post: forall P c Q Q',
  |-- {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  |-- {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + exact H.
  + exact H0.
Qed.

(* ================================================================= *)
(** ** Deriving the forward assignment rule *)

(** Now we try to derive the forward assigement rule from our Hoare logic. Our
proof needs the following program state construction. *)

Print state_update.

(** The following statement reminds us that we are proving things about a
logic but not proving things using a Hoare logic. When we use a Hoare logic
to prove program correctness, we simply use Coq variables to represent logical
variables and use Coq's integer terms to represent integer constants. Now, we
established a formal definition of syntax trees with all of these features.
Thus, we need to add extra assumptions like "x does not freely occur in P" to
ensure that the existentially quantified variable [x] only appears in the scope
of that existential quantifier. *)

Lemma hoare_asgn_fwd_der : forall P (X: var) (x: logical_var) (E: aexp),
  assn_free_occur x P = O ->
  |-- {{ P }}
        X ::= E
      {{ EXISTS x, P [X |-> x] AND
                   {[X]} = {[ E [X |-> x] ]} }}.
Proof.
  intros.
  eapply hoare_consequence_pre; [| apply hoare_asgn_bwd].
  (** In short, the forward assignment rule can be derived by
  a combination of the backward assignment rule and the
  consequence rule. To complete the proof, we need to prove
  this assertion derivation.*)
  apply TrivialFOL_complete_der.
  unfold FOL_valid.
  intros.
  destruct J as [st La].
  simpl.
  pose proof classic ((st, La) |== P).
  destruct H0; [right | left; exact H0].
  (** After these lines of transformation, we only need to prove
  that: as long as [P] is satisfied,
  [[
    (EXISTS x, P [X |-> x] AND {[X]} == {[E [X |-> x]]}) [X |-> E]
  ]]
  is satisfied. *)
  pose proof state_update_spec st X (aeval E st).
  destruct H1.
  apply Assertion_sub_spec with (state_update st X (aeval E st)).
  { rewrite <- aeval_aexp'_denote. exact H1. }
  { exact H2. }
  (** Here, we turn syntactic substitution into program state
  update using [Assertion_sub_spec]. *)
  simpl.
  (** This [simpl] unfolds the semantic definition of [EXISTS],
  [AND] and equality in the assertion language. *)
  exists (st X).
  pose proof Lassn_update_spec La x (st X).
  destruct H3.
  split.
  + unfold Interp_Lupdate; simpl.
    (** Again, in order to prove that [P[X |-> x]] is satisfied,
    we only need to prove that [P] is satisfied on a modified
    program state. *)
    apply Assertion_sub_spec with st.
    { simpl. rewrite H3. reflexivity. }
    { intros. specialize (H2 _ H5). rewrite H2; reflexivity. }
    clear H1 H2 H3 H4.
    (** Now, we want to prove the conclusion from [H0]. This is
    easy since we know that [x] does not freely occur in [P] and
    two interpretations in [H0] and the conclusion only differ
    in [x]'s value. *)
    apply no_occ_satisfies; tauto.
  + rewrite H1.
    unfold Interp_Lupdate; simpl.
    (** Now the equation's right hand side is the denotation of
    [E [X |-> x]], it is equivalent with [E]'s denotation on a
    modified program state. This property is described by
    [aexp_sub_spec]. *)
    assert (aexp'_denote
             (state_update st X (aeval E st), Lassn_update La x (st X))
             (E [X |-> x]) = 
            aexp'_denote (st, Lassn_update La x (st X)) E).
    {
      apply aexp_sub_spec.
      { simpl. rewrite H3. reflexivity. }
      { intros. specialize (H2 _ H5). rewrite H2. reflexivity. }
    }
    rewrite H5.
    (** Then, the residue proof goal is trivial. *)
    rewrite <- aeval_aexp'_denote.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Inversion of Sequence Rule *)

(** When we derive [hoare_consequence_pre], we actually prove such a meta
theorem:

    If {{ P' }} c {{ Q }} is provable and P' |-- P
    then {{ P }} c {{ Q }} is also provable.

In other words, we prove that if there is a proof tree for the former Hoare
triple, we can always construct another proof tree for the latter one. Here
is a brief illustration:

    Assumption:

      *- - - - - - - - -*
      |                 |
      | Some Proof Tree |
      |                 |
      *- - - - - - - - -*
      {{ P' }} c {{ Q }}          P' |-- P

    Conclusion:

    *- - - - - - - - - - - - - - - - - - - - - - - - - - - - -*
    |                                                         |
    |  *- - - - - - - - -*           New Proof Tree           |
    |  |                 |                                    |
    |  | Some Proof Tree |                                    |
    |  |                 |                                    |
    |  *- - - - - - - - -*                       -----------  |
    |  {{ P' }} c {{ Q }}           P' |-- P       Q |-- Q    |
    | ------------------------------------------------------  |
    |                   {{ P }} c {{ Q }}                     |
    |                                                         |
    *- - - - - - - - - - - - - - - - - - - - - - - - - - - - -*

Beside such proof tree construction, we can say something more. *)

Lemma hoare_seq_inv: forall P c1 c2 R,
  |-- {{ P }} c1 ;; c2 {{ R }} ->
  exists Q, (|-- {{ P }} c1 {{ Q }}) /\ (|-- {{ Q }} c2 {{ R }}).
(** This lemma says, if [ {{ P }} c1;; c2 {{ R }} ] is provable, then we can
always find a middle condition [Q]. It is worth noticing that the proof tree
for [ {{ P }} c1;; c2 {{ R }} ] does not necessarily have the following form:

    *- - - - - - - - - - - - - - - - - - - - - - - - - - - - -*
    |                                                         |
    |  *- - - - - - - - -*         *- - - - - - - - -*        |
    |  |                 |         |                 |        |
    |  | Some Proof Tree |         | Some Proof Tree |        |
    |  |                 |         |                 |        |
    |  *- - - - - - - - -*         *- - - - - - - - -*        |
    |  {{ P }} c1 {{ Q }}           {{ Q }} c2 {{ R }}        |
    | ------------------------------------------------------  |
    |               {{ P }} c1;; c2 {{ Q }}                   |
    |                                                         |
    *- - - - - - - - - - - - - - - - - - - - - - - - - - - - -*

because the last step in the proof might not be [hoare_seq]. It can also be
[hoare_consequence]. This lemma says: even if the last step in the proof is
not [hoare_seq], we can always find such an assertion [Q] and reconstruct proof
trees for [ {{ P }} c1 {{ Q }} ] and [ {{ Q }} c2 {{ R }} ]. *)
Proof.
  intros.
  remember ({{P}} c1;; c2 {{R}}) as Tr.
  revert P c1 c2 R HeqTr; induction H; intros.
  + injection HeqTr as ?H ?H ?H; subst.
    exists Q.
    tauto.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ?H ?H ?H; subst.
    assert (({{P'}} c1;; c2 {{Q'}}) = ({{P'}} c1;; c2 {{Q'}})) by reflexivity.
    specialize (IHprovable P' c1 c2 Q' H2); clear H2.
    destruct IHprovable as [Q [? ?]].
    exists Q.
    split.
    - eapply hoare_consequence_pre.
      * exact H.
      * exact H2.
    - eapply hoare_consequence_post.
      * exact H3.
      * exact H1.
Qed.

(* ================================================================= *)
(** ** Associativity *)

(** The following lemma is more interesting. It says: we can always rebuild a
proof tree for [ {{ P }} (c1 ;; c2) ;; c3 {{ Q }} ] if we discover the internal
structure of a [ {{ P }} c1 ;; c2 ;; c3 {{ Q }} ]'s proof tree (and vise
versa). *)

Lemma seq_assoc_der : forall P c1 c2 c3 Q,
  |-- {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |-- {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
Proof.
  intros.
  split; intros.
  + apply hoare_seq_inv in H.
    destruct H as [P1 [? ?]].
    apply hoare_seq_inv in H0.
    destruct H0 as [P2 [? ?]].
    apply hoare_seq with P2.
    - apply hoare_seq with P1.
      * exact H.
      * exact H0.
    - exact H1.
  + apply hoare_seq_inv in H.
    destruct H as [P2 [? ?]].
    apply hoare_seq_inv in H.
    destruct H as [P1 [? ?]].
    apply hoare_seq with P1.
    - exact H.
    - apply hoare_seq with P2.
      * exact H1.
      * exact H0.
Qed.

(* ================================================================= *)
(** ** If And Sequence *)

(** Very similarly, we can prove the following facts about Hoare logic proof
trees for if-commands. *)

Lemma hoare_if_inv: forall P b c1 c2 Q,
  |-- {{P}} If b Then c1 Else c2 EndIf {{Q}} ->
  (|-- {{ P  AND {[b]} }} c1 {{Q}}) /\
  (|-- {{ P  AND NOT {[b]} }} c2 {{Q}}).
Proof.
  intros.
  remember ({{P}} If b Then c1 Else c2 EndIf {{Q}}) as Tr.
  revert P b c1 c2 Q HeqTr; induction H; intros.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ? ? ?; subst.
    clear IHprovable1 IHprovable2.
    tauto.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ?; subst.
    assert ({{P'}} If b Then c1 Else c2 EndIf {{Q'}} = 
            {{P'}} If b Then c1 Else c2 EndIf {{Q'}}).
    { reflexivity. }
    pose proof IHprovable _ _ _ _ _ H2; clear IHprovable H2.
    destruct H3.
    split.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H2.
      * apply H1.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H3.
      * apply H1.
Qed.

Lemma if_seq_der : forall P b c1 c2 c3 Q,
  |-- {{ P }} If b Then c1 Else c2 EndIf;; c3 {{ Q }} ->
  |-- {{ P }} If b Then c1;; c3 Else c2;; c3 EndIf {{ Q }}.
Proof.
  intros.
  apply hoare_seq_inv in H.
  destruct H as [Q' [? ?]].
  apply hoare_if_inv in H.
  destruct H.
  apply hoare_if.
  + apply hoare_seq with Q'.
    - exact H.
    - exact H0.
  + apply hoare_seq with Q'.
    - exact H1.
    - exact H0.
Qed.

End HoareLogic.

(* ################################################################# *)
(** * General First Order Logic *)

(** Hoare logic's soundness and completeness theorems tell us that the Hoare
triples defined by the logic do precisely express "if the beginning state
satisfies the precondition then the ending state satisfies the postcondition".

For first order logic, we can ask the same question. When we use logical
connectives (like [AND], [OR] and [EXISTS]) in assertions, do those FOL proof
rules precisely describe their meaning? What about arithmetic symbols like
"+", "-" and "<="?

The answer is "yes" for logical connectives. A first order language consists of
logical symbols and nonlogical symbols (relation symbols and function symbols.
Specifically,

    logical variables (v)
    
    function symbols (f)
    
    relation symbols (R)

    t ::= v
        | f t t .. t

    P ::= t = t
        | R t t .. t
        | TRUE
        | FALSE
        | P IMPLY P
        | P AND P
        | P OR P
        | NOT P
        | FORALL v P
        | EXISTS v P

We can formalize this syntax tree as follows. *)

Module General_FOL.

Class Symbol: Type := {
  RS: Type; (* Relation symbol *)
  FS: Type; (* Function symbol *)
  R_ary: RS -> nat;
  F_ary: FS -> nat
}.

(** This defines choices of nonlogical symbols. Every set of function symbols
and relation symbols determins a first order language. *)

Definition logical_var: Type := nat.

Inductive term {s: Symbol}: Type :=
| term_var (v: logical_var): term
| term_constr (t: unfinished_term O): term
with unfinished_term {s: Symbol}: nat -> Type :=
| func (f: FS): unfinished_term (F_ary f)
| fapp {n: nat} (f: unfinished_term (S n)) (x: term): unfinished_term n.

Inductive unfinished_atom_prop {s: Symbol}: nat -> Type :=
| rel (r: RS): unfinished_atom_prop (R_ary r)
| rapp {n: nat} (r: unfinished_atom_prop (S n)) (x: term): unfinished_atom_prop n.

Inductive prop {s: Symbol}: Type :=
| PEq (t1 t2: term): prop
| PAtom (P: unfinished_atom_prop O): prop
| PTrue: prop
| PFalse: prop
| PNot (P: prop): prop
| PImpl (P Q: prop): prop
| PAnd (P Q: prop): prop
| POr (P Q: prop): prop
| PForall (x: logical_var) (P: prop): prop
| PExists (x: logical_var) (P: prop): prop.

End General_FOL.

(** From now on, we will only use one simple first order language for
convenience. This language does not have any function symbol and only has one
binary relation symbol.


    P ::= v = v
        | R v v
        | TRUE
        | FALSE
        | P IMPLY P
        | FORALL v P

*)

Module OneBinRel_FOL.

Definition logical_var: Type := nat.

Inductive term: Type :=
| TId (v: logical_var): term.

Inductive prop: Type :=
| PEq (t1 t2: term): prop
| PRel (t1 t2: term): prop
| PFalse: prop
| PImpl (P Q: prop): prop
| PForall (x: logical_var) (P: prop): prop.

(** Not only the nonlogical symbol set is minimal, the primary logical symbols
of this language is only [IMPLY] and [FALSE]. Other symbols are defined as
derived symbols. *)

Definition PTrue: prop := PImpl PFalse PFalse.
Definition PNot (P: prop): prop := PImpl P PFalse.
Definition PAnd (P Q: prop): prop := PNot (PImpl P (PNot Q)). 
Definition POr (P Q: prop): prop := PImpl (PNot P) Q. 
Definition PExists (x: logical_var) (P: prop): prop :=
  PNot (PForall x (PNot P)).

Bind Scope FOL_scope with prop.
Delimit Scope FOL_scope with FOL.

Coercion TId: logical_var >-> term.
Notation "x = y" := (PEq x y) (at level 70, no associativity) : FOL_scope.
Notation "P1 'OR' P2" := (POr P1 P2) (at level 76, left associativity) : FOL_scope.
Notation "P1 'AND' P2" := (PAnd P1 P2) (at level 74, left associativity) : FOL_scope.
Notation "P1 'IMPLY' P2" := (PImpl P1 P2) (at level 77, right associativity) : FOL_scope.
Notation "'NOT' P" := (PNot P) (at level 73, right associativity) : FOL_scope.
Notation "'EXISTS' x ',' P " := (PExists x ((P)%FOL)) (at level 79,  right associativity) : FOL_scope.
Notation "'FORALL' x ',' P " := (PForall x ((P)%FOL)) (at level 79, right associativity) : FOL_scope.

(** Similar to what we have done in assertion formalization, we can define
syntactic substitution over logical variables as follows. *)

Definition term_rename (x y: logical_var) (t: term) :=
    match t with
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    end.

Fixpoint prop_rename (x y: logical_var) (d: prop): prop :=
    match d with
    | PEq t1 t2    => PEq (term_rename x y t1) (term_rename x y t2)
    | PRel t1 t2   => PRel (term_rename x y t1) (term_rename x y t2)
    | PImpl P1 P2  => PImpl (prop_rename x y P1) (prop_rename x y P2)
    | PFalse       => PFalse
    | PForall x' P => if Nat.eq_dec x x'
                      then PForall x' P
                      else PForall x' (prop_rename x y P)
    end.

Definition term_max_var (t: term): logical_var :=
    match t with
    | TId x => x
    end.

Fixpoint prop_max_var (d: prop): logical_var :=
    match d with
    | PEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | PRel t1 t2   => max (term_max_var t1) (term_max_var t2)
    | PFalse       => O
    | PImpl P1 P2  => max (prop_max_var P1) (prop_max_var P2)
    | PForall x' P => max x' (prop_max_var P)
    end.

Definition new_var (P: prop) (t: term): logical_var :=
  S (max (prop_max_var P) (term_max_var t)).

Definition term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TId x' => if Nat.eq_dec x x' then S O else O
    end.

Fixpoint prop_free_occur (x: logical_var) (d: prop): nat :=
    match d with
    | PEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | PRel t1 t2   => (term_occur x t1) + (term_occur x t2)
    | PFalse       => O
    | PImpl P1 P2  => (prop_free_occur x P1) + (prop_free_occur x P2)
    | PForall x' P => if Nat.eq_dec x x'
                      then O
                      else prop_free_occur x P
    end.

Fixpoint rename_all (t: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq t1 t2
    | PRel t1 t2  => PRel t1 t2
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (rename_all t P1) (rename_all t P2)
    | PForall x P => match term_occur x t with
                        | O => PForall x (rename_all t P)
                        | _ => PForall
                                 (new_var (rename_all t P) t)
                                 (prop_rename x
                                   (new_var (rename_all t P) t)
                                   (rename_all t P))
                        end
    end.

Definition term_sub (x: logical_var) (tx: term) (t: term) :=
    match t with
    | TId x' =>
         if Nat.eq_dec x x'
         then tx
         else TId x'
    end.

Fixpoint naive_sub (x: logical_var) (tx: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq (term_sub x tx t1) (term_sub x tx t2)
    | PRel t1 t2  => PRel (term_sub x tx t1) (term_sub x tx t2)
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (naive_sub x tx P1) (naive_sub x tx P2)
    | PForall x P => PForall x (naive_sub x tx P)
    end.

Definition prop_sub (x: logical_var) (tx: term) (P: prop): prop :=
  naive_sub x tx (rename_all tx P).

Notation "P [ x |-> t ]" := (prop_sub x t ((P)%FOL)) (at level 10, x at next level) : FOL_scope.

(** The we are able to state proof rules of this first order logic. *)

Inductive provable: prop -> Prop :=
| PImply_1: forall P Q, provable (P IMPLY (Q IMPLY P))
| PImply_2: forall P Q R, provable
   ((P IMPLY Q IMPLY R) IMPLY
    (P IMPLY Q) IMPLY
    (P IMPLY R))
| Modus_ponens: forall P Q,
    provable (P IMPLY Q) ->
    provable P ->
    provable Q
| PFalse_elim: forall P,
    provable (PFalse IMPLY P)
| Excluded_middle: forall P,
    provable (NOT P OR P)
| PForall_elim: forall x t P,
    provable ((FORALL x, P) IMPLY (P [x |-> t]))
| PForall_intros: forall x P Q,
    prop_free_occur x P = O ->
    provable (P IMPLY Q) ->
    provable (P IMPLY FORALL x, Q)
| PEq_refl: forall t,
    provable (t = t)
| PEq_sub: forall P x t t',
    provable (t = t' IMPLY P[x |-> t] IMPLY P[x |-> t']).

Notation "|--  P" := (provable P) (at level 91, no associativity): FOL_scope.

(** We can formalize its semantics as follows. First, an interpretation is a
domain [D], an interpretation [Rel] of the binary relation symbol [PRel] and
assignments of all logical variables.*)

Inductive Interp: Type :=
| Build_Interp (D: Type) (Rel: D -> D -> Prop) (La: logical_var -> D) : Interp.

Definition domain_of (J: Interp): Type :=
  match J with
  | Build_Interp D _ _ => D
  end.

(** The following definition is an interesting one. Usually, when we define a
function, its argument type and return type are fixed. For polymorphic
functions, its argument type and return type are both determined by an
additional type argument. But this function [Rel_of]'s return type is directly
determined by its argument's value. Such function is called a dependently
typed function. Coq's type system is very rich and allows dependent types. *)

Definition Rel_of (J: Interp): domain_of J -> domain_of J -> Prop :=
  match J as J0 return
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    Prop
  with
  | Build_Interp D Rel La => Rel
  end.

(** The definition of [Rel_of] looks verbose. But we have to do this in order
to make the [match] expression type check. The function is actually:

    Definition Rel_of (J: Interp): domain_of J -> domain_of J -> Prop :=
      match J with
      | Build_Interp D Rel La => Rel
      end.

All other lines are for typing -- the return type of this pattern matching
expression depends on the pattern matching itself. The type of [Rel] is
[D -> D -> Prop] but this value [D] is only introduced by [match]. Thus Coq
requires us to use the following lines to describe the return type:

    match J as J0 return
        match J0 with
        | Build_Interp D Rel La => D
        end ->
        match J0 with
        | Build_Interp D Rel La => D
        end ->
        Prop
    with.

The following function also needs a similar dependently typed pattern
matching. *)

Definition Lassn_of (J: Interp): logical_var -> domain_of J :=
  match J as J0 return
    logical_var -> 
    match J0 with
    | Build_Interp D Rel La => D
    end
  with
  | Build_Interp D Rel La => La
  end.

(** Next we can define the result of modifying the value of one logical
variable. *)

Definition Lassn_update {D: Type} (La: logical_var -> D) (x: logical_var) (v: D): logical_var -> D :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Definition Interp_Lupdate (J: Interp) (x: logical_var): domain_of J -> Interp :=
  match J with
  | Build_Interp D Rel La =>
     fun v => Build_Interp D Rel (Lassn_update La x v)
  end.

(** The denotation of a term can be easily defined. *)

Definition term_denote (J: Interp) (t: term): domain_of J :=
    match t with
    | TId x => Lassn_of J x
    end.

(** Evenually, we can recursively define the satisfaction relation. *)

Fixpoint satisfies (J: Interp) (d: prop): Prop :=
    match d with
    | PEq t1 t2   => (term_denote J t1 = term_denote J t2)
    | PRel t1 t2  => Rel_of J (term_denote J t1) (term_denote J t2)
    | PFalse      => False
    | PImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | PForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity): FOL_scope.

(** As a routine in logical studies, we can define [valid], [sound] and
[complete]. *)

Local Open Scope FOL_scope.

Definition valid (P: prop): Prop :=
  forall J: Interp, J |== P.

Notation "|==  P" := (valid P) (at level 91, no associativity): FOL_scope.

Definition sound: Prop :=
  forall P: prop, |-- P -> |== P.

Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.

(** We can prove that this first order logic is sound and complete!

The soundness proof is easy -- we only need to do induction over the proof
tree. The only interest cases are about those two proof rules for universal
quantifiers. We need the following lemmas. *)

Lemma prop_sub_spec: forall J (P: prop) (x: logical_var) (t: term),
  J |== P[ x |-> t] <->
  Interp_Lupdate J x (term_denote J t) |== P.
Admitted.

Lemma no_occ_satisfies: forall J P x v,
  prop_free_occur x P = O ->
  (J |== P <-> Interp_Lupdate J x v |== P).
Admitted.

End OneBinRel_FOL.



(* Wed Apr 22 21:40:19 CST 2020 *)
