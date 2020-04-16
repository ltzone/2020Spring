Require Import PL.Imp3.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Review *)

(** Here is a list of important terminologies that introduced in the last
    lecture.

    - We use syntax trees to describe assertions. Assertions describe properties
      of program states and logical variables via expressions ([aexp] and
      [bexp]) and terms.

    - Syntactic substitution is recursively defined. When quantifiers (forall
      and exists) are involved, renaming should be done beforehand. E.g.
      [  (EXISTS x, {[X]} = 2 * x) [X |-> x]  ] should be
      [  EXISTS y, {[x]} = 2 * y ] instead of [  EXISTS x, {[x]} = 2 * x ].

    - A Hoare triple is _provable_ (可证) if we can prove it from our Hoare
      logic proof rules, written as [ |-- {{ P }} c {{ Q }} ]. In these two
      weeks, we will pick backward assignment rule in our proof theories.

    - An _interpretation_ (解释) is a pair of program state and logical variable
      assignment. When an interpretation _satisfies_ (满足) an assertion is
      defined by recursively on the assertion's syntax tree. We write
      [ J |= P ] if [J] satisfies [P].

    - A Hoare triple [ {{ P }} c {{ Q }} ] is _valid_ (有效) when for any
      beginning state [st1], assignment [La] and ending state [st2], if
      [ (st1, La) |= P ] and [ (st1, st2) ] is in the denotation of [c],
      then [ (st2, La) |= Q ], written as [ |== {{ P }} c {{ Q }} ]. *)

(* ################################################################# *)
(** * Soundness *)

(** We will prove Hoare logic's soundness today. Recall that a Hoare logic is
sound when all provable Hoare triples are valid. *)

Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |-- {{ P }} c {{ Q }} ->
    |== {{ P }} c {{ Q }}.

(** We will prove that if the logic for assertion derivation is sound, then the
corresponding Hoare logic is also sound. Similarly, an assertion is called
_valid_ if it is satisfied on all interpreations. And a logic for assertion
derivation is called sound, if every provable assertion is valid. *)

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

(** Now, we will start our Hoare logic soundness proof. *)

Lemma hoare_seq_sound : forall (P Q R: Assertion) (c1 c2: com),
  |== {{P}} c1 {{Q}} ->
  |== {{Q}} c2 {{R}} ->
  |== {{P}} c1;;c2 {{R}}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold Relation_Operators.concat in H2.
  destruct H2 as [st1' [? ?]].
  specialize (H _ _ _ H1 H2).
  specialize (H0 _ _ _ H H3).
  exact H0.
Qed.

Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  unfold Relation_Operators.id in H0.
  rewrite <- H0.
  exact H.
Qed.

Lemma hoare_if_sound : forall P Q (b: bexp) c1 c2,
  |== {{ P AND {[b]} }} c1 {{ Q }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
Proof.
  unfold valid.
  intros.
  rewrite ceval_CIf in H2.
  unfold if_sem in H2.
  unfold Relation_Operators.union,
         Relation_Operators.concat,
         Relation_Operators.test_rel in H2.
  destruct H2 as [H2 | H2];
  destruct H2 as [st [[? ?] ?]]; subst st.
  + apply H with st1.
    - simpl.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - tauto.
  + apply H0 with st1.
    - simpl.
      simpl in H3.
      unfold Sets.complement in H3.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - tauto.
Qed.

Lemma hoare_while_sound : forall P (b: bexp) c,
  |== {{ P AND {[b]} }} c {{P}} ->
  |== {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.
Proof.
  unfold valid.
  intros.
  rewrite ceval_CWhile in H1.
  unfold loop_sem in H1.
  unfold Relation_Operators.omega_union in H1.
  destruct H1 as [n ?].
  revert st1 H0 H1; induction n; intros.
  + simpl in H1.
    unfold Relation_Operators.test_rel,
           Sets.complement in H1.
    destruct H1.
    subst st2.
    simpl.
    pose proof beval_bexp'_denote st1 La b.
    tauto.
  + simpl in H1.
    unfold Relation_Operators.concat at 1,
           Relation_Operators.test_rel in H1.
    destruct H1 as [st1' [[HH ?] ?]]; subst st1'.
    unfold Relation_Operators.concat in H2.
    destruct H2 as [st1' [? ?]].
    apply IHn with st1'.
    - apply H with st1.
      * simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      * exact H2.
    - exact H3.
Qed.

(** For backward assignment rule's case, we need to use an important property
    of syntactic substitution. *)

Check Assertion_sub_spec.

(* Assertion_sub_spec
     : forall (st1 : state) (st2 : var -> Z) (La : Lassn) 
         (P : Assertion) (X : var) (E : aexp'),
       st2 X = aexp'_denote (st1, La) E ->
       (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
       (st1, La) |== P [X |-> E] <-> (st2, La) |== P *)

(** It says: the effect of syntactic substitution is the same as doing real
    modification on program states. We provide its proof in [Imp]. *)

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{ P [ X |-> E] }} X ::= E {{ P }}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  destruct H0.
  pose proof aeval_aexp'_denote st1 La E.
  rewrite H2 in H0.
  pose proof Assertion_sub_spec st1 st2 _ P _ _ H0 H1.
  tauto.
Qed.

Lemma hoare_consequence_sound : forall (T: FirstOrderLogic) (P P' Q Q' : Assertion) c,
  FOL_sound T ->
  P |-- P' ->
  |== {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  |== {{P}} c {{Q}}.
Proof.
  intros.
  unfold FOL_sound in H.
  unfold derives in H0, H2.
  apply H in H0.
  apply H in H2.
  unfold FOL_valid in H0, H2.
  simpl in H0, H2.
  unfold valid in H1.
  unfold valid.
  intros.
  assert ((st1, La) |== P').
  {
    specialize (H0 (st1, La)).
    tauto.
  }
  pose proof H1 _ _ _ H5 H4.
  specialize (H2 (st2, La)).
  tauto.
Qed.

Theorem Hoare_logic_soundness: forall (T: FirstOrderLogic) (TS: FOL_sound T),
  hoare_sound T.
Proof.
  intros.
  unfold hoare_sound.
  intros.
  remember ({{P}} c {{Q}}) as Tr.
  clear P c Q HeqTr.
  induction H.
  + eapply hoare_seq_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_skip_sound.
  + apply hoare_if_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_while_sound.
    exact IHprovable.
  + apply hoare_asgn_bwd_sound.
  + pose proof hoare_consequence_sound T P P' Q Q' c TS H IHprovable H1.
    exact H2.
Qed.

(* Thu Apr 16 00:31:53 CST 2020 *)
