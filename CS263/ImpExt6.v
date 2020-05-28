Require Import PL.Imp3.
Require Import PL.ImpExt5.

Import Assertion_D.
Import Relation_Operators.

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

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Class FOL_sound (T: FirstOrderLogic): Prop :=
  FOL_soundness: forall P: Assertion, FOL_provable P -> FOL_valid P.

Class FOL_complete (T: FirstOrderLogic): Prop :=
  FOL_completenss: forall P: Assertion, FOL_valid P -> FOL_provable P.

Section Der.

Context {T: FirstOrderLogic}
        {T_sound: FOL_sound T}
        {T_complete: FOL_complete T}.

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

Theorem derives_trans: forall P Q R, P |-- Q -> Q |-- R -> P |-- R.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  apply TrivialFOL_sound_der in H.
  apply TrivialFOL_sound_der in H0.
  unfold FOL_valid in *.
  intros.
  specialize (H J).
  specialize (H0 J).
  simpl in H, H0 |- *.
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

Lemma hoare_skip_inv: forall P Q,
  |-- {{P}} Skip {{Q}} ->
  P |-- Q.  
Proof.
  intros.
  remember ({{P}} Skip {{Q}}) as tr eqn:?H.
  revert P Q H0; induction H; intros.
  + discriminate H1.
  + injection H0 as ? ?; subst.
    apply derives_refl.
  + discriminate H1.
  + discriminate H0.
  + discriminate H0.
  + injection H2 as ? ? ?; subst.
    eapply derives_trans; [exact H |].
    eapply derives_trans; [apply IHprovable; reflexivity |].
    apply H1.
Qed.

Lemma hoare_seq_inv: forall P c1 c2 R,
  |-- {{ P }} c1 ;; c2 {{ R }} ->
  exists Q, (|-- {{ P }} c1 {{ Q }}) /\ (|-- {{ Q }} c2 {{ R }}).
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

Lemma seq_assoc_der: forall P c1 c2 c3 Q,
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

Lemma seq_skip: forall c P Q,
  |-- {{ P }} c;; Skip {{ Q }} <-> |-- {{ P }} c {{ Q }}.
Proof.
  intros; split; intros.
  + apply hoare_seq_inv in H.
    destruct H as [R [? ?]].
    apply hoare_skip_inv in H0.
    apply hoare_consequence_post with R; tauto.
  + apply hoare_seq with Q.
    - exact H.
    - apply hoare_skip.
Qed.

Lemma Hoare_triple_congr_CSeq: forall c1 c1' c2 c2',
  (forall P Q, |-- {{ P }} c1 {{ Q}} <-> |-- {{ P }} c1' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c2 {{ Q}} <-> |-- {{ P }} c2' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c1;; c2 {{ Q}} <-> |-- {{ P }} c1';; c2' {{ Q }}).
Proof.
  intros.
  split; intros; apply hoare_seq_inv in H1; destruct H1 as [? [? ?]];
  (eapply hoare_seq; [apply H, H1 | apply H0, H2]).
Qed.

End Der.

(* Thu Apr 30 00:22:46 CST 2020 *)
