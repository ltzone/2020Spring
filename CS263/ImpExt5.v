Require Import PL.Imp3 PL.ImpExt4.
Local Open Scope imp.

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus1.
      exact H.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult1.
      exact H.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq1.
      exact H.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le1.
      exact H.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_NotStep.
      exact H.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_AndStep.
      exact H.
Qed.

Theorem multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  multi_cstep (CAss X a, st) (CAss X a', st).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_AssStep.
      exact H.
Qed.

Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (CSeq c1 c2, st1) (CSeq c1' c2, st1').

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_SeqStep.
      exact H.
Qed.

Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (CIf b c1 c2, st)
    (CIf b' c1 c2, st).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_IfStep.
      exact H.
Qed.

(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + unfold constant_func in H.
    rewrite H.
    reflexivity.
  + rewrite <- H.
    etransitivity_n1; [reflexivity |].
    apply AS_Id.
  + etransitivity.
    { apply multi_congr_APlus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_APlus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Plus.
  + etransitivity.
    { apply multi_congr_AMinus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMinus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Minus.
  + etransitivity.
    { apply multi_congr_AMult1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMult2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Mult.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      reflexivity.
    - unfold Sets.full.
      tauto.
  + split.
    - unfold Sets.empty.
      tauto.
    - intros.
      reflexivity.
  + assert (multi_bstep st (a1 == a2) (aeval a1 st == aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BEq1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BEq2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_eq; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Eq_True, H0.
    - apply BS_Eq_False, H0.
  + assert (multi_bstep st (a1 <= a2) (aeval a1 st <= aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BLe1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BLe2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_le; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Le_True, H0.
    - apply BS_Le_False.
      lia.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH2.
        unfold Sets.complement in H; exact H.
      * apply BS_NotFalse.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH1.
        unfold Sets.complement in H; tauto.
      * apply BS_NotTrue.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - assert (multi_bstep st (b1 && b2) b2).
      {
        etransitivity_n1.
        * apply multi_congr_BAnd, IHb11, H.
        * apply BS_AndTrue.
      }
      split; unfold Sets.intersect; intros;
      (etransitivity; [exact H0 |]).
      * apply IHb21; tauto.
      * apply IHb22; tauto.
    - split; unfold Sets.intersect; intros; [ tauto |].
      etransitivity_n1.
      * apply multi_congr_BAnd, IHb12, H.
      * apply BS_AndFalse.
Qed.

Corollary semantic_equiv_bexp1_true: forall st b,
  beval b st -> multi_bstep st b BTrue.
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.
  
Corollary semantic_equiv_bexp1_false: forall st b,
  (Sets.complement (beval b) st -> multi_bstep st b BFalse).
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c,
  (forall st1 st2, ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2)) ->
  iter_loop_body b (ceval c) n st1 st2 ->
  multi_cstep (While b Do c EndWhile, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    unfold Relation_Operators.test_rel in H0.
    destruct H0.
    subst st2.
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 |].
    etransitivity_1n; [apply CS_IfFalse |].
    reflexivity.
  + simpl in H0.
    unfold Relation_Operators.concat at 1,
           Relation_Operators.test_rel in H0.
    destruct H0 as [st [[? H0] ?]]; subst st.
    unfold Relation_Operators.concat in H2.
    destruct H2 as [st1' [? ?]].
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 |].
    etransitivity_1n; [apply CS_IfTrue |].
    etransitivity; [apply multi_congr_CSeq, H, H1 |].
    etransitivity_1n; [apply CS_Seq |].
    apply IHn, H2.
Qed.

Theorem semantic_equiv_com1: forall st1 st2 c,
  ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + rewrite ceval_CSkip in H.
    unfold Relation_Operators.id in H.
    rewrite H.
    reflexivity.
  + rewrite ceval_CAss in H.
    destruct H.
    etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply CS_Ass; tauto.
  + rewrite ceval_CSeq in H.
    unfold Relation_Operators.concat in H.
    destruct H as [st' [? ?]].
    etransitivity; [apply multi_congr_CSeq, IHc1, H |].
    etransitivity_1n; [ apply CS_Seq |].
    apply IHc2, H0.
  + rewrite ceval_CIf in H.
    unfold if_sem in H.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [st [[? ?] ?]]; subst st.
    - etransitivity; [apply multi_congr_CIf, H0, H2 |].
      etransitivity_1n; [apply CS_IfTrue |].
      apply IHc1, H3.
    - etransitivity; [apply multi_congr_CIf, H1, H2 |].
      etransitivity_1n; [apply CS_IfFalse |].
      apply IHc2, H3.
  + rewrite ceval_CWhile in H.
    unfold loop_sem in H.
    unfold Relation_Operators.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

(* ################################################################# *)
(** * Properties Of Execution Paths *)

Local Open Scope Z.
Local Close Scope imp.

Lemma ANum_halt: forall st n a,
  multi_astep st (ANum n) a ->
  a = ANum n.

Proof.
  unfold_with_1n multi_astep.
  intros.
  inversion H; subst.
  + reflexivity.
  + inversion H0.
Qed.

Lemma never_BFalse_to_BTrue: forall st,
  multi_bstep st BFalse BTrue -> False.

Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma never_BTrue_to_BFalse: forall st,
  multi_bstep st BTrue BFalse -> False.

Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma CSkip_halt: forall st st' c,
  multi_cstep (CSkip, st) (c, st') ->
  c = CSkip /\ st = st'.
Proof.

  unfold_with_1n multi_cstep.
  intros.
  inversion H; subst.
  + split; reflexivity.
  + inversion H0.
Qed.

Lemma APlus_path_spec: forall st a1 a2 n,
  multi_astep st (APlus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 + n2).
Proof.
  intros.
  remember (APlus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMinus_path_spec: forall st a1 a2 n,
  multi_astep st (AMinus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 - n2).
Proof.
  intros.
  remember (AMinus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMult_path_spec: forall st a1 a2 n,
  multi_astep st (AMult a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 * n2).
Proof.
  intros.
  remember (AMult a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma BEq_True_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 = n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n2, n2.
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BEq_False_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <> n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BLe_True_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <= n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BLe_False_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 > n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BNot_True_path_spec: forall st b,
  multi_bstep st (BNot b) BTrue ->
  multi_bstep st b BFalse.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BTrue as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
    - reflexivity.
Qed.

Lemma BNot_False_path_spec: forall st b,
  multi_bstep st (BNot b) BFalse ->
  multi_bstep st b BTrue.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BFalse as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - reflexivity.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
Qed.

Lemma BAnd_True_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BTrue ->
  multi_bstep st b1 BTrue /\
  multi_bstep st b2 BTrue.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BTrue as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      assert (multi_bstep st b1 BTrue). { etransitivity_1n; eassumption. }
      tauto.
    - split.
      * reflexivity.
      * exact H0.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BAnd_False_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BFalse ->
  multi_bstep st b1 BFalse \/
  multi_bstep st b2 BFalse.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BFalse as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      * assert (multi_bstep st b1 BFalse). { etransitivity_1n; eassumption. }
        tauto.
      * tauto.
    - right.
      exact H0.
    - left.
      reflexivity.
Qed.

Lemma CAss_path_spec: forall X a st1 st2,
  multi_cstep (CAss X a, st1) (CSkip, st2) ->
  exists n,
  multi_astep st1 a (ANum n) /\
  st2 X = n /\
  (forall Y : var, X <> Y -> st1 Y = st2 Y).
Proof.
  intros.
  remember (CAss X a) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert a H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n [? ?]].
      exists n.
      assert (multi_astep s a n). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply CSkip_halt in H0.
      destruct H0.
      subst s.
      exists (st2 X).
      split; [reflexivity | tauto].
Qed.

Lemma CSeq_path_spec: forall c1 st1 c2 st3,
  multi_cstep (CSeq c1 c2, st1) (CSkip, st3) ->
  exists st2,
  multi_cstep (c1, st1) (CSkip, st2) /\
  multi_cstep (c2, st2) (CSkip, st3).
Proof.
  intros.
  remember (CSeq c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [st2 [? ?]].
      exists st2.
      assert (multi_cstep (c1, st1) (Skip%imp, st2)).
      { etransitivity_1n; eassumption. }
      tauto.
    - exists s.
      split; [reflexivity | tauto].
Qed.

Lemma CIf_path_spec: forall b c1 c2 st1 st2,
  multi_cstep (CIf b c1 c2, st1) (CSkip, st2) ->
  multi_bstep st1 b BTrue /\
  multi_cstep (c1, st1) (CSkip, st2) \/
  multi_bstep st1 b BFalse /\
  multi_cstep (c2, st1) (CSkip, st2).
Proof.
  intros.
  remember (CIf b c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [[? ?] | [? ?]].
      * assert (multi_bstep s b BTrue). { etransitivity_1n; eassumption. }
        tauto.
      * assert (multi_bstep s b BFalse). { etransitivity_1n; eassumption. }
        tauto.
    - assert (multi_bstep s BTrue BTrue). { reflexivity. }
      tauto.
    - assert (multi_bstep s BFalse BFalse). { reflexivity. }
      tauto.
Qed.

Fixpoint CWhile_path b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b BTrue /\
            multi_cstep (c1, st1) (CSkip, st1') /\
            CWhile_path b c1 st1' st2 n'
  end.

Definition CWhile_path' b' b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b' BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b' BTrue /\
            multi_cstep (c1, st1) (CSkip, st1') /\
            CWhile_path b c1 st1' st2 n'
  end.

Definition CWhile_path'' c1' b c1 st1 st2 (n: nat): Prop:=
  exists st1',
    multi_cstep (c1', st1) (CSkip, st1') /\
    CWhile_path b c1 st1' st2 n.

Lemma CWhile_path_spec_aux: forall st1 st2 c c',
  multi_cstep (c, st1) (c', st2) ->
  (forall b c1,
     c = CWhile b c1 ->
     c' = Skip%imp ->
     exists n, CWhile_path b c1 st1 st2 n) /\
  (forall b' b c1,
     c = CIf b' (CSeq c1 (CWhile b c1)) CSkip ->
     c' = Skip%imp ->
     exists n, CWhile_path' b' b c1 st1 st2 n) /\
  (forall c1' b c1,
     c = CSeq c1' (CWhile b c1) ->
     c' = Skip%imp ->
     exists n, CWhile_path'' c1' b c1 st1 st2 n).
Proof.
  intros.
  induction_1n H; intros.
  + split.
    { intros; subst. inversion H0. }
    split.
    { intros; subst. inversion H0. }
    { intros; subst. inversion H0. }
  + split; [| split].
    - intros; subst.
      destruct IHrt as [_ [IHrt _]].
      inversion H; subst.
      specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n ?].
      exists n.
      destruct n; exact H1.
    - intros; subst.
      inversion H; subst.
      * destruct IHrt as [_ [IHrt _]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        destruct n; simpl in H1; simpl.
       ++ destruct H1.
          split; [etransitivity_1n; eassumption | tauto].
       ++ destruct H1 as [st1' [? [? ?]]].
          exists st1'.
          split; [etransitivity_1n; eassumption | tauto].
      * destruct IHrt as [_ [_ IHrt]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists (S n).
        unfold CWhile_path'' in H1.
        simpl.
        destruct H1 as [st1' [? ?]].
        exists st1'.
        assert (multi_bstep s BTrue BTrue). { reflexivity. }
        tauto.
      * exists O.
        simpl.
        assert (multi_bstep s BFalse BFalse). { reflexivity. }
        apply CSkip_halt in H0.
        tauto.
    - intros; subst.
      inversion H; subst.
      * destruct IHrt as [_ [_ IHrt]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        unfold CWhile_path'' in H1.
        unfold CWhile_path''.
        destruct H1 as [st1' [? ?]].
        exists st1'.
        assert (multi_cstep (c1', st1) (Skip%imp, st1')).
        { etransitivity_1n; eassumption. }
        tauto.
      * destruct IHrt as [IHrt [? ?]].
        specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        unfold CWhile_path''.
        exists s.
        split; [reflexivity | tauto].
Qed.

Lemma CWhile_path_spec: forall b c1 st1 st2,
  multi_cstep (CWhile b c1, st1) (CSkip, st2) ->
  exists n, CWhile_path b c1 st1 st2 n.
Proof.
  intros.
  remember (CWhile b c1) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 H0 H1.
  pose proof CWhile_path_spec_aux st1 st2 c c'.
  tauto.
Qed.

(* ################################################################# *)
(** * From Multi-step Relations To Denotations *)

Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  revert n H; induction a; intros; simpl.
  + apply ANum_halt in H.
    injection H as ?H.
    rewrite H.
    reflexivity.
  + unfold_with_1n multi_astep in H.
    inversion H; subst.
    inversion H0; subst.
    inversion H1; subst.
    - reflexivity.
    - inversion H2.
  + apply APlus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.add; lia.
  + apply AMinus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.sub; lia.
  + apply AMult_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.mul; nia.
Qed.

Theorem semantic_equiv_bexp2: forall st b,
  (multi_bstep st b BTrue -> beval b st) /\
  (multi_bstep st b BFalse -> ~ beval b st).
Proof.
  intros.
  induction b; simpl.
  + split; intros.
    - exact I.
    - apply never_BTrue_to_BFalse in H.
      destruct H.
  + split; intros.
    - apply never_BFalse_to_BTrue in H.
      destruct H.
    - tauto.
  + split; intros.
    - apply BEq_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
    - apply BEq_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
  + split; intros.
    - apply BLe_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
    - apply BLe_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
  + destruct IHb as [IHb1 IHb2].
    split; intros.
    - apply BNot_True_path_spec in H.
      unfold Sets.complement; tauto.
    - apply BNot_False_path_spec in H.
      unfold Sets.complement; tauto.
  + split; intros.
    - apply BAnd_True_path_spec in H.
      unfold Sets.intersect; tauto.
    - apply BAnd_False_path_spec in H.
      unfold Sets.intersect; tauto.
Qed.

Theorem semantic_equiv_com2: forall c st1 st2,
  multi_cstep (c, st1) (CSkip, st2) -> ceval c st1 st2.
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + apply CSkip_halt in H.
    destruct H.
    rewrite H0.
    simpl.
    unfold Relation_Operators.id.
    reflexivity.
  + apply CAss_path_spec in H.
    destruct H as [n [? [? ?]]].
    apply semantic_equiv_aexp2 in H.
    rewrite ceval_CAss, H.
    tauto.
  + apply CSeq_path_spec in H.
    destruct H as [st1' [? ?]].
    apply IHc1 in H.
    apply IHc2 in H0.
    rewrite ceval_CSeq.
    unfold Relation_Operators.concat.
    exists st1'.
    tauto.
  + apply CIf_path_spec in H.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    specialize (IHc1 st1 st2).
    specialize (IHc2 st1 st2).
    pose proof semantic_equiv_bexp2 st1 b.
    destruct H; [left | right]; exists st1; tauto.
  + apply CWhile_path_spec in H.
    rewrite ceval_CWhile.
    unfold loop_sem.
    unfold Relation_Operators.omega_union.
    destruct H as [n ?].
    exists n.
    revert st1 H; induction n; simpl; intros.
    - pose proof semantic_equiv_bexp2 st1 b.
      destruct H.
      subst st2.
      unfold Relation_Operators.test_rel,
             Sets.complement.
      tauto.
    - destruct H as [st1' [? [? ?]]].
      specialize (IHn st1').
      unfold Relation_Operators.concat,
             Relation_Operators.test_rel.
      apply semantic_equiv_bexp2 in H.
      exists st1.
      split.
      * tauto.
      * exists st1'.
        specialize (IHc st1 st1').
        tauto.
Qed.

(* ################################################################# *)
(** * Final Theorem *)

Theorem semantic_equiv: forall c st1 st2,
  ceval c st1 st2 <-> multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

(* ################################################################# *)
(** * Alternative Proofs: From Multi-step Relations To Denotations *)

Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add, constant_func.
    reflexivity.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub, constant_func.
    reflexivity.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul, constant_func.
    reflexivity.
Qed.

Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_eq.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_eq.
    lia.
  + simpl.
    unfold Func.test_eq, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_eq, Sets.empty.
    tauto.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_le.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_le.
    lia.
  + simpl.
    unfold Func.test_le, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_le, constant_func, Sets.empty.
    lia.
  + simpl.
    unfold Sets.complement.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.intersect.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.full.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.empty.
    tauto.
Qed.

Lemma ceval_preserve: forall c1 c2 st1 st2,
  cstep (c1, st1) (c2, st2) ->
  forall st3, ceval c2 st2 st3 -> ceval c1 st1 st3.
Proof.
(** We could prove a stronger conclusion:

    forall st3, ceval c1 st1 st3 <-> ceval c2 st2 st3.

But this single direction version is enough to use. *)
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  revert c1 c2 st1 st2 st3 H0 H1; induction H; simpl; intros.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CAss in H2.
    rewrite ceval_CAss.
    rewrite H.
    tauto.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    rewrite ceval_CSkip in H3.
    rewrite ceval_CAss.
    unfold Relation_Operators.id in H3.
    subst.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CSeq in H2.
    rewrite ceval_CSeq.
    unfold Relation_Operators.concat in H2.
    unfold Relation_Operators.concat.
    destruct H2 as [st2' [? ?]].
    exists st2'.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c1', st2) = (c1', st2)). { reflexivity. }
    specialize (IHcstep _ _ _ _ st2' H2 H3).
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    unfold Relation_Operators.concat, Relation_Operators.id.
    exists st2.
    split.
    - reflexivity.
    - exact H2.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf in H2.
    rewrite ceval_CIf.
    unfold if_sem in H2.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel in H2.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    apply beval_preserve in H.
    simpl in H2.
    simpl.
    unfold Sets.complement in H2.
    unfold Sets.complement.
    destruct H2 as [[st2' ?] | [st2' ?]]; [left | right];
      exists st2'; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    left; exists st2; simpl.
    unfold Sets.full; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.concat,
           Relation_Operators.test_rel.
    right; exists st2; simpl.
    unfold Sets.complement, Sets.empty; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    pose proof loop_unrolling b c.
    unfold com_equiv, Rel.equiv in H.
    specialize (H st2 st3).
    tauto.
Qed.

(* Fri Apr 17 00:44:34 CST 2020 *)
