Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.micromega.Psatz.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.
Require Import Permutation.
Require Import ListDec.
Require Import FL.Mobius_Definition.
Require Import FL.Mobius_Lemmas.

Module Lemma2.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Import Def.

Import Lemmas.

(* 定理2证明的关键引理， 描述 x sub Y -> x0 sub Y -> PowerSet Y 中有唯一元素 y, 满足 x cup x0 = y *)
Lemma Summ_Test_Union_Eq: forall (x x0 Y: list nat),
In x (PowerSet Y) -> In x0 (PowerSet Y) -> NoDup Y -> 
Summ_Of_List (list nat) (test_eq_union_Z x x0) (PowerSet Y) = 1%Z.
Proof.
  intros.
  remember (filter (test_in_union_b x x0) Y) as l.
  assert (subseq l Y). { rewrite Heql. pose proof filter_subseq _ Y (test_in_union_b x x0). tauto. }
  apply inpowerset_subseq_eq in H2 as H3.
  apply Per_add in H3 as H4; destruct H4 as [PY' ?].
  pose proof Permutation_Summ _ _ _ (test_eq_union_Z x x0) H4.
  rewrite <- H5.
  simpl.
  assert (Eq_Union x x0 l).
  {
    unfold Eq_Union; intros.
    split; intros.
    - apply Test_In_Union_b in H6 as H7.
      rewrite Heql.
      apply filter_In; split; [ | tauto].
      destruct H6.
      -- apply inpowerset_subseq_eq in H.
         eapply subseq_in; [apply H| tauto].
      -- apply inpowerset_subseq_eq in H0.
         eapply subseq_in; [apply H0| tauto].
    - rewrite Heql in H6.
      apply filter_In in H6; destruct H6.
      apply Test_In_Union_b in H7; tauto.
  }
  pose proof Test_Eq_Union_Z x x0 l; destruct H7.
  apply H7 in H6 as H9.
  rewrite H9.
  assert (Summ_Of_List (list nat) (test_eq_union_Z x x0) PY' = 0%Z).
  {
    rewrite Summ_f_g with (g:= fun l': list nat => 0%Z).
    apply F_zero_summ_zero.
    intros.
    pose proof Test_Eq_Union_Z x x0 x1; destruct H11.
    destruct (classic (Eq_Union x x0 x1)); [ | apply H12 in H13; tauto].
    unfold Eq_Union in H6, H13.
    assert (forall n:nat, In n x1 <-> In n l).
    {
      intros; split; intros.
      - apply H13 in H14.
        apply H6 in H14; tauto.
      - apply H6 in H14;
        apply H13 in H14; tauto.
    }
    assert (NoDup l). { eapply PowerSet_Element_NoDup. apply H1. tauto. }
    assert (NoDup x1). 
    { 
      eapply PowerSet_Element_NoDup. 
      apply H1.
      eapply Permutation_in; [apply H4 | apply in_cons; tauto].
    }
    assert (In x1 (PowerSet Y)). {eapply Permutation_in; [apply H4 | apply in_cons; tauto]. }
    pose proof NoDup_NoPer Y H1 l x1 H3 H17.
    destruct H18.
    - assert (NoDup (l :: PY')). { eapply Permutation_NoDup. apply Permutation_sym, H4. apply PowerSet_NoDup; tauto. }
      rewrite <- H18 in H10.
      apply NoDup_cons_iff in H19; tauto.
    - pose proof NoDup_Permutation H16 H15 H14.
      apply Permutation_sym in H19; tauto.
  }
  rewrite H10.
  lia.
Qed.


End Lemma2.