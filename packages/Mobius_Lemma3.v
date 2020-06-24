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
Require Import FL.Mobius_Lemma2.

Module Lemma3.

Import Def.
Import Lemmas.
Import Lemma2.

(*两种不同定义的等价性*)
Lemma Summ_to_0_eq_Summ_list:
  forall n f,
  Summ_From_n_to_0 n f = Summ_Of_List nat f (nat_list n).
Proof.
  induction n; simpl ;intros.
  - lia.
  - specialize (IHn f).
    rewrite IHn.
    lia.
Qed.

(*交换求和顺序结果不变, Exchange_Summ 要求内外求和列表同类型, Exchange_Summ2 则不要求*)
Lemma Exchange_Summ2 (U1 U2: Type) (f: U1 -> U2 -> Z) (g: U2 -> U1 -> Z):
  (forall (x: U1) (y: U2), f x y = g y x) -> 
  (forall (S1: list U1) (S2: list U2), Summ_Of_List U1 (fun (I: U1) => Summ_Of_List U2 (f I) S2) S1 =
   Summ_Of_List U2 (fun (J: U2) => Summ_Of_List U1 (g J) S1) S2).
Proof.
  intros.
  revert S2.
  induction S1.
  + simpl; intros.
    rewrite F_zero_summ_zero.
    reflexivity.
  + simpl; intros.
    assert (Summ_Of_List U2 (fun J : U2 => (g J a + Summ_Of_List U1 (g J) S1)%Z) S2 =
    (Summ_Of_List U2 (fun J : U2 => g J a) S2)%Z + (Summ_Of_List U2 (fun J : U2 =>Summ_Of_List U1 (g  J) S1) S2))%Z.
    { induction S2;[reflexivity|simpl;lia]. }
    rewrite H0.
    pose proof IHS1 S2.
    rewrite H1.
    assert (forall S: list U2, Summ_Of_List U2 (f a) S = Summ_Of_List U2 (fun J: U2 => g J a) S).
    {
      induction S; intros;[reflexivity|].
      simpl.
      rewrite IHS, H.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
Qed.

Lemma NoDup_In_Length_NoDup_pre: forall (A B: list nat),
  NoDup A ->
  (forall n:nat, In n A -> In n B) ->
  Datatypes.length A <= Datatypes.length B .
Proof.
  induction A; intros.
  - simpl; lia.
  - simpl in *.
    assert (In a B). { apply H0. left; tauto. }
    apply In_Permutation in H1 as H3.
    destruct H3 as [B' ?].
    assert (NoDup A). { apply NoDup_cons_iff in H. tauto. }
    assert (forall n:nat, In n A -> In n B'). 
    {
      intros.
      assert (In n B). {apply H0; tauto. }
      assert (In n (a::B')). { eapply Permutation_in; [apply H2 | tauto]. }
      apply in_inv in H6.
      destruct H6; [ | tauto].
      apply NoDup_cons_iff in H.
      rewrite <- H6 in H4; tauto.
    }
    pose proof Permutation_length H2.
    rewrite H5; simpl.
    pose proof IHA B' H3 H4.
    lia.
Qed.

Lemma NoDup_In_Length_NoDup: forall (A B: list nat),
  NoDup A ->
  (forall n:nat, In n A -> In n B) ->
  Datatypes.length A = Datatypes.length B ->
  NoDup B.
Proof.
  induction A; intros.
  - destruct B; [apply NoDup_nil | simpl in H1; inversion H1].
  - simpl in *.
    assert (In a B). { apply H0. left; tauto. }
    apply In_Permutation in H2 as H3.
    destruct H3 as [B' ?].
    assert (NoDup A). { apply NoDup_cons_iff in H. tauto. }
    assert (forall n:nat, In n A -> In n B'). 
    {
      intros.
      assert (In n B). {apply H0; tauto. }
      assert (In n (a::B')). { eapply Permutation_in; [apply H3 | tauto]. }
      apply in_inv in H7.
      destruct H7; [ | tauto].
      apply NoDup_cons_iff in H.
      rewrite <- H7 in H5; tauto.
    }
    pose proof Permutation_length H3.
    rewrite H6 in H1; simpl in H1.
    inversion H1.
    pose proof IHA B' H4 H5 H8.
    eapply Permutation_NoDup; [apply Permutation_sym, H3 | ].
    apply NoDup_cons; [ | tauto].
    destruct (classic (In a B')); [ | tauto].
    apply In_Permutation in H9 as H10.
    destruct H10 as [B'' ?].
    assert (forall n: nat, In n A -> In n B'').
    {
      intros.
      assert (In n (a::B')). { eapply Permutation_in; [apply H3 | apply H0; tauto]. }
      apply in_inv in H12.
      destruct H12; [rewrite <- H12 in H11; apply NoDup_cons_iff in H; tauto | ].
      assert (In n (a::B'')). { eapply Permutation_in; [apply H10 | tauto]. }
      apply in_inv in H13.
      destruct H13; [rewrite <- H13 in H11; apply NoDup_cons_iff in H; tauto | tauto].
    }
    apply NoDup_cons_iff in H; destruct H.
    pose proof NoDup_In_Length_NoDup_pre A B'' H12 H11.
    pose proof Permutation_length H10.
    rewrite H14 in H8.
    simpl in H8.
    rewrite H8 in H13.
    lia.
Qed.

Lemma NoDup_app': forall (A B: list nat),
  NoDup (A++B) -> (forall n:nat, In n A -> ~ In n B).
Proof.
  intros.
  apply In_Permutation in H0.
  destruct H0 as [A' ?].
  remember (n::A') as A0.
  assert (Permutation (A++B) (A0++B)). 
  { 
    apply Permutation_app; [ tauto | apply Permutation_refl ].
  }
  pose proof Permutation_NoDup H1 H.
  rewrite HeqA0 in H2.
  rewrite <- app_comm_cons in H2.
  apply NoDup_cons_iff in H2.
  destruct H2.
  destruct (classic (In n B));[|tauto].
  assert (In n (A' ++ B)). { apply in_app_iff. tauto. }
  tauto.
Qed.

(* 定理3证明的关键引理 *)
Lemma Union_Length_Empty: forall (A B X: list nat),
  NoDup A -> 
  NoDup B ->
  NoDup X ->
  Eq_Union A B X ->
  Empty_Intersect A B <-> Datatypes.length A + Datatypes.length B = Datatypes.length X.
Proof.
  intros.
  assert (forall n: nat, In n X <-> In n (A++B)).
  {
    unfold Eq_Union in H2.
    intros; split; intros.
    - apply In_A_app_B.
      apply H2 in H3; tauto.
    - apply H2.
      apply In_A_app_B; tauto.
  }
  unfold Empty_Intersect.
  split; intros.
  - pose proof NoDup_App _ _ _ H H0 H4.
    pose proof NoDup_Permutation H1 H5 H3.
    pose proof Permutation_length H6.
    rewrite app_length in H7.
    lia.
  - rewrite <- app_length in H4.
    assert (NoDup (A++B)).
    {
      eapply NoDup_In_Length_NoDup.
      apply H1.
      apply H3.
      lia.
    }
    pose proof NoDup_app' _ _ H6.
    apply H7, H5.
Qed.


End Lemma3.