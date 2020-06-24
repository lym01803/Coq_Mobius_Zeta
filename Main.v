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
Require Import FL.Mobius_Lemma3.

Section Fast_Zeta_Mobius_Transforms.

Import Def.
Import Lemmas.
Import Lemma2.
Import Lemma3.

(*关键定义*)
Print Zeta.
Locate Zeta.
Print Mobius.
Locate Mobius.

(*关键引理*)
Check Constraint_in.
Locate Constraint_in.
Check Exchange_Summ.
Locate Exchange_Summ.
Check Binomial_inner_constraint_new.
Locate Binomial_inner_constraint_new.
Check Binomial_minusone.
Locate Binomial_minusone.

(* Theorem 10.11 f(X) = (mu zeta f) (X) = (zeta mu f) (X) *)
Theorem Inversion_formula: forall (f: (list nat) -> Z) (X: list nat), 
  NoDup X ->
  Zeta (Mobius f) X = f X /\ Mobius (Zeta f) X = f X.
Proof.
  split; intros.
  + unfold Mobius, Zeta.
    rewrite Summ_f_g with (g := (fun X0 : list nat => Summ_Of_List (list nat) 
                          (f_x_test_in (Mu f (Datatypes.length X0)) (PowerSet X0)) (PowerSet X))).
    2:
    { 
      intros. 
      apply Constraint_in. 
      apply H. 
      apply H0. 
    }
    rewrite Exchange_Summ with (g := fun (z y: list nat) => f_x_test_in (Mu f (Datatypes.length y)) 
                               (PowerSet y) z); [ | reflexivity ].
    unfold f_x_test_in, Mu.
    erewrite Summ_f_g.
    2:
    { 
      intros.
      assert (forall y: list nat, In y (PowerSet X) -> 
                        (MinusOnePower (Datatypes.length y - Datatypes.length x) * f x * test_in_list_Z x (PowerSet y))%Z = 
                        (MinusOnePower (Datatypes.length y + Datatypes.length x) * f x * test_in_list_Z x (PowerSet y))%Z).
      { 
        intros.
        unfold test_in_list_Z.
        destruct (test_in_list x (PowerSet y));[|lia].
        rewrite MinusOnePower_Minus_to_Add; [reflexivity | apply Subset_length].
        ** eapply PowerSet_Element_NoDup; [apply H | apply H1].
        ** eapply PowerSet_Element_NoDup; [eapply PowerSet_Element_NoDup; [apply H | apply H1 ] | apply i].
        ** apply PowerSet_Subset, i.
      }
      apply Summ_f_g.
      apply H1.
    }
    erewrite Summ_f_g.
    2:
    {
      intros.
      apply Summ_f_g; intros.
      rewrite <- MinusOnePower_Add.
      reflexivity.
    }
    erewrite Summ_f_g.
    2:
    {
      intros.
      assert (forall l: list (list nat), (Summ_Of_List (list nat)
              (fun x0 : list nat =>
              (MinusOnePower (Datatypes.length x0) * MinusOnePower (Datatypes.length x) * f x *
              test_in_list_Z x (PowerSet x0))%Z) l) = 
              Z.mul (Z.mul (MinusOnePower (Datatypes.length x)) (f x)) (Summ_Of_List (list nat)
                    (fun x0 : list nat => (MinusOnePower (Datatypes.length x0) * test_in_list_Z x (PowerSet x0))%Z) l)).
      {
        intros.
        induction l.
        - simpl. lia.
        - simpl.
          rewrite IHl.
          lia.
      }
      rewrite H1.
      reflexivity.
    }
    rewrite Summ_f_g with (g := fun x: list nat => Z.mul (f x) (test_list_eq_Z x X)).
    apply Summ_test_eq, H.
    intros.
    rewrite Binomial_inner_constraint_new; [ | tauto | tauto].
    unfold test_list_eq_Z.
    destruct (test_list_eq x X).
    - apply Eq_Subset_Empty in e.
      rewrite e.
      simpl.
      assert (forall a b c:Z, Z.mul (Z.mul a b) c = Z.mul (Z.mul a c) b). { lia. }
      rewrite H1.
      rewrite Z.mul_assoc.
      rewrite MinusOnePower_Add, MinusOnePower_Double; lia.
    - pose proof Binomial_minusone(MinusSet X x).
      destruct H1.
      pose proof PowerSet_Element_NoDup X x H H0.
      pose proof inpowerset_subseq_eq x X.
      apply H4 in H0 as H5.
      pose proof Not_Eq_Subseq x X H H3 H5 n.
      destruct H6 as [x0 [? ?]].
      assert (In x0 (MinusSet X x)). 
      { 
        unfold MinusSet. apply filter_In.
        split; [tauto | unfold Test_In].
        destruct (test_in x0 x); [tauto | tauto]. 
      }
      assert (MinusSet X x <> []).
      { 
        destruct (classic (MinusSet X x = [] ));[|tauto].
        rewrite H9 in H8. apply in_nil in H8; tauto.
      }
      apply H2 in H9.
      unfold MinusOnetoLen in H9.
      lia.
  + unfold Mobius, Zeta, Mu.
    rewrite Summ_f_g with (g := fun X0: list nat => Summ_Of_List (list nat) 
                          (fun x: list nat => Z.mul (MinusOnePower (Datatypes.length X + Datatypes.length X0)) (f x)) 
                          (PowerSet X0)).
    2:
    {
      intros.
      rewrite <- Out_coef.
      erewrite Summ_f_g; [reflexivity | intros].
      simpl.
      rewrite MinusOnePower_Minus_to_Add; [reflexivity | ].
      apply Subset_length; [tauto | eapply PowerSet_Element_NoDup; [apply H | tauto] | apply PowerSet_Subset; tauto].
    }
    rewrite Summ_f_g with (g:= fun X0: list nat => Summ_Of_List (list nat) 
                                      (fun x: list nat => Z.mul 
                                      (Z.mul (MinusOnePower (Datatypes.length X + Datatypes.length X0)) (f x)) 
                                      (test_in_list_Z x (PowerSet X0))) (PowerSet X)).
    2:
    {
      intros.
      assert (NoDup (PowerSet X)). { apply PowerSet_NoDup; tauto. }
      assert (NoDup (PowerSet x)). { apply PowerSet_NoDup. eapply PowerSet_Element_NoDup; [apply H | tauto]. }
      assert (Subset _ (PowerSet x) (PowerSet X)). { apply Subset_PowerSet; [tauto | eapply PowerSet_Element_NoDup; [apply H | tauto] | tauto]. }
      pose proof Summ_constraint_X_Y (PowerSet X) (PowerSet x) ((fun x0 : list nat =>
   (MinusOnePower (Datatypes.length X + Datatypes.length x) * f x0)%Z)) H1 H2 H3.
      rewrite H4.
      unfold f_x_test_in; reflexivity.
    }
    rewrite Exchange_Summ with (g:= fun (z y: list nat) => Z.mul (Z.mul (MinusOnePower (Datatypes.length X + Datatypes.length y)) (f z)) (test_in_list_Z z (PowerSet y))); [ | reflexivity].
    erewrite Summ_f_g.
    2:
    {
      intros.
      erewrite Summ_f_g.
      2:
      {
        intros.
        rewrite <- MinusOnePower_Add.
        assert (forall a b c d: Z, Z.mul (Z.mul (Z.mul a b) c) d = Z.mul (Z.mul a c) (Z.mul b d)). { lia. }
        rewrite H2; reflexivity.
      }
      pose proof Out_coef (list nat) (PowerSet X) (fun x0: list nat => Z.mul (MinusOnePower (Datatypes.length x0)) (test_in_list_Z x (PowerSet x0))) (Z.mul (MinusOnePower (Datatypes.length X)) (f x)).
      rewrite H1; reflexivity.
    }
    rewrite Summ_f_g with (g:= fun x: list nat => Z.mul (f x) (test_list_eq_Z x X)).
    apply Summ_test_eq, H.
    intros.
    rewrite Binomial_inner_constraint_new; [ | tauto | tauto].
    unfold test_list_eq_Z.
    destruct (test_list_eq x X).
    - apply Eq_Subset_Empty in e as H1.
      rewrite H1, e.
      simpl.
      assert (forall a b c d:Z, Z.mul (Z.mul a b) (Z.mul c d) = Z.mul (Z.mul (Z.mul a c) b) d). { lia. }
      rewrite H2, MinusOnePower_Add, MinusOnePower_Double; lia.
    - pose proof Binomial_minusone(MinusSet X x).
      destruct H1.
      pose proof PowerSet_Element_NoDup X x H H0.
      pose proof inpowerset_subseq_eq x X.
      apply H4 in H0 as H5.
      pose proof Not_Eq_Subseq x X H H3 H5 n.
      destruct H6 as [x0 [? ?]].
      assert (In x0 (MinusSet X x)). 
      { unfold MinusSet. apply filter_In.
        split; [tauto | unfold Test_In].
        destruct (test_in x0 x); [tauto | tauto]. }
      assert (MinusSet X x <> []).
      { destruct (classic (MinusSet X x = [] )).
        * rewrite H9 in H8.
          apply in_nil in H8; tauto.
        * tauto. }
      apply H2 in H9.
      unfold MinusOnetoLen in H9.
      rewrite H9.
      lia.
Qed.


(*关键定义*)
Print Cover_Product_new.
Locate Cover_Product_new.
(*关键引理*)
Check Summ_Test_Union_Eq.
Locate Summ_Test_Union_Eq.

(* Theorem 10.13 The zeta transform of the cover product is the pointwise product of the zeta-transformed arguments, zeta (f *c g) = (zeta f) * (zeta g) *)
(* Cover_Product_new 的第一个参数是全集(求和的枚举范围), 特别地, 计算 (f *c g) (X) 时，传入的全集是 PowerSet X *)
Theorem BreakUpLemma: forall (f g: list nat -> Z) (Y: list nat), 
  NoDup Y ->
  Zeta (Cover_Product_new (PowerSet Y) f g) Y = Z.mul (Zeta f Y) (Zeta g Y).
Proof.
  intros.
  unfold Zeta, Cover_Product_new.
  erewrite Exchange_Summ; [ | reflexivity].
  erewrite Summ_f_g.
  2:{
    intros.
    erewrite Exchange_Summ; [ | reflexivity].
    erewrite Summ_f_g.
    2:{
      intros.
      rewrite Out_coef.
      rewrite Summ_Test_Union_Eq; [ |tauto |tauto |tauto ].
      rewrite Z.mul_1_r.
      reflexivity.
    }
    rewrite Out_coef.
    rewrite Z.mul_comm.
    reflexivity.
  }
  rewrite Out_coef.
  lia.
Qed.


(*关键定义*)
Print Convolution_new.
Locate Convolution_new.
Print Check_i.
Locate Check_i.

(*关键引理*)
Check Add_sum_one.
Locate Add_sum_one.
Check Union_Length_Empty.
Locate Union_Length_Empty.

(* Theorem 10.15 Fast subset convolution *)
(* f_k(S) := f(S) * [|S| = k].
   (f * g) (X) = summ (i from |X| to 0) ((fi *c g(|X|-i)) X) *)
Theorem Fast_Subset_Convolution: forall (f g: list nat -> Z) (X: list nat) (N: nat),
  NoDup X ->
  N = (Datatypes.length X) ->
  Convolution_new (PowerSet X) f g X = 
  Summ_Of_List 
    (nat) 
    (fun i:nat => Cover_Product_new (PowerSet X) (Check_i i f) (Check_i (N-i) g) X) 
    (nat_list N).
Proof.
  intros.
  unfold Convolution_new.
  erewrite Summ_f_g.
  2:{
    intros.
    erewrite Summ_f_g.
    2:{
      intros.
      assert (forall a:Z, a = Z.mul a 1%Z). { lia. }
      rewrite H3 at 1.
      assert (Datatypes.length x <= N).
      {
        rewrite H0.
        apply Subset_length; [tauto |eapply PowerSet_Element_NoDup; [apply H | apply H1] | ].
        apply PowerSet_Subset; tauto.
      }
      pose proof Add_sum_one N (Datatypes.length x) H4.
      rewrite <- H5.
      rewrite Summ_to_0_eq_Summ_list.
      rewrite <- Out_coef.
      erewrite Summ_f_g.
      2:{
        intros.
        assert (Z.mul (Z.mul (test_eq_union_Z x x0 X) (test_empty_intersect_Z x x0))
 (Nat_eq_Z (Datatypes.length x) x1) = Z.mul (Z.mul (test_eq_union_Z x x0 X) (Nat_eq_Z (Datatypes.length x) x1)) (Nat_eq_Z (Datatypes.length x0) (N-x1))).
        {  
          unfold test_eq_union_Z.
          destruct (test_eq_union x x0 X); [ | lia].
          unfold test_empty_intersect_Z.
          assert (NoDup x). { eapply PowerSet_Element_NoDup. apply H. tauto. }
          assert (NoDup x0). { eapply PowerSet_Element_NoDup. apply H. tauto. }
          pose proof Union_Length_Empty _ _ _ H7 H8 H e.
          destruct (test_empty_intersect x x0).
          - apply H9 in e0.
            unfold Nat_eq_Z.
            destruct (test_eq_nat (Datatypes.length x) x1); [ | lia].
            destruct (test_eq_nat (Datatypes.length x0) (N - x1)); [lia | ].
            rewrite <- H0 in e0.
            rewrite e1 in e0.
            lia.
          - unfold Nat_eq_Z.
            destruct (test_eq_nat (Datatypes.length x) x1); [ | lia].
            destruct (test_eq_nat (Datatypes.length x0) (N - x1)); [ | lia].
            assert (Datatypes.length x + Datatypes.length x0 = Datatypes.length X).
            {
              lia.
            }
            apply H9 in H10.
            tauto.
        }
        assert (forall a b c d e: Z, Z.mul (Z.mul (Z.mul (Z.mul a b) c) d) e = Z.mul (Z.mul a b) (Z.mul (Z.mul c d) e)). { lia. }
        rewrite H8, H7.
        assert (forall a b c d e: Z, Z.mul (Z.mul a b) (Z.mul (Z.mul c d) e) = Z.mul (Z.mul (Z.mul a d) (Z.mul b e)) c). { lia. }
        rewrite H9.
        reflexivity.
      }
      reflexivity.
    }
    erewrite Exchange_Summ2; [ | reflexivity].
    simpl.
    reflexivity.
  }
  erewrite Exchange_Summ2; [ | reflexivity].
  simpl.
  unfold Cover_Product_new, Check_i.
  reflexivity.
Qed.

(* Fast Zeta/Mobius transform half_0 证明了递推式的其中一种情况 (xj = 0) (对应于 ~ In j X) *)
Theorem Fast_Mobius_Transform_0: forall (j n:nat) (X: list nat) (f: list nat -> Z),
In X (PowerSet (list_n_1 n)) -> (0 < j) -> (j <= n) -> ~ In j X -> 
Zeta_j j f X = Zeta_j (j-1) f X.
Proof.
  unfold Zeta_j; intros.
  apply Summ_f_g; intros.
  unfold test_check_j_Z.
  destruct (test_check_j j x X); destruct (test_check_j (j-1) x X); [lia| | | lia].
  - assert (forall n: nat, j - 1 < n -> In n x <-> In n X).
    {
      intros.
      destruct (classic (j = n1)).
      * subst.
        split; [ | tauto].
        apply subseq_in, inpowerset_subseq_eq; tauto.
      * assert (j < n1). { lia. }
        apply i in H6; tauto.
    }
    tauto.
  - assert (forall n: nat, j < n -> In n x <-> In n X).
    {
      intros.
      assert (j - 1 < n1). { lia. }
      apply i in H5; tauto.
    }
    tauto.
Qed.

(* Fast Zeta/Mobius transform half_1 证明了递推式的其中一种情况 (xj = 1) (对应于 In j X) *)
Theorem Fast_Mobius_Transform_1: forall (j n:nat) (X: list nat) (f: list nat -> Z),
In X (PowerSet (list_n_1 n)) -> (0 < j) -> (j <= n) -> In j X -> 
  Zeta_j j f X = 
  Z.add 
  (Zeta_j (j-1) f X) 
  (Zeta_j (j-1) f (filter (fun n0:nat => negb (Nat_eq_b j n0)) X)).
Proof.
  unfold Zeta_j; intros.
  pose proof Summ_constraint_X_Y.
  assert (NoDup X). { eapply PowerSet_Element_NoDup; [ | apply H]. apply NoDup_list_n_1. }
  assert (NoDup (PowerSet X)). { apply PowerSet_NoDup. tauto. } 
  assert (In (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X) (PowerSet X)).
  { apply inpowerset_subseq_eq. apply filter_subseq. }
  assert (NoDup (PowerSet (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))).
  { 
    apply PowerSet_NoDup.
    eapply PowerSet_Element_NoDup; [ | ].
    2:{ apply inpowerset_subseq_eq. apply filter_subseq. }
    tauto.
  }
  assert (Subset (list nat) (PowerSet (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X)) (PowerSet X)).
  {
    eapply Subset_PowerSet; [tauto | | tauto].
    eapply subseq_NoDup; [ | apply H4].
    apply filter_subseq.
  }
  pose proof H3 (PowerSet X) _ (fun x : list nat =>
    Z.mul (f x) (test_check_j_Z (j - 1) x (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))) H5 H7 H8.
  rewrite H9.
  clear H9 H3.
  rewrite Summ_f_plus_g.
  unfold f_x_test_in; simpl.
  erewrite Summ_f_g; [reflexivity | intros; simpl].
  assert (test_check_j_Z j x X = Z.add (test_check_j_Z (j-1) x X) (Z.mul (test_check_j_Z (j - 1) x (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X)) (test_in_list_Z x
   (PowerSet (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))))).
  {
    unfold test_in_list_Z.
    destruct (test_in_list x (PowerSet (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))); simpl.
    - destruct (classic (In j x)).
      apply inpowerset_subseq_eq in i as H10.
      pose proof subseq_in _ _ j H10 H9.
      apply filter_In in H11.
      destruct H11.
      unfold Nat_eq_b in H12.
      destruct (Nat.eq_dec j j); [inversion H12 | tauto].
      assert (test_check_j_Z (j-1) x X = 0%Z).
      {
        unfold test_check_j_Z.
        destruct (test_check_j (j-1) x X); [ | lia].
        assert (j - 1 < j). { lia. }
        apply i0 in H10.
        tauto.
      }
      rewrite H10; simpl.
      assert (forall a:Z, Z.mul a 1%Z = a). { lia. }
      rewrite H11.
      unfold test_check_j_Z.
      destruct (test_check_j j x X); destruct (test_check_j (j - 1) x (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X)); [lia | | | lia].
      -- assert ((forall n : nat,
      j - 1 < n ->
      In n x <-> In n (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))).
         {
           intros.
           split; intros.
           apply filter_In.
           assert (In n1 X).
           { apply inpowerset_subseq_eq in H3 as H14.
             eapply subseq_in. apply H14. tauto. }
           split.
           * tauto.
           * unfold Nat_eq_b.
             destruct (Nat.eq_dec j n1); [ | tauto].
             rewrite <- e in H13; tauto.
           * apply filter_In in H13.
             destruct H13.
             unfold Nat_eq_b in *.
             destruct (Nat.eq_dec j n1); [inversion H14 | ].
             assert (j < n1). { lia. }
             apply i0 in H15.
             tauto.
        }
        tauto.
      -- assert (forall n: nat, j < n -> In n x <-> In n X).
         {
           intros.
           split; intros.
           assert (In n1 X).
           { apply inpowerset_subseq_eq in H3 as H14.
             eapply subseq_in. apply H14. tauto. }
           tauto.
           assert (j-1 < n1). { lia. }
           pose proof i0 _ H14.
           apply H15.
           apply filter_In.
           split; [tauto | ].
           unfold Nat_eq_b.
           destruct (Nat.eq_dec j n1); [lia | tauto].
         }
         tauto.
    - assert (forall a b : Z, Z.add a (Z.mul b 0%Z) = a). { lia. }
      rewrite H9.
      destruct (classic (In j x)).
      -- unfold test_check_j_Z.
         destruct (test_check_j j x X); destruct (test_check_j (j-1) x X); [lia | | | lia].
         * assert (forall n:nat, j-1 < n -> In n x <-> In n X).
           {
             intros; split; intros.
             destruct (classic (j = n2)); [subst; tauto| ].
             assert (j < n2). { lia. }
             apply i in H14; tauto.
             destruct (classic (j = n2)); [subst; tauto| ].
             assert (j < n2). { lia. }
             apply i in H14; tauto.
           }
           tauto.
         * assert (forall n : nat, j < n -> In n x <-> In n X).
           {
             intros; split; intros.
             assert (j - 1 < n2). { lia. }
             apply i in H13; tauto.
             assert (j - 1 < n2). { lia. }
             apply i in H13; tauto.
           }
           tauto.
      -- assert (In x (PowerSet (filter (fun n0 : nat => negb (Nat_eq_b j n0)) X))).
         {
           apply inpowerset_subseq_eq.
           apply subseq_filter_subseq.
           * apply inpowerset_subseq_eq, H3.
           * intros.
             unfold Nat_eq_b.
             destruct (Nat.eq_dec j n1).
             ** rewrite <- e in H11; tauto.
             ** tauto.
         }
         tauto.
   }     
  rewrite H9.
  lia.
Qed.

(* 证明了 zeta_j n 和 原先 zeta 变换的结果是一致的, 全集V是 list_n_1 n, 函数变量 X 是 (list_n_1 n) 的子集 *)
Theorem Zeta_n_eq_Zeta:
  forall (n:nat) (f: list nat -> Z) (X: list nat),
  subseq X (list_n_1 n) ->
  Zeta_j n f X = Zeta f X.
Proof.
  intros;unfold Zeta_j, Zeta.
  erewrite Summ_f_g;[reflexivity|].
  intros.
  assert(test_check_j_Z n x X = 1%Z).
  {
    unfold test_check_j_Z.
    destruct test_check_j;[reflexivity|].
    assert ((forall n0 : nat, n < n0 -> In n0 x <-> In n0 X)).
    {
      split; intros.
      - apply inpowerset_subseq_eq in H0 as H3.
        eapply subseq_in; [apply H3 | tauto].
      - assert (forall n0: nat, n < n0 -> In n0 x <-> In n0 X).
        {
          intros.
          pose proof Bign_not_in_list_n_1 n2.
          apply H4 in H3 as H5.
          split; intros.
          * pose proof In_PowerSet_In n2 x X H6 H0; tauto.
          * pose proof subseq_in _ _ _ H H6; tauto.
        }
        tauto.
    }
    tauto.
  }
  rewrite H1.
  lia.
Qed.


End Fast_Zeta_Mobius_Transforms.