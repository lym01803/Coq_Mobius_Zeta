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

Module Lemmas.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Import Mobius_Definition.Def.


Lemma App_eq:
  forall (U:Type) (l1 l2 l: list U),
  l1 = l2 -> l1 ++ l = l2 ++ l.
Proof.
  intros.
  rewrite H.
  tauto.
Qed.
Lemma Same_list_same_map:
  forall (U1 U2:Type) (x y: list U1) (f: U1 ->U2),
  x = y -> map f x = map f y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Summ_list_listsum_eq:
  forall (U:Type) f l,
  Summ_Of_List U f l = list_Z_sum (map f l).
Proof.
  induction l;[reflexivity|].
  simpl. rewrite IHl. lia.
Qed.

Lemma same_list_same_sum:
  forall (x y: list Z),
  x = y -> list_Z_sum x = list_Z_sum y.
Proof.
  intros.
  rewrite H.
  tauto.
Qed.

Lemma Nothingfit_nil:
  forall (U: Type) (l: list U) f,
  (forall x, In x l -> f x = false) ->
  filter f l = [].
Proof.
  induction l.
  - intros; reflexivity.
  - simpl; intros.
    specialize (IHl f).
    assert ((forall x : U, In x l -> f x = false)).
    { intros. apply H. tauto. }
    apply IHl in H0.
    assert (f a = false).
    {
      specialize (H a).
      apply H. tauto.
    }
    rewrite H1.
    tauto.
Qed.

Lemma AddOne_map_length:
  forall l1 l2 a,
  map (Datatypes.length (A:=nat)) l1 = map (Datatypes.length (A:=nat)) l2 -> 
  map (Datatypes.length (A:=nat)) (AddOne a l1) = map (Datatypes.length (A:=nat)) (AddOne a l2).
Proof.
  induction l1, l2; intros.
  - reflexivity.
  - inversion H.
  - inversion H.
  - simpl.
    inversion H.
    pose proof IHl1 l2 a0 H2.
    rewrite H0.
    reflexivity.
Qed.

Lemma overflow_0:
  forall n i, i > n -> forall x, x<= n -> Nat_eq_Z x i = 0%Z.
Proof.
  intros. induction n.
  - inversion H0.
    unfold Nat_eq_Z.
    destruct (test_eq_nat 0 i);[lia|reflexivity].
  - inversion H0. 
    * rewrite <- H1 in H.
      rewrite <- H1.
      unfold Nat_eq_Z.
      destruct (test_eq_nat x i);[lia|reflexivity].
    * assert(i > n). { lia. }
      apply IHn;[apply H3|apply H2].
Qed.

Lemma summ_overflow:
  forall n i, i > n -> Summ_From_n_to_0 n (Nat_eq_Z i) = 0 %Z.
Proof.
  induction n;intros.
  - simpl.
    apply neq_and_testeq_false.
    unfold Nat.eq. lia.
  - simpl.
    assert (Nat_eq_Z i (S n) = 0%Z).
    {
      apply neq_and_testeq_false.
      unfold Nat.eq. lia.
    }
    rewrite H0.
    assert (i > n). {lia. }
    pose proof IHn i H1.
    rewrite H2.
    reflexivity.
Qed.

Lemma Add_sum_one:
  forall n i, i <= n ->
  Summ_From_n_to_0 n (Nat_eq_Z i) = 1%Z.
Proof.
  intros.
  induction n.
  - inversion H; subst.
    simpl. apply Eq_and_test_eq.
    unfold Nat.eq. lia.
  - inversion H.
    * simpl.
      assert (Nat_eq_Z (S n) (S n) = 1%Z).
      {
        apply Eq_and_test_eq.
        unfold Nat.eq. lia.
      }
      assert (Summ_From_n_to_0 n (Nat_eq_Z (S n)) = 0%Z).
      { apply summ_overflow. lia. }
      lia.
    * simpl. 
      assert (Nat_eq_Z i (S n) = 0%Z).
      {
        apply neq_and_testeq_false.
        unfold Nat.eq. lia.
      }
      apply IHn in H1.
      lia.
Qed.

Fact MinusOnePower_Add: forall (a b: nat), Z.mul (MinusOnePower a) (MinusOnePower b) = MinusOnePower (a + b).
Proof.
  intros.
  induction b.
  + simpl.
    rewrite Z.mul_1_r.
    assert (a+0 = a). { lia. }
    rewrite H.
    reflexivity.
  + simpl.
    assert (S (a+b) = a + S b). { lia. }
    rewrite <- H.
    simpl.
    rewrite <- IHb.
(*     Search Z.mul. *)
    rewrite <- Z.mul_opp_comm.
(*     Search Z.mul. *)
    rewrite Zopp_mult_distr_l.
    reflexivity.
Qed.

(* 列表求和的基本性质之一 *)
Lemma Summ_List_App: forall (U: Type) (f: U -> Z) (A B: list U),
  Z.add (Summ_Of_List _ f A) (Summ_Of_List _ f B) = Summ_Of_List _ f (A ++ B).
Proof.
  intros.
  induction A.
  + simpl.
    reflexivity.
  + simpl.
    rewrite <- IHA.
    apply Zplus_assoc_reverse.
Qed.

Fact F_zero_summ_zero (U: Type): forall (S: list U), Summ_Of_List _ (fun (_: U) => 0%Z) S = 0%Z.
Proof.
  intros.
  induction S.
  - simpl; reflexivity.
  - simpl; apply IHS.
Qed.

Lemma Exchange_Summ (U: Type) (f g: U -> U -> Z):
  (forall (x y: U), f x y = g y x) -> 
  (forall (S1 S2: list U), Summ_Of_List U (fun (I: U) => Summ_Of_List U (f I) S2) S1 =
   Summ_Of_List U (fun (J: U) => Summ_Of_List U (g J) S1) S2).
Proof.
  intros.
  revert S2.
  induction S1.
  + simpl; intros.
    rewrite F_zero_summ_zero.
    reflexivity.
  + simpl; intros.
    assert (Summ_Of_List U (fun J : U => (g J a + Summ_Of_List U (g J) S1)%Z) S2 =
    (Summ_Of_List U (fun J : U => g J a) S2)%Z + (Summ_Of_List U (fun J : U =>Summ_Of_List U (g  J) S1) S2))%Z.
    { induction S2;[reflexivity|simpl;lia]. }
    rewrite H0.
    pose proof IHS1 S2.
    rewrite H1.
    assert (forall S: list U, Summ_Of_List U (f a) S = Summ_Of_List U (fun J: U => g J a) S).
    {
      induction S; intros;[reflexivity|].
      simpl.
      rewrite IHS, H.
      reflexivity.
    }
    rewrite H2.
    reflexivity.
Qed.

Lemma Permutation_Summ: forall (U: Type) (l1 l2: list U) (f: U -> Z),
  Permutation l1 l2 -> Summ_Of_List U f l1 = Summ_Of_List U f l2.
Proof.
  intros.
  induction H.
  + reflexivity.
  + simpl.
    rewrite IHPermutation.
    reflexivity.
  + simpl.
    lia.
  + lia.
Qed.


Fact example_test_in_z_1: forall (n: nat) (l: list nat),
  In n l -> Test_In_Z n l = 1%Z.
Proof.
  intros.
  unfold Test_In_Z.
  destruct (test_in n l).
  - reflexivity.
  - tauto.
Qed.

Fact example_test_in_z_0: forall (n: nat) (l: list nat),
  ~ In n l -> Test_In_Z n l = 0%Z.
Proof.
  intros.
  unfold Test_In_Z.
  destruct (test_in n l).
  - tauto.
  - reflexivity.
Qed.


Lemma App_Complement: forall (subL L : list nat),
  (forall x: nat, In x subL -> In x L) -> NoDup subL -> NoDup L ->
  Permutation (subL ++ (filter (fun n:nat => negb (Test_In n subL)) L)) L.
Proof.
  intros.
  revert H H0.
  revert subL.
  induction L; intros.
  + induction subL.
    - simpl; reflexivity.
    - pose proof in_eq a subL.
      apply H in H2.
      apply in_nil in H2; tauto.
  + simpl.
    remember (Test_In a subL).
    destruct b.
    2:{ 
        assert (~In a subL).
        { 
          pose proof classic (In a subL).
          destruct H2;[|tauto].
          apply In_and_test_in in H2. 
          rewrite <- Heqb in H2. inversion H2. 
        }
        simpl.
        apply Permutation_sym.
        apply Permutation_cons_app.
        assert (forall x: nat, In x subL -> In x L).
        {  intros.
           pose proof H _ H3 as H4; inversion H4.
           - rewrite <- H5 in H3; tauto.
           - tauto. 
        }
        pose proof NoDup_cons_iff a L.
        apply H4 in H1.
        destruct H1.
        pose proof IHL H5 subL H3 H0.
        apply Permutation_sym, H6. 
      }
    simpl.
    assert (Test_In a subL = true). { rewrite Heqb. reflexivity. }
    clear Heqb.
    apply In_and_test_in in H2.
    apply Add_inv in H2; destruct H2 as [subL' H2].
    apply Permutation_Add in H2 as H3.
    rewrite <- H3.
    rewrite Permutation_app_comm, Permutation_sym; [ reflexivity | ].
    apply Permutation_cons_app, Permutation_sym.
    assert (forall x:nat, In x subL' -> In x L).
    { 
      intros. 
      pose proof classic (x=a) as H5; destruct H5.
      - pose proof NoDup_Add H2.
        rewrite H5 in H4; tauto.
      - pose proof in_cons a x subL' H4.
        pose proof Add_in H2.
        apply H7, H in H6.
        apply in_inv in H6; destruct H6;[lia|tauto].
    }
    pose proof NoDup_cons_iff.
    apply H5 in H1.
    destruct H1.
    pose proof NoDup_Add H2.
    apply H7 in H0.
    destruct H0.
    pose proof IHL H6 subL' H4 H0.
    rewrite Permutation_app_comm.
    assert ((filter (fun n : nat => negb (Test_In n subL')) L) = (filter (fun n : nat => negb (Test_In n subL)) L)).
    { 
      apply filter_ext_in.
      intros.
      assert (a0 <> a). 
      { 
        pose proof classic (a = a0). 
        destruct H11;[rewrite <- H11 in H10; tauto|lia]. 
      }
      unfold Test_In.
      destruct (test_in a0 subL').
      - destruct test_in; [reflexivity | ].
        apply in_cons with(a:=a) in i.
        pose proof Permutation_in _ H3 i; tauto.
      - destruct test_in; [ | reflexivity].
        apply Permutation_sym in H3.
        pose proof Permutation_in _ H3 i.
        apply in_inv in H12.
        destruct H12; [lia | tauto ].
    }
    rewrite <- H10.
    exact H9.
Qed.

Lemma App_Complement_list: forall (subL L : list (list nat)),
  (forall x: list nat, In x subL -> In x L) -> NoDup subL -> NoDup L ->
  Permutation (subL ++ (filter (fun l: (list nat) => negb (test_in_list_b l subL)) L)) L.
Proof.
  intros.
  revert H H0.
  revert subL.
  induction L; intros.
  + induction subL.
    - simpl; reflexivity.
    - pose proof in_eq a subL.
      apply H in H2.
      apply in_nil in H2; tauto.
  + simpl.
    remember (test_in_list_b a subL).
    destruct b.
    2:
    { 
        assert (~In a subL).
        { 
          pose proof classic (In a subL).
          destruct H2;[|tauto].
          apply In_and_test_in_list in H2. 
          rewrite <- Heqb in H2. inversion H2. 
        }
        simpl.
        apply Permutation_sym.
        apply Permutation_cons_app.
        assert (forall x: list nat, In x subL -> In x L).
        {  
           intros.
           pose proof H _ H3 as H4.
           inversion H4;[|tauto].
           rewrite <- H5 in H3; tauto.
        }
        pose proof NoDup_cons_iff a L.
        apply H4 in H1.
        destruct H1.
        pose proof IHL H5 subL H3 H0.
        apply Permutation_sym, H6. 
    }
    simpl.
    assert (test_in_list_b a subL = true). { rewrite Heqb. reflexivity. }
    clear Heqb.
    apply In_and_test_in_list in H2.
    apply Add_inv in H2; destruct H2 as [subL' H2].
    apply Permutation_Add in H2 as H3.
    rewrite <- H3.
    rewrite Permutation_app_comm, Permutation_sym; [ reflexivity | ].
    apply Permutation_cons_app, Permutation_sym.
    assert (forall x: list nat, In x subL' -> In x L).
    { 
      intros. 
      pose proof classic (x=a) as H5; destruct H5.
      - pose proof NoDup_Add H2.
        rewrite H5 in H4; tauto.
      - pose proof in_cons a x subL' H4.
        pose proof Add_in H2.
        apply H7, H in H6.
        apply in_inv in H6; destruct H6;[|tauto].
        destruct H5. rewrite H6. reflexivity.
    }
    pose proof NoDup_cons_iff.
    apply H5 in H1.
    destruct H1.
    pose proof NoDup_Add H2.
    apply H7 in H0.
    destruct H0.
    pose proof IHL H6 subL' H4 H0.
    rewrite Permutation_app_comm.
    assert (
            (filter (fun n : list nat => negb (test_in_list_b n subL')) L) = 
            (filter (fun n : list nat => negb (test_in_list_b n subL)) L)).
    { 
      apply filter_ext_in.
      intros.
      assert (a0 <> a). 
      { 
        pose proof classic (a = a0). 
        destruct H11. 
        - rewrite <- H11 in H10; tauto. 
        - destruct (classic (a0 = a)). 
          rewrite H12 in H11. 
          destruct H11. 
          reflexivity. 
          apply H12. 
      }
      unfold test_in_list_b.
      destruct (test_in_list a0 subL').
      - destruct test_in_list; [reflexivity | ].
        apply in_cons with(a:=a) in i.
        pose proof Permutation_in _ H3 i; tauto.
      - destruct test_in_list; [ | reflexivity].
        apply Permutation_sym in H3.
        pose proof Permutation_in _ H3 i.
        apply in_inv in H12.
        destruct H12; [ | tauto ].
        destruct H11.
        rewrite H12; tauto.
    }
    rewrite <- H10.
    exact H9.
Qed.

Lemma Summ_f_g: forall (U:Type) (f g: U -> Z) (L: list U),
  (forall x:U, In x L -> f x = g x) -> Summ_Of_List _ f L = Summ_Of_List _ g L.
Proof.
  intros.
  induction L.
  - simpl; reflexivity.
  - simpl.
    pose proof in_eq a L.
    apply H in H0.
    rewrite H0.
    assert (forall x:U, In x L -> f x = g x).
    { 
      intros.
      apply in_cons with (a:= a) in H1.
      apply H in H1.
      tauto. 
    }
    apply IHL in H1.
    lia.
Qed.

Lemma Summ_constraint_X_Y: forall (X Y: list (list nat)) (f: list nat -> Z),
  NoDup X ->
  NoDup Y ->
  Subset _ Y X -> 
  Summ_Of_List _ f Y = Summ_Of_List _ (f_x_test_in f Y) X. 
Proof.
  intros.
  assert (Summ_Of_List (list nat) f Y = Z.add (Summ_Of_List (list nat) f Y)%Z 0%Z). { lia. }
  rewrite H2; clear H2.
  pose proof F_zero_summ_zero (list nat) (filter (fun l: (list nat) => negb (test_in_list_b l Y)) X).
  rewrite <- H2.
  pose proof Summ_f_g.
  pose proof f_x_test_in_val_1 f Y.
  pose proof H3 _ (f_x_test_in f Y) f Y H4.
  rewrite <- H5.
  pose proof f_x_test_in_val_0 f Y.
  assert (forall x : list nat, In x (filter (fun l : list nat => negb (test_in_list_b l Y)) X) -> 
  f_x_test_in f Y x = always_zero x).
  { 
    intros.
    apply H6.
    apply filter_In in H7.
    destruct H7.
    unfold test_in_list_b in *.
    destruct (test_in_list x Y).
    - inversion H8.
    - tauto.
  }
  pose proof H3 _ (f_x_test_in f Y) always_zero (filter (fun l : list nat => negb (test_in_list_b l Y)) X) H7.
  unfold always_zero in H8.
  rewrite <- H8.
  rewrite Summ_List_App.
  apply Permutation_Summ.
  apply App_Complement_list;[apply H1| | ];tauto.
Qed.

Lemma list_neq_sym: forall (U:Type) (x y:list U),
  x <> y <-> y <> x.
Proof.
  split;intros.
  + pose proof classic (y = x).
    destruct H0.
    - rewrite H0 in H.
      destruct H.
      reflexivity.
    - tauto.
  + pose proof classic (x = y).
    destruct H0. 
    - rewrite H0 in H.
      destruct H.
      reflexivity.
    - exact H0.
Qed.

Lemma Binomial_minusone_pre: forall a (l: list (list nat)),
  (Summ_Of_List (list nat) (MinusOnetoLen) (AddOne a l) + 
  Summ_Of_List (list nat) (MinusOnetoLen) l)%Z = 0%Z.
Proof.
  unfold MinusOnetoLen.
  induction l; simpl;[reflexivity|lia].
Qed.

Lemma Binomial_minusone: forall (l: list nat),
  (l = nil -> Summ_Of_List _ MinusOnetoLen (PowerSet l) = 1%Z) /\
  (l <> nil -> Summ_Of_List _ MinusOnetoLen (PowerSet l) = 0%Z) .
Proof.
  split; intros.
  + rewrite H.
    reflexivity.
  + induction l.
    - destruct H.
      reflexivity.
    - simpl.
      rewrite <- Summ_List_App.
      apply Binomial_minusone_pre.
Qed.

Lemma NoDup_app: forall (U: Type) (l1 l2: list U), NoDup l1 -> NoDup l2 -> (forall x:U, In x l2 -> ~ In x l1) -> NoDup (l1 ++ l2).
Proof.
  intros.
  revert H1 H.
  revert l1.
  induction l2; intros.
  - rewrite <- app_nil_end.
    exact H.
  - eapply Permutation_NoDup.
    apply Permutation_middle.
    apply NoDup_cons_iff in H0; destruct H0.
    pose proof IHl2 H2 (a::l1).
    assert (forall x: U, In x l2 -> ~ In x (a :: l1)).
    { intros.
      destruct (classic (In x (a::l1))).
      * apply in_inv in H5.
        apply in_cons with (a:=a) in H4 as H6.
        apply H1 in H6. 
        destruct H5; [ | tauto].
        rewrite <- H5 in H4; tauto .
      * tauto.
    }
    apply H3 in H4.
    apply H4.
    apply NoDup_cons; [ | apply H ].
    pose proof in_eq a l2.
    apply H1 in H5.
    exact H5.
Qed.

Fact MinusOnePower_Double: forall n: nat, MinusOnePower (n + n) = 1%Z.
Proof.
  intros.
  induction n.
  - simpl. lia.
  - assert (S n + S n = S (S (n + n))).
    { lia. }
    rewrite H.
    simpl.
    rewrite IHn.
    lia.
Qed.

Fact MinusOnePower_Minus_to_Add: forall (n m : nat), m <= n -> MinusOnePower (n-m) = MinusOnePower (n+m).
Proof.
  intros.
  assert (MinusOnePower (n - m) = Z.mul (MinusOnePower (n - m)) (MinusOnePower (m + m))).
  { rewrite MinusOnePower_Double. lia. }
  rewrite MinusOnePower_Add in H0.
  assert (n - m + m + m = n + m). 
  { remember (n-m).
    rewrite Nat.add_comm, Nat.add_assoc.
    rewrite Heqn0.
    erewrite le_plus_minus_r; [reflexivity | tauto ].
  }
  rewrite Nat.add_assoc in H0.
  rewrite H1 in H0.
  exact H0.
Qed.

Lemma Forall_trans:
  forall (U:Type) (P Q R:U -> Prop),
  (forall x: U, P x-> Q x) -> (forall x: U, Q x-> R x) -> (forall x : U, P x-> R x).
Proof.
  intros.
  apply H0, H, H1.
Qed.

Fact Addone_not_in_r: forall x l a,
  In (a::x) (AddOne a l) -> In x l.
Proof.
  intros.
  induction l.
  - pose proof in_nil.
    tauto.
  - assert (AddOne a (a0 :: l) = (a::a0) :: (AddOne a l)).
    { simpl. reflexivity. }
    rewrite H0 in H.
    apply in_inv in H.
    destruct H.
    2:{
      apply IHl in H.
      apply in_cons, H.
    }
    inversion H.
    apply in_eq.
Qed.

Lemma Addone_not_in:
  forall x l a,
  ~In x l -> ~In (a :: x) (AddOne a l).
Proof.
  intros.
  pose proof classic (In (a :: x) (AddOne a  l)).
  destruct H0;[|tauto].
  apply Addone_not_in_r in H0.
  tauto.
Qed.

Lemma Add_NoDup: forall (l: list (list nat)) (a: nat),
  (forall x, In x l -> ~In a x) -> NoDup l -> NoDup (AddOne a l).
Proof.
  intros. 
  induction l; simpl.
  + apply NoDup_nil.
  + assert (forall x: list nat, (fun x : list nat => In x l) x -> (fun x : list nat => In x (a0 :: l)) x).
    {
      intros.
      apply in_cons.
      exact H1.
    }
    pose proof Forall_trans (list nat) (fun x: list nat => In x l)
                                       (fun x: list nat => In x (a0 :: l))
                                       (fun x: list nat => ~In a x) H1 H.
    pose proof IHl H2.
    apply NoDup_cons_iff in H0.
    apply NoDup_cons_iff.
    destruct H0.
    apply Addone_not_in with (a:=a) in H0.
    apply H3 in H4.
    tauto.
Qed.

Lemma App_nil_equ:
  forall (U: Type) (l : list U),
  l ++ [] = l.
Proof.
  induction l;simpl;[reflexivity|].
  rewrite IHl.
  reflexivity.
Qed.

Lemma NoDup_App: forall (U: Type) (l l2: list U), 
  NoDup l -> NoDup l2 -> (forall x, In x l -> ~In x l2) ->  NoDup (l ++ l2).
Proof.
  intros.
  induction l2; simpl;[rewrite App_nil_equ; apply H|].
  assert (Add a (l ++ l2) (l ++ a :: l2)). { apply Add_app. }
  pose proof NoDup_Add H2.
  apply H3.
  split.
  - apply NoDup_cons_iff in H0.
    destruct H0.
    apply IHl2;[apply H4|].
    intros.
    specialize (H1 x).
    apply H1 in H5.
    apply not_in_cons in H5.
    tauto.
  - unfold not; intros.
    apply in_app_iff in H4.
    destruct H4.
    * specialize (H1 a).
      apply H1 in H4.
      destruct H4.
      apply in_eq.
    * apply NoDup_cons_iff in H0.
      tauto.
Qed.

Lemma In_add_a_l:
  forall a l x,
  In x (AddOne a l) -> In a x.
Proof.
  induction l;simpl; intros.
  - destruct H.
  - destruct H. 
    * rewrite <- H.
      apply in_eq.
    * apply IHl, H.
Qed.

Lemma Add_remove:
  forall x l a,
  In x (AddOne a l) -> exists y, x = a:: y /\ In y l.
Proof.
  intros.
  induction l.
  - destruct H.
  - simpl in H.
    destruct H.
    * exists a0.
      inversion H.
      split;[reflexivity| apply in_eq].
    * apply IHl in H.
      destruct H as [? [? ?]].
      exists x0.
      split;[apply H|apply in_cons, H0].
Qed.

Lemma not_int_Ps:
  forall l a,
  ~In a l -> (forall x, In x (PowerSet l) -> ~In a x).
Proof.
  induction l; simpl.
  - intros;destruct H0.
    * rewrite <- H0. apply in_nil.
    * destruct H0.
  - intros.
    apply not_in_cons in H.
    destruct H.
    apply in_app_iff in H0.
    destruct H0.
    * unfold not.
      intros.
      apply Add_remove in H0.
      destruct H0 as [? [? ?]].
      pose proof IHl a0 H1 x0 H3.
      rewrite H0 in H2.
      inversion H2. 
      ++ rewrite H5 in H.
         destruct H.
         reflexivity.
      ++ tauto.
    * apply IHl;[apply H1| apply H0].
Qed.

Lemma constrain_app:
  forall (U:Type) F G (l: list U),
  (forall x, {F x} + {~ F x})-> (forall x, F x <-> G x = true) ->
  (forall x, ~F x <-> G x = false)->
  Permutation (filter G l ++ (filter (fun x=> negb(G x)) l)) l.
Proof.
  intros.
  induction l.
  - simpl. apply perm_nil.
  - specialize (X a).
    destruct X.
    * apply H in f.
      simpl. rewrite f. simpl.
      apply Permutation_cons.
      + reflexivity.
      + apply IHl.
    * apply H0 in n.
      simpl.
      rewrite n.
      simpl.
      pose proof Permutation_middle (filter G l) (filter (fun x : U => negb (G x)) l) a.
      eapply perm_trans.
      apply Permutation_sym.
      apply Permutation_middle.
      apply Permutation_cons. 
      + reflexivity.
      + apply IHl.
Qed.

Lemma PowerSet_NoDup: forall l, NoDup l -> NoDup (PowerSet l).
Proof.
  intros. induction l; simpl.
  - apply NoDup_cons_iff.
    split;[apply in_nil|apply NoDup_nil].
  - apply NoDup_App.
    * apply Add_NoDup.
      + intros. 
        apply not_int_Ps with (l := l).
        ++ apply NoDup_cons_iff, H.
        ++ apply H0.
      + apply IHl.
        apply NoDup_cons_iff in H.
        tauto.
    * apply NoDup_cons_iff in H.
      apply IHl. tauto.
    * intros. unfold not. intros.
      pose proof not_int_Ps l a.
      apply NoDup_cons_iff in H.
      destruct H.
      pose proof H2 H.
      apply In_add_a_l in H0.
      pose proof H4 x H1.
      tauto.
Qed.
   
Lemma PowerSet_Element_NoDup: 
  forall l subl ,NoDup l -> In subl (PowerSet l) -> NoDup subl.
Proof.
  induction l; intros.
  - destruct H0; subst;[apply NoDup_nil| destruct H0].
  - simpl in H0.
    apply in_app_iff in H0.
    destruct H0.
    * apply NoDup_cons_iff in H.
      destruct H.
      apply Add_remove in H0.
      destruct H0 as [? [? ?]].
      specialize (IHl x).
      rewrite H0.
      apply NoDup_cons_iff.
      split.
      + pose proof not_int_Ps _ _ H _ H2.
        exact H3.
      + apply IHl;[apply H1|apply H2].
    * apply NoDup_cons_iff in H.
      apply IHl;[tauto|apply H0].
Qed.


Lemma PowerSet_Subset: forall l subl, In subl (PowerSet l) -> Subset _ subl l.
Proof.
  induction l; intros.
  - destruct H; subst.
    * unfold Subset. tauto.
    * destruct H.
  - unfold Subset in *.
    intros. simpl in H.
    apply in_app_iff in H.
    destruct H.
    * apply Add_remove in H.
      destruct H as [? [? ?]].
      subst.
      specialize (IHl x).
      pose proof IHl H1 u.
      destruct H0.
      + rewrite H0. apply in_eq.
      + apply in_cons, H, H0.
    * apply in_cons, IHl with (subl:=subl);[apply H|apply H0].
Qed.

Lemma subset_nil: forall (x:Type) u, Subset x u [] <-> u = [].
Proof.
  unfold Subset.
  split;intros.
  - induction u;[reflexivity|].
    pose proof in_eq a u.
    pose proof H a H0.
    destruct H1.
  - rewrite H in H0.
    exact H0.
Qed.


Lemma empty_subset: forall (l: list nat), In [] (PowerSet l).
Proof.
  intros.
  induction l; simpl.
  - left. reflexivity.
  - apply in_app_iff.
    right. apply IHl.
Qed.

Lemma Subset_app:
  forall (U:Type) (x l: list U) a,
  Subset U (a::x) l -> Subset U x l.
Proof.
  intros.
  unfold Subset in *.
  induction x.
  - intros. destruct H0.
  - intros. 
    specialize (H u).
    apply in_cons with (a:= a) in H0.
    apply H, H0.
Qed.

Lemma In_Permutation_pre: forall (U: Type) (a:U) l,
  In a l -> exists l', Permutation l (a::l').

Proof.
  intros.
  induction l.
  - apply in_nil in H; tauto.
  - apply in_inv in H.
    destruct H.
    * subst.
      exists l.
      apply Permutation_refl.
    * apply IHl in H as H1.
      destruct H1.
      exists (a0::x).
      rewrite H0.
      apply perm_swap.
Qed.


Lemma In_Permutation: forall (a: nat) (l: list nat), 
  In a l -> exists (l': list nat), Permutation l (a::l').
Proof.
  apply In_Permutation_pre.
Qed.

Lemma Subset_length: forall (l subl: list nat), NoDup l -> NoDup subl -> Subset _ subl l -> 
  Datatypes.length subl <= Datatypes.length l.
Proof.
  intro.
  intro.
  revert l.
  induction subl; unfold Subset; intros.
  - simpl; lia.
  - simpl.
    pose proof in_eq a subl.
    apply H1 in H2.
    apply In_Permutation in H2; destruct H2 as [l' ?].
    assert (Subset nat subl l').
    { 
      unfold Subset; intros.
      pose proof in_cons a u subl H3.
      apply H1 in H4.
      assert (In u (a::l')). 
      { 
        eapply Permutation_in.
        apply H2.
        apply H4. 
      }
      apply in_inv in H5.
      destruct H5; [ | tauto].
      apply NoDup_cons_iff in H0.
      rewrite <- H5 in H3; tauto.
    }
    pose proof IHsubl l'.
    assert (NoDup (a::l')). { eapply Permutation_NoDup. apply H2. apply H. }
    apply NoDup_cons_iff in H5.
    destruct H5.
    apply NoDup_cons_iff in H0.
    destruct H0.
    pose proof H4 H6 H7 H3.
    pose proof Permutation_length H2.
    rewrite H9; simpl.
    lia.
Qed.

Lemma Subset_merge :
  forall (U: Type) (a b c: list U),
  Subset U (a ++ b) c -> Subset U a c /\ Subset U  b c.
Proof.
  intros.
  induction a.
  + unfold Subset in *.
    rewrite app_nil_l in H.
    split;intros;[destruct H0| apply H, H0].
  + assert ((a :: a0) ++ b = a:: (a0 ++ b)). { reflexivity. }
    rewrite H0 in H.
    pose proof Subset_app _ (a0 ++ b) c a H.
    apply IHa in H1.
    destruct H1.
    split.
    - unfold Subset in *.
      intros.
      specialize (H u).
      rewrite <- H0 in H.
      assert (In u (a :: a0) -> (In u (a :: a0) \/ In u b)). {intros. left. tauto. }
      pose proof in_or_app (a::a0) b u.
      apply H, H5, H4, H3.
    - apply H2.
Qed.

Lemma Add_a_in:
  forall a l x,
  In x l -> In (a::x) (AddOne a l).
Proof.
  induction l; intros.
  - destruct H.
  - apply in_inv in H.
    destruct H.
    * subst. simpl.
      left. reflexivity.
    * simpl. right.
      apply IHl, H.
Qed.

Lemma PowerSet_half_in:
  forall a l x,
  In x (PowerSet l) -> In (a :: x) (PowerSet (a :: l)).
Proof.
  intros. simpl.
  apply in_app_iff.
  left. apply Add_a_in, H.
Qed.
    

Lemma Subset_app2:
  forall (U:Type) (x l: list U) a,
  Subset U (a::x) l -> Subset U x l /\ In a l.
Proof.
  intros. split.
  apply Subset_app with a, H.
  unfold Subset in H.
  specialize (H a).
  apply H,in_eq.
Qed.

Lemma Per_add:
  forall (U:Type) (a:U) l,
  In a l -> exists y, Permutation (a :: y) l.
Proof.
  intros.
  pose proof Add_inv _ _ H.
  destruct H0.
  exists x.
  apply Permutation_Add, H0.
Qed.

Lemma InPs_in:
  forall a l x,
  In (a::x) (PowerSet l) -> In x (PowerSet l).
Proof.
  induction l.
  - intros.
    destruct H.
    * inversion H.
    * destruct H.
  - simpl.
    intros.
    apply in_app_iff in H.
    destruct H.
    * apply Add_remove in H.
      destruct H as [? [? ?]].
      injection H as ? ?.
      subst.
      apply in_app_iff.
      right. apply H0.
    * apply IHl in H.
      apply in_app_iff.
      tauto.
Qed.

Lemma inpowerset_subseq_eq:
  forall x y,
  In x (PowerSet y) <-> subseq x y.

Proof.
  intros. revert x.
  induction y; split ;intros.
  - destruct H.
    * destruct H.
      apply sub_nil.
    * inversion H.
  - inversion H; subst.
    apply empty_subset.
  - simpl in H.
    apply in_app_iff in H.
    destruct H.
    * apply Add_remove in H.
      destruct H as [? [? ?]].
      apply IHy in H0.
      rewrite H.
      apply sub_take, H0.
    * apply IHy in H.
      apply sub_skip, H.
  - simpl.
    inversion H; subst.
    * apply in_app_iff.
      right. apply empty_subset.
    * apply IHy in H2.
      apply PowerSet_half_in with (a:=a) in H2.
      apply H2.
    * apply IHy in H2.
      apply in_app_iff.
      tauto.
Qed.

Lemma In_PowerSet_trans:
  forall a b c,
  In a (PowerSet b) -> In b (PowerSet c) -> In a (PowerSet c).
Proof.
  intros.
  apply inpowerset_subseq_eq.
  apply inpowerset_subseq_eq in H.
  apply inpowerset_subseq_eq in H0.
  apply subseq_trans with b;[apply H|apply H0].
Qed.


Lemma Subset_PowerSet: forall l subl, 
  NoDup l -> NoDup subl -> In subl (PowerSet l) -> Subset _ (PowerSet subl) (PowerSet l).
Proof.
  intros.
  induction l.
  - destruct H1.
    * destruct H1.
      unfold Subset; simpl.
      intros. tauto.
    * destruct H1.
  - simpl in *.
    unfold Subset in *; intros.
    apply in_app_iff in H1.
    destruct H1.
    * apply Add_remove in H1.
      destruct H1 as [? [? ?]].
      rewrite H1 in H2; simpl in H2.
      apply in_app_iff in H2.
      destruct H2.
      + apply Add_remove in H2.
        destruct H2 as [? [? ?]].
        pose proof In_PowerSet_trans x0 x l H4 H3.
        apply in_app_iff.
        left. rewrite H2.
        apply Add_a_in, H5.
      + pose proof In_PowerSet_trans u x l H2 H3.
        apply in_app_iff. tauto.
    * apply NoDup_cons_iff in H.
      destruct H.
      apply in_app_iff.
      pose proof IHl H3 H1 u H2.
      tauto.
Qed.


Fact PowerSet_Contain_Self: forall l: list nat, In l (PowerSet l).
Proof.
  intros.
  induction l.
  - simpl. left. reflexivity.
  - simpl.
    apply in_app_iff; left.
    assert (forall (a:nat) (l: list nat) (L: list (list nat)), In l L -> In (a::l) (AddOne a L)).
    { 
      intros.
      induction L.
      - apply in_nil in H; tauto.
      - simpl.
        apply in_inv in H.
        destruct H.
        -- rewrite H; left; reflexivity.
        -- apply IHL in H; right; tauto.
    }
    apply H, IHl.
Qed.

  
Fact Constraint_in:
forall (x X: list nat) (f: list nat -> Z),
NoDup X ->
In x (PowerSet X) ->
Summ_Of_List (list nat) (Mu f (Datatypes.length x)) (PowerSet x) =
Summ_Of_List (list nat) (f_x_test_in (Mu f (Datatypes.length x)) (PowerSet x)) (PowerSet X).
Proof.
  intros.
  apply Summ_constraint_X_Y.
      - apply PowerSet_NoDup, H.
      - eapply PowerSet_NoDup, PowerSet_Element_NoDup.
        apply H.
        apply H0.
      - eapply Subset_PowerSet; [apply H | eapply PowerSet_Element_NoDup; [apply H | apply H0] | tauto].
Qed.

Fact Summ_test_eq:
forall (X: list nat) (f: list nat -> Z), NoDup X ->
  Summ_Of_List (list nat) (fun x : list nat => (Z.mul (f x) (test_list_eq_Z x X)%Z)) (PowerSet X) = f X.
Proof.
  intros.
  pose proof PowerSet_Contain_Self X.
  apply Add_inv in H0 as H1; destruct H1 as [l' ?].
  apply Permutation_Add in H1 as H2.
  erewrite Permutation_Summ; [ | apply Permutation_sym; apply H2].
  simpl.
  assert (Z.mul (f X) (test_list_eq_Z X X) = f X).
  { 
    unfold test_list_eq_Z.
    destruct (test_list_eq X X).
    - lia.
    - destruct n; reflexivity.
  }
  rewrite H3.
  rewrite Summ_f_g with (g:= fun _ => 0%Z).
  2: {
    intros.
    unfold test_list_eq_Z.
    destruct (test_list_eq x X).
    - apply NoDup_Add in H1 as H5.
      apply PowerSet_NoDup in H as H6.
      apply H5 in H6.
      rewrite e in H4.
      tauto.
    - lia.
  }
  rewrite F_zero_summ_zero.
  lia.
Qed.

Lemma subseq_in:
  forall x y (a:nat), subseq x y -> In a x -> In a y.
Proof.
  intros.
  pose proof inpowerset_subseq_eq x y.
  apply H1 in H.
  apply PowerSet_Subset in H.
  unfold Subset in H.
  apply H, H0.
Qed.

Fact Sub_Sub_eq1: forall (l1 l2: list nat), 
  NoDup l1 -> In l1 (PowerSet l2) -> In l2 (PowerSet l1) -> NoDup l2 -> l1 = l2.
Proof.
  intros.
  apply inpowerset_subseq_eq in H0.
  apply inpowerset_subseq_eq in H1.
  revert H H0.
  induction H1.
  - intros. inversion H0. tauto.
  - intros. 
    inversion H0; subst.
    * apply NoDup_cons_iff in H2.
      destruct H2.
      apply NoDup_cons_iff in H.
      destruct H.
      pose proof IHsubseq H3 H5 H4.
      rewrite H6. tauto.
    * assert (In x (x::l2)). {apply in_eq. }
      pose proof subseq_in (x::l2) l1 x H5 H3.
      apply NoDup_cons_iff in H2.
      tauto.
  - intros.
    assert (In x (x::l2)). { apply in_eq. }
    pose proof subseq_in (x::l2) l1 x H0 H3.
    pose proof subseq_in l1 l2 x H1 H4.
    apply NoDup_cons_iff in H. tauto.
Qed.

Lemma Sub_Sub_eq: forall (l1 l2: list nat), 
  NoDup l1 -> In l1 (PowerSet l2) -> In l2 (PowerSet l1) -> l1 = l2.
Proof.
  intros.
  pose proof PowerSet_Element_NoDup l1 l2 H H1.
  apply Sub_Sub_eq1;[apply H|apply H0|apply H1| apply H2].
Qed.

Fact Binomial_inner_constraint_pre:
forall (a:nat) (x: list nat) (l: list (list nat)),
  ~ In a x ->
  NoDup x ->
  (forall l': list nat, In l' l -> ~ In a l') ->
  Z.add (Summ_Of_List (list nat) (fun x0:list nat => Z.mul (MinusOnePower (Datatypes.length x0)) 
        (test_in_list_Z x (PowerSet x0))) (AddOne a l)) 
        (Summ_Of_List (list nat) (fun x0:list nat => Z.mul (MinusOnePower (Datatypes.length x0)) 
        (test_in_list_Z x (PowerSet x0))) l) = 0%Z.
Proof.
  intros.
  induction l.
  - simpl; tauto.
  - simpl.
    assert (forall (a b c d: Z), Z.add (Z.add a b) (Z.add c d) = Z.add (Z.add (Z.add b d) a) c). { lia. }
    rewrite H2.
    assert (forall l': list nat, In l' l -> ~ In a l').
    { 
      intros. 
      apply in_cons with (a:=a0) in H3.
      apply H1 in H3; tauto. 
    }
    pose proof IHl H3.
    rewrite H4.
     unfold test_in_list_Z.
     destruct (test_in_list x (PowerSet a0)).
     * destruct (test_in_list x (AddOne a (PowerSet a0) ++ PowerSet a0)); [lia | ].
       assert (In x (AddOne a (PowerSet a0) ++ PowerSet a0)). { apply in_app_iff. right. tauto. }
       tauto.
     * destruct (test_in_list x (AddOne a (PowerSet a0) ++ PowerSet a0)); [ | lia].
       apply in_app_or in i.
       destruct i; [ | tauto].
       apply Add_remove in H5.
       destruct H5 as [y [? ?]].
       assert (In a x). { rewrite H5. apply in_eq. }
       tauto.
Qed.

Lemma Bi_constraint_in_out: forall (x X: list nat),
NoDup X -> In x (PowerSet X) ->
Summ_Of_List (list nat)
   (fun x0 : list nat => Z.mul (MinusOnePower (Datatypes.length x0)) (test_in_list_Z x (PowerSet x0))) (PowerSet X) =
Summ_Of_List (list nat)
   (fun x0 : list nat => MinusOnePower (Datatypes.length x0)) (filter (fun l => test_in_list_b x (PowerSet l)) (PowerSet X)).
Proof.
  intros.
  remember (fun l => test_in_list_b x (PowerSet l)) as G.
  remember (fun l => In x (PowerSet l)) as F.
  assert (forall l: list nat, {F l} + {~ F l}). { rewrite HeqF. intros. apply test_in_list. }
  assert (forall l: list nat, F l <-> G l = true). { intros. rewrite HeqF, HeqG. apply Test_In_List_True. }
  assert (forall l: list nat, ~ F l <-> G l = false). { intros. rewrite HeqF, HeqG. apply Test_In_List_False. }
  pose proof constrain_app _ F G (PowerSet X) H1 H2 H3.
  erewrite <- Permutation_Summ; [ | apply H4].
  rewrite <- Summ_List_App.
  assert (forall x0 : list nat, In x0 (filter (fun x1 : list nat => negb (G x1)) (PowerSet X))
  -> (fun x1 : list nat => Z.mul (MinusOnePower (Datatypes.length x1)) (test_in_list_Z x (PowerSet x1))) x0 =
     (fun _ : list nat => 0%Z) x0).
  {
    intros.
    apply filter_In in H5 as H6; destruct H6 as [H7 H8].
    rewrite Bool.negb_true_iff with (b:= G x0) in H8.
    apply H3 in H8; rewrite HeqF in H8.
    unfold test_in_list_Z.
    destruct (test_in_list x (PowerSet x0)); [tauto | lia].
  }
  pose proof Summ_f_g _ (fun x0 : list nat => Z.mul (MinusOnePower (Datatypes.length x0)) 
                        (test_in_list_Z x (PowerSet x0))) (fun x0: list nat => 0%Z) 
                        (filter (fun x0 : list nat => negb (G x0)) (PowerSet X)) H5.
  rewrite H6.
  rewrite F_zero_summ_zero.
  assert (forall a: Z, Z.add a 0%Z = a). { lia. }
  rewrite H7.
  eapply Summ_f_g.
  intros.
  apply filter_In in H8; destruct H8.
  apply H2 in H9; rewrite HeqF in H9.
  unfold test_in_list_Z.
  destruct (test_in_list x (PowerSet x0)); [lia | tauto].
Qed.

Lemma empty_Minusset_empty:
  forall x, MinusSet [] x = [].
Proof.
  intros.
  unfold MinusSet.
  simpl. reflexivity.
Qed.

Lemma MinusSet_subseq:
  forall x y,
  subseq (MinusSet y x) y.
Proof.
  intros. revert x. induction y.
  + intros.
    rewrite empty_Minusset_empty.
    apply sub_nil.
  + unfold MinusSet, Test_In.
    intros. simpl.
    destruct (test_in a x); simpl.
    - apply subseq_trans with (l2 := y); [apply IHy|apply sub_skip].
      apply subseq_refl.
    - apply sub_take, IHy.
Qed.


Lemma filter_empty:
  forall (U:Type) f (l:list U),
  filter f l = [] -> (forall x, In x l -> f x = false).
Proof.
  induction l; simpl;intros.
  - destruct H0.
  - destruct H0.
    * subst.
      destruct (f x);[inversion H| reflexivity].
    * destruct (f a);[inversion H|].
      pose proof IHl H x H0. tauto.
Qed.


Lemma Binomial_map_powerset_pre:
  forall l1 l2 x a,
  ~In a x ->
  map (Datatypes.length (A:=nat))
    (filter (fun l : list nat => if test_in_list x (PowerSet l) then true else false) l1) =
  map (Datatypes.length (A:=nat)) (map (fun l : list nat => x ++ l) l2) ->
  map (Datatypes.length (A:=nat))
    (filter (fun l : list nat => if test_in_list x (PowerSet l) then true else false) (AddOne a l1)) =
  map (Datatypes.length (A:=nat)) (map (fun l : list nat => x ++ l) (AddOne a l2)).
Proof.
  induction l1, l2; simpl ;intros.
  - reflexivity.
  - inversion H0.
  - destruct (test_in_list x (PowerSet a)).
    * inversion H0.
    * destruct (test_in_list x (AddOne a0 (PowerSet a) ++ PowerSet a)).
      + apply in_app_iff in i.
        destruct i;[simpl |tauto].
        apply Add_remove in H1.
        destruct H1 as [? [? ?]].
        assert (In a0 x). { rewrite H1. apply in_eq. }
        tauto.
      + pose proof IHl1 [] x a0 H H0.
        simpl in H1. tauto.
  - destruct (test_in_list x ((AddOne a0 (PowerSet a) ++ PowerSet a))).
    + simpl.
      apply in_app_iff in i.
      * destruct i.
        ++ apply Add_remove in H1.
           destruct H1 as [? [? ?]].
           rewrite H1 in H.
           assert (In a0 (a0 :: x0)). {apply in_eq. }
           tauto.
        ++ destruct (test_in_list x (PowerSet a));[|tauto]. 
           rewrite map_cons in H0.
           injection H0 as ? ?.
           pose proof IHl1 l2 x a0 H H2.
           rewrite H3.
           assert (Datatypes.length (x ++ a0 :: l) = Datatypes.length (a0 :: x ++ l)).
           {
              apply Permutation_length, Permutation_sym, Permutation_middle.
           }
           rewrite H4. simpl.
           rewrite H0. reflexivity.
   + destruct (test_in_list x (PowerSet a)).
     * assert (In x (AddOne a0 (PowerSet a)) \/ In x (PowerSet a)). { tauto. }
       apply in_or_app in H1. tauto. 
     * pose proof IHl1 (l :: l2) x a0 H.
       simpl in H1. apply H1, H0.
Qed.

Lemma Over_Minus:
  forall  x l (a:nat),
  ~In a x -> ~In a l -> MinusSet l x = MinusSet l (a::x).
Proof.
  intros.
  unfold MinusSet.
  apply filter_ext_in.
  intros.
  unfold Test_In.
  destruct (test_in a0 x); destruct (test_in a0 (a:: x)).
  - reflexivity.
  - destruct n.
    apply in_cons, i.
  - destruct i.
    * rewrite H2 in H0. tauto.
    * tauto.
  - tauto.
Qed.

Lemma filter_all_hit:
  forall (U:Type) l f,
  (forall x:U, In x l -> f x = true) -> filter f l = l.
Proof.
  induction l.
  - intros. reflexivity.
  - intros.
    assert ((forall x : U, In x l -> f x = true)).
    {
       intros.
       assert(In x (a::l)). { apply in_cons, H0. }
       apply H in H1. tauto.
    }
    simpl.
    pose proof IHl f H0.
    rewrite H1.
    pose proof H a.
    assert (In a (a::l)). { apply in_eq. }
    apply H2 in H3.
    rewrite H3. reflexivity.
Qed.

Lemma S_plus:
  forall (x: nat), S x = x + 1.
Proof.
  intros. lia.
Qed.

Lemma App_length_shift:
  forall a x0 l1,
  map (Datatypes.length (A:=nat)) (map (fun l : list nat => (a :: x0) ++ l) l1 )
  = map PlusOne (map (Datatypes.length (A:=nat)) (map (fun l :list nat => x0 ++ l) l1)).
Proof.
  induction l1; simpl;intros;[reflexivity|].
  unfold PlusOne.
  pose proof S_plus (Datatypes.length (x0 ++ a0)).
  simpl in IHl1.
  rewrite IHl1, H.
  unfold PlusOne.
  reflexivity.
Qed.


Lemma AddOne_length_shift:
  forall a x0 l1,
  map (Datatypes.length (A:=nat))
  (filter (fun l : list nat => if test_in_list (a :: x0) (PowerSet l) then true else false) (AddOne a l1))=
  map PlusOne ( map (Datatypes.length (A:=nat))
  (filter (fun l : list nat => if test_in_list x0 (PowerSet l) then true else false) l1)).
Proof.
  induction l1;simpl;intros;[reflexivity|].
  destruct (test_in_list x0 (PowerSet a0)).
  - destruct (test_in_list (a :: x0) (AddOne a (PowerSet a0) ++ PowerSet a0)).
    * simpl. unfold PlusOne in *.
      rewrite S_plus, IHl1. reflexivity.
    * apply PowerSet_half_in with (a:= a) in i.
      simpl in i. tauto.
  - destruct (test_in_list (a :: x0) (AddOne a (PowerSet a0) ++ PowerSet a0)).
    * apply in_app_iff in i. destruct i.
      + apply Add_remove in H.
        destruct H as [? [? ?]].
        injection H as ?.
        rewrite H in n.
        tauto.
      + apply InPs_in in H.
        tauto.
    * tauto.
Qed.

Lemma Binomial_map_powerset: forall (x X: list nat),
NoDup X -> In x (PowerSet X) ->
Summ_Of_List (list nat) (fun x0 : list nat => MinusOnePower (Datatypes.length x0)) 
      (filter (fun l : list nat => test_in_list_b x (PowerSet l)) (PowerSet X)) = 
Summ_Of_List (list nat) (fun x0 : list nat => MinusOnePower (Datatypes.length x0))
      (map (fun l: list nat => x ++ l) (PowerSet (MinusSet X x))).
Proof.
  intros.
  repeat rewrite Summ_list_listsum_eq.
  apply same_list_same_sum.
  rewrite <- map_map.
  pose proof map_map (Datatypes.length (A:=nat)) MinusOnePower
       ((map (fun l : list nat => x ++ l) (PowerSet (MinusSet X x)))).
  rewrite <-H1. clear H1.
  apply Same_list_same_map.
  revert H H0. revert x.
  induction X;unfold test_in_list_b; intros.
  - destruct H0; subst; simpl.
    * destruct (test_in_list [] [[]]);[reflexivity|].
      destruct n. apply in_eq.
    * destruct H0.
  - simpl in H0. apply in_app_iff in H0.
    destruct H0; simpl; unfold Test_In.
    + apply Add_remove in H0.
      destruct H0 as [? [? ?]].
      rewrite filter_app.
      apply NoDup_cons_iff in H.
      destruct H.
      assert (filter (fun l : list nat => if test_in_list x (PowerSet l) then true else false) (PowerSet X) = []).
      {
        apply Nothingfit_nil.
        intros.
        destruct (test_in_list x (PowerSet x1));[|tauto].
        pose proof In_PowerSet_trans x x1 X i H3.
        pose proof not_int_Ps X a H x H4.
        assert( In a x). { rewrite H0. apply in_eq. }
        tauto.
      }
      rewrite H3.
      destruct (test_in a x).
      * simpl. rewrite app_nil_r.
        pose proof IHX x0 H2 H1. 
        unfold test_in_list_b in H4.
        pose proof not_int_Ps X a H x0 H1.
        pose proof Over_Minus x0 X a H5 H.
        pose proof App_length_shift a x0 (PowerSet (MinusSet X x0)).
        pose proof AddOne_length_shift a x0 (PowerSet X).
        rewrite H0, <- H6, H7, H8, H4. reflexivity.
      * assert(In a x). { rewrite H0. apply in_eq. }
        tauto.
    + apply NoDup_cons_iff in H.
      destruct H.
      pose proof not_int_Ps X a H x H0.
      destruct (test_in a x);[tauto|].
      simpl. rewrite filter_app.
      rewrite !map_app.
      pose proof IHX x H1 H0.
      unfold test_in_list_b in H3.
      rewrite H3. apply App_eq.
      apply Binomial_map_powerset_pre with (a:= a) in H3.
      rewrite H3. tauto. tauto.
Qed.

Lemma Binomial_map_remove: forall (x : list nat) (L : list (list nat)),
Summ_Of_List (list nat) (fun x0 : list nat => MinusOnePower (Datatypes.length x0))
(map (fun l: list nat => x ++ l) L) =
Summ_Of_List (list nat) (fun x0 : list nat => Z.mul (MinusOnePower (Datatypes.length x)) (MinusOnePower (Datatypes.length x0))) L.
Proof.
  intros.
  induction L.
  - simpl; reflexivity.
  - simpl.
    assert (forall a b c d: Z, a = b -> c = d -> Z.add a c = Z.add b d). { intros. lia. }
    apply H; [ | tauto].
    rewrite app_length.
    rewrite <- MinusOnePower_Add; lia.
Qed.

Lemma Out_coef: forall (U:Type) (L: list U) (f: U -> Z) (c: Z),
Summ_Of_List _ (fun x:U => Z.mul c (f x)) L = Z.mul c (Summ_Of_List _ f L).
Proof.
  intros.
  induction L.
  - simpl; lia.
  - simpl.
    rewrite IHL.
    lia.
Qed.
  
Lemma Binomial_inner_constraint_new: forall (x X: list nat), 
NoDup X -> 
In x (PowerSet X) ->
Summ_Of_List (list nat)
   (fun x0 : list nat => Z.mul (MinusOnePower (Datatypes.length x0)) (test_in_list_Z x (PowerSet x0))) (PowerSet X) =
Z.mul (MinusOnePower (Datatypes.length x)) (Summ_Of_List (list nat)
   (fun x0 : list nat => MinusOnePower (Datatypes.length x0)) (PowerSet (MinusSet X x))).
Proof.
  intros.
  rewrite Bi_constraint_in_out; [ | tauto | tauto ].
  rewrite Binomial_map_powerset; [ | tauto | tauto].
  rewrite Binomial_map_remove.
  rewrite Out_coef; lia.
Qed.

Lemma Empty_filter: forall (U: Type) (l: list U) (f: U -> bool),
(forall x:U, In x l -> f x = false) -> filter f l = nil.
Proof.
  intros.
  induction l.
  - simpl; reflexivity.
  - simpl.
    pose proof H a.
    assert (In a (a::l)). { apply in_eq. }
    apply H0 in H1.
    rewrite H1.
    assert (forall x: U, In x l -> f x = false).
    { 
      intros.
      apply in_cons with (a:= a) in H2.
      apply H; tauto. 
    }
    pose proof IHl H2; tauto.
Qed.

Lemma Eq_Subset_Empty: forall (x X: list nat), x = X -> MinusSet X x = nil.
Proof.
  intros.
  unfold MinusSet.
  rewrite H.
  apply Empty_filter.
  intros.
  unfold Test_In.
  destruct (test_in x0 X).
  - reflexivity.
  - tauto.
Qed.

Lemma Add_not_in:
  forall (a:nat) l,
  (forall x, In x l -> ~ In a x) ->(forall x, In x l -> ~In x (AddOne a l)).
Proof.
  intros.
  apply H in H0.
  unfold not; intros.
  apply In_add_a_l in H1.
  tauto.
Qed.

Lemma not_in_remove:
  forall (U:Type) (a:U) b l,
  ~In a (b::l) -> ~In a l /\ a <> b.
Proof.
  intros.
  pose proof  classic (In a l).
  destruct H0.
  - pose proof in_cons b a l H0.
    tauto.
  - assert (~ In a l /\ a <> b <-> ~ ( a = b \/ In a l )). { split;tauto. }
    apply H1. unfold not. intros.
    assert (In a (b::l)).
    {
      destruct H2.
      rewrite H2. apply in_eq.
      apply in_cons, H2.
    }
    tauto.
Qed.
    
Lemma Notin_neq:
  forall (a: list nat) l,
  ~In a l <-> (forall x, In x l -> x <> a).
Proof.
  intros.
  induction l; split; intros.
  - destruct H0.
  - unfold not; intros.
    destruct H0.
  - apply not_in_remove in H.
    destruct IHl, H.
    pose proof H1 H x.
    apply in_inv in H0.
    destruct H0.
    * rewrite <- H0.
      apply list_neq_sym, H3.
    * apply H4, H0.
  - destruct IHl.
    unfold not; intros.
    apply in_inv in H2.
    destruct H2.
    * pose proof H a0.
      assert(In a0 (a0 :: l)). { apply in_eq. }
      apply H3 in H4.
      rewrite H2 in H4.
      destruct H4. reflexivity.
    * assert (forall x: list nat, In x l -> x <> a).
      {
        intros. apply H.
        apply in_cons, H3.
      }
      pose proof H1 H3.
      tauto.
Qed.

Lemma Add_not_per:
  forall (U:Type) a b (c:U),
  ~ In c a -> ~In c b -> ~Permutation a b -> ~Permutation (c::a) (c::b).
Proof.
  intros. unfold not. intros.
  apply Permutation_cons_inv in H2.
  tauto.
Qed.
Lemma NoDup_NoPer:
  forall l, NoDup l ->
  (forall x y, In x (PowerSet l) -> In y (PowerSet l) -> (x = y \/ ~Permutation x y)).
Proof.
  induction l.
  - intros.
    destruct H0, H1.
    * subst. tauto.
    * inversion H1.
    * inversion H0.
    * inversion H0.
  - intros.
    apply NoDup_cons_iff in H.
    destruct H.
    pose proof IHl H2.
    simpl in H0, H1.
    apply in_app_iff in H0.
    apply in_app_iff in H1.
    destruct H0,H1.
    * apply Add_remove in H0.
      apply Add_remove in H1.
      destruct H0 as [? [? ?]].
      destruct H1 as [? [? ?]].
      subst.
      pose proof H3 x1 x0 H5 H4.
      destruct H0.
      + left. rewrite H0. tauto.
      + pose proof not_int_Ps l a H.
        pose proof H1 x0 H4.
        pose proof H1 x1 H5.
        pose proof Add_not_per (nat) x1 x0 a H7 H6 H0.
        right. unfold not. intros.
        apply Permutation_sym in H9.
        tauto. 
    * apply not_int_Ps with (a:=a) in H1;[|apply H].
      apply Add_remove in H0.
      destruct H0 as [? [? ?]].
      right. unfold not. intros.
      apply Permutation_in with (x:=a) in H5;[tauto|].
      rewrite H0. apply in_eq.
    * apply not_int_Ps with (a:=a) in H0;[|apply H].
      apply Add_remove in H1.
      destruct H1 as [? [? ?]].
      right. unfold not. intros.
      apply Permutation_sym in H5.
      apply Permutation_in with (x:=a) in H5;[tauto|].
      rewrite H1. apply in_eq.
    * pose proof H3 x y H0 H1.
      tauto.
Qed.

Lemma subnot:
  forall x y (a:nat), subseq x y -> ~In a y -> ~In a x.
Proof.
  intros.
  pose proof inpowerset_subseq_eq x y.
  apply H1 in H.
  apply PowerSet_Subset in H.
  unfold Subset in H.
  unfold not. intros.
  pose proof H a H2.
  tauto.
Qed.

Lemma Not_Eq_Subseq: forall (x X: list nat),
NoDup X -> NoDup x ->
  subseq x X -> x <> X -> exists u:nat, In u X /\ ~ In u x.
Proof.
  intros.
  revert H H0 H1 H2.
  revert x.
  induction X; intros.
  - inversion H1; subst.
    destruct H2. tauto.
  - inversion H1; subst.
    -- exists a; split; [apply in_eq | apply in_nil].
    -- destruct (classic (l1 = X)).
       * subst. destruct H2; tauto.
       * apply NoDup_cons_iff in H as H6; destruct H6.
       apply NoDup_cons_iff in H0 as H7; destruct H7.
         pose proof IHX l1 H6 H8 H5 H3.
         destruct H9 as [u [? ?]].
         exists u.
         split. 
         ** apply in_cons, H9.
         ** unfold not; intros.
            apply in_inv in H11.
            destruct H11; [subst; tauto | tauto].
    -- exists a.
       split; [apply in_eq | ].
       apply NoDup_cons_iff in H; destruct H.
       pose proof subnot _ _ _ H5 H; tauto.
Qed.


End Lemmas.
