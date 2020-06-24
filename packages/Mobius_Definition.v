Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.micromega.Psatz.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.
Require Import Permutation.
Require Import ListDec.

Module Def.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(* 向一个S: list (list nat) 中的每一项 (list nat) 的头部添加一个x: nat *)
Fixpoint AddOne (x: nat) (S: list (list nat)): list (list nat) :=
  match S with
  | nil => nil
  | cons l S' => cons (cons x l) (AddOne x S')
  end
.
(* Compute AddOne 1%nat [[2;3;4];[2;5]]. *)

(*对 l: list nat, 生成它的幂集*)
Fixpoint PowerSet (l: list nat): list (list nat) :=
  match l with
  | nil => cons nil nil
  | cons x l' => app (AddOne x (PowerSet l')) (PowerSet l')
  end
.
(* Compute PowerSet [1;2;3;4]. *)

(*定义 -1 的 n 次方*)
Fixpoint MinusOnePower (n: nat): Z :=
  match n with
  | O => 1
  | S n' => - MinusOnePower n'
  end
.

(*对一个给定的列表进行求和: 对列表中的元素应用函数 f 后求和*)
Fixpoint Summ_Of_List (U: Type) (f: U -> Z) (L: list U) : Z := 
  match L with
  | nil => 0
  | cons x L' => (f x) + (Summ_Of_List _ f L')
  end.

(*Zeta 变换: 对X的所有子集构成的列表求和*)
Definition Zeta (f: (list nat) -> Z) (X: list nat): Z :=
  Summ_Of_List _ f (PowerSet X).

(*Mobius 变换的辅助定义*)
Definition Mu (f: (list nat) -> Z) (n: nat) (X: list nat): Z :=
  (MinusOnePower (n - (Datatypes.length X))) * (f X) .

(*Mobius 变换*)  
Definition Mobius (f: (list nat) -> Z) (X: list nat): Z :=
  Summ_Of_List _ (Mu f (Datatypes.length X)) (PowerSet X).


(* 对自然数i, 从n到0遍历求和*)
Fixpoint Summ_From_n_to_0 (i: nat) (f: nat -> Z): Z :=
  match i with 
  | O => f O
  | S i' => (f i) + Summ_From_n_to_0 i' f
  end
.

(* nat 是否在 list nat 中 可判定 *)
Lemma test_in (a: nat) (l: list nat): {In a l} + {~ In a l}.
Proof.
  apply In_dec.
  intros.
  apply Nat.eq_dec.
Qed.

Definition Test_In (a: nat) (l: list nat): bool := 
  if test_in a l then true else false.

Lemma In_and_test_in (a: nat) (l: list nat): In a l <-> Test_In a l = true.
Proof.
  split; unfold Test_In; intros.
  + destruct (test_in a l).
    - tauto.
    - tauto.
  + destruct (test_in a l).
    - tauto.
    - inversion H.
Qed.

Lemma NotIn_and_test_notin (a:nat) (l: list nat): ~ In a l <-> Test_In a l = false.
Proof.
  split; unfold Test_In; intros.
  + destruct (test_in a l);tauto.
  + destruct (test_in a l);[inversion H| tauto].
Qed.


(* 将 In a l 转化为 Z 类型: 1%Z or 0%Z *)
Definition Test_In_Z (n: nat) (l: list nat): Z :=
  if test_in n l then 1 else 0.

(* 子集的定义， 不要求顺序 *)
Definition Subset (U: Type) (Y X: list U): Prop :=
  forall u: U, In u Y -> In u X.
  
  
Definition always_zero (x: list nat): Z := 0%Z.

(* In (list nat) (list (list nat)) 可判定 *) 
Lemma test_in_list (x: list nat) (X: list (list nat)): {In x X} + {~ In x X}.
Proof.
  apply In_dec.
  intros.
  apply list_eq_dec.
  apply Nat.eq_dec.
Qed.

Definition test_in_list_Z (x: list nat) (X: list (list nat)): Z :=
  if (test_in_list x X) then 1%Z else 0%Z.
  
Definition test_in_list_b (x: list nat) (X: list (list nat)): bool :=
  if (test_in_list x X) then true else false.
  
Lemma In_and_test_in_list: forall (x: list nat) (X: list (list nat)),
  In x X <-> test_in_list_b x X = true.
Proof.
  split; intros.
  unfold test_in_list_b in *.
  - destruct (test_in_list x X); [reflexivity | tauto].
  - unfold test_in_list_b in H.
    destruct (test_in_list x X); [tauto | inversion H].
Qed.

Lemma NotIn_and_test_not_in_list:
  forall (x: list nat) l,
  ~In x l <-> test_in_list_b x l = false.
Proof.
  split;unfold test_in_list_b; intros.
  - destruct (test_in_list x l);tauto. 
  - destruct (test_in_list x l);[inversion H| tauto].
Qed.

(* f(x) * [x \subset X] *)
Definition f_x_test_in (f: list nat -> Z) (X:list (list nat)) (x: list nat): Z :=  
  Z.mul (f x) (test_in_list_Z x X).
  
Lemma f_x_test_in_val_1: forall (f: list nat -> Z) (X: list (list nat)) (x: list nat),
  In x X -> f_x_test_in f X x = f x.
Proof.
  intros.
  unfold f_x_test_in, test_in_list_Z.
  destruct (test_in_list x X).
  - lia.
  - tauto.
Qed.

Lemma f_x_test_in_val_0: forall (f: list nat -> Z) (X: list (list nat)) (x: list nat),
  ~ In x X -> f_x_test_in f X x = 0%Z.
Proof.
  intros.
  unfold f_x_test_in, test_in_list_Z.
  destruct (test_in_list x X).
  - tauto.
  - lia.
Qed.

Definition MinusOnetoLen (x: list nat): Z :=
  MinusOnePower (Datatypes.length x).

(* 子序列的定义 *)
Inductive subseq {A: Type} : list A -> list A -> Prop :=
  | sub_nil  l : subseq [] l
  | sub_take x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | sub_skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2).

(* 传递性 *)
Theorem subseq_trans : forall (A: Type) (l1 l2 l3 : list A),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros A l1 l2 l3 S12 S23. revert l1 S12.
  (** Here, we need a stronger induction hypotheses. *)
  induction S23 as [|x l2 l3 |x l2 l3]; intros.
  inversion S12.
  - apply sub_nil.
  - inversion S12; subst.
    * apply sub_nil.
    * apply sub_take.
      apply IHS23, H1.
    * apply sub_skip.
      apply IHS23, H1.
  - apply sub_skip.
    apply IHS23, S12.
Qed.

Theorem subseq_app : forall (A: Type) (l1 l2 l3 : list A),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H; simpl.
  - apply sub_nil.
  - apply sub_take, IHsubseq.
  - apply sub_skip, IHsubseq.
Qed.
    

Theorem subseq_map : forall (A B: Type) (f: A -> B) (l1 l2: list A),
  subseq l1 l2 ->
  subseq (map f l1) (map f l2).
Proof.
  intros.
  induction H; simpl.
  - apply sub_nil.
  - apply sub_take.
    tauto.
  - apply sub_skip.
    tauto.
Qed.

Theorem subseq_refl : forall (A: Type) (l : list A), subseq l l.
Proof.
  intros.
  induction l.
  - apply sub_nil.
  - apply sub_take.
    exact IHl.
Qed.

(* list nat 可判定 *)
Lemma test_list_eq: forall (l1 l2: list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  intros.
  apply list_eq_dec.
  intros.
  apply Nat.eq_dec.
Qed.

Definition test_list_eq_Z (l1 l2:list nat): Z :=
  if test_list_eq l1 l2 then 1 else 0.

Fact Test_List_Eq_Z: forall (x X: list nat), 
  (x = X -> test_list_eq_Z x X = 1%Z) /\ (x <> X -> test_list_eq_Z x X = 0%Z).
Proof.
  split; intros; unfold test_list_eq_Z in *.
  - destruct (test_list_eq x X); [lia | ].
    rewrite H in n.
    destruct n; tauto.
  - destruct (test_list_eq x X); [ | lia ].
    rewrite e in H.
    destruct H; tauto.
Qed.

Fact Test_In_List_Z: forall (x: list nat) (X: list (list nat)), 
(In x X -> test_in_list_Z x X = 1%Z) 
/\ 
(~ In x X -> test_in_list_Z x X = 0%Z).
Proof.
  split; intros; unfold test_in_list_Z in *.
  - destruct (test_in_list x X); [lia | tauto].
  - destruct (test_in_list x X); [tauto | lia].
Qed.

Fact Test_In_List_True: forall (x: list nat) (X: list (list nat)),
  In x X <-> test_in_list_b x X = true.
Proof.
  split; intros; unfold test_in_list_b in *.
  destruct (test_in_list x X); [reflexivity | tauto].
  destruct (test_in_list x X); [tauto | inversion H].
Qed.

Fact Test_In_List_False: forall (x: list nat) (X: list (list nat)),
  ~ In x X <-> test_in_list_b x X = false.
Proof.
  split; intros; unfold test_in_list_b in *.
  destruct (test_in_list x X); [tauto | reflexivity].
  destruct (test_in_list x X); [inversion H | tauto ].
Qed.

(* 集合作差, 保持原顺序 *)
Definition MinusSet (S s: list nat) : list nat := filter (fun x => negb (Test_In x s)) S.

Lemma test_eq_nat (a b: nat): {a = b} + {a <> b}.
Proof.
  apply Nat.eq_dec.
Qed.


Definition Nat_eq_Z (a b:nat): Z :=
  if test_eq_nat a b then 1%Z else 0%Z.

Lemma Eq_and_test_eq (a b: nat): Nat.eq a b <-> Nat_eq_Z a b = 1%Z.
Proof.
  split; unfold Nat_eq_Z ;intros; destruct (test_eq_nat a b).
  - reflexivity.
  - inversion H.
    lia.
  - unfold Nat.eq. tauto.
  - inversion H.
Qed.

Lemma neq_and_testeq_false (a b:nat):
  ~ (Nat.eq a b) <-> Nat_eq_Z a b = 0%Z.
Proof.
  split; unfold Nat_eq_Z; intros.
  - destruct (test_eq_nat a b).
    * unfold Nat.eq in H. lia.
    * reflexivity.
  - destruct (test_eq_nat a b).
    * inversion H.
    * unfold Nat.eq. lia.
Qed.

(* 生成列表 [n;(n-1);...;2;1;0] *)
Fixpoint nat_list (x:nat): list nat :=
  match x with
   | O => O :: nil
   | S n => (S n) :: nat_list n
  end.

Fixpoint list_Z_sum (x:list Z): Z :=
  match x with 
   | nil => 0%Z
   | a :: l => (a + list_Z_sum l)%Z
  end.

Definition list_nat_length (a: list nat) := Datatypes.length a.

(* "x 是否属于 A cup B" 可判定 *)
Lemma test_in_union (A B: list nat) (x:nat): {In x A \/ In x B} + {~ In x A /\ ~ In x B}.
Proof.
  apply Sumbool.sumbool_or.
  - apply test_in.
  - apply test_in.
Qed.

Definition test_in_union_b (A B: list nat) (x:nat) : bool := 
  if test_in_union A B x then true else false.

(* A cup B = Y 的定义 (顺序不敏感) *)
Definition Eq_Union (A B Y: list nat) : Prop :=
  forall n:nat , In n A \/ In n B <-> In n Y.

Lemma In_A_app_B: forall (n: nat) (A B: list nat), In n A \/ In n B <-> In n (A++B).
Proof.
  intros; split; [apply in_or_app | apply in_app_or ].
Qed.

Lemma In_Equiv_split: forall (l1 l2: list nat),
  (forall n: nat, In n l1 <-> In n l2) <-> (forall n:nat, In n l1 -> In n l2) /\ (forall n: nat, In n l2 -> In n l1).
Proof.
  intros; split; intros.
  - split; intros; apply H in H0; tauto.
  - split; intros; destruct H as [H1 H2]; [apply H1 in H0; tauto | apply H2 in H0; tauto].
Qed.

(* "A subset B" 可判定 *)
Lemma test_subset (A B: list nat): {forall n:nat, In n A -> In n B} + {~ (forall n:nat, In n A -> In n B)}.
Proof.
  induction A.
  - apply left; intros.
    apply in_nil in H; tauto.
  - destruct IHA.
    -- pose proof test_in a B.
       destruct H.
       --- left; intros.
           apply in_inv in H.
           destruct H; [subst; tauto | apply i in H; tauto].
       --- right.
           destruct (classic (forall n0 : nat, In n0 (a :: A) -> In n0 B)).
           * assert (In a (a::A)). { apply in_eq. }
             apply H in H0; tauto.
           * tauto.
    -- right.
       destruct (classic (forall n0 : nat, In n0 (a :: A) -> In n0 B)).
       * assert (forall n0: nat, In n0 A -> In n0 B).
         {
           intros.
           apply in_cons with (a:=a) in H0.
           apply H in H0; tauto.
         }
         tauto.
       * tauto.
Qed.

Lemma sumbool_equiv: forall (A B C D E F: Prop),
{A} + {C} -> {B} + {D} -> (E <-> A /\ B) -> (F <-> C \/ D) -> {E} + {F}.
Proof.
  intros.
  pose proof Sumbool.sumbool_and _ _ _ _ H H0.
  destruct H3.
  - left.
    tauto.
  - right.
    tauto.
Qed.

(* "A cup B = Y" 可判定 *)
Lemma test_eq_union (A B Y: list nat): {Eq_Union A B Y} + {~ Eq_Union A B Y}.
Proof.
  unfold Eq_Union.
  assert (forall a b c: Prop, a <-> b -> b <-> c -> a <-> c). { intros. tauto. }
  assert ((forall n: nat, In n A \/ In n B <-> In n Y) <-> (forall n: nat, In n (A++B) -> In n Y) /\ (forall n:nat, In n Y -> In n (A++B))).
  { 
    eapply H; [ | apply In_Equiv_split].
    split; intros.
    - eapply H; [pose proof In_A_app_B n A B | apply H0].
      split; tauto.
    - eapply H; [apply In_A_app_B | split].
      apply H0.
      apply H0.
  }
  assert (~ (forall n: nat, In n A \/ In n B <-> In n Y) <-> ~(forall n: nat, In n (A++B) -> In n Y) \/ ~(forall n: nat, In n Y -> In n (A++B))).
  {
    assert (forall P Q R: Prop, P <-> Q /\ R -> ~ P <-> ~ Q \/ ~ R). { intros. tauto. }
    apply H1; tauto.
  }
  pose proof test_subset.
  pose proof H2 (A++B) Y as H3.
  pose proof H2 Y (A++B) as H4.
  pose proof sumbool_equiv _ _ _ _ _ _ H3 H4 H0 H1.
  tauto.
Qed.

Definition test_eq_union_Z (A B Y: list nat): Z := 
  if test_eq_union A B Y then 1%Z else 0%Z.

(* 交集为空的定义 *)
Definition Empty_Intersect (A B: list nat):Prop :=
  forall n: nat, In n A -> ~ In n B.

(* "交集为空" 可判定 *)
Lemma test_empty_intersect (A B: list nat): {Empty_Intersect A B} + {~ Empty_Intersect A B}.
Proof.
  unfold Empty_Intersect.
  induction A.
  - left; intros.
    apply in_nil in H; tauto.
  - destruct IHA.
    -- pose proof test_in a B.
       destruct H.
       * right.
         destruct (classic (forall n0 : nat, In n0 (a :: A) -> ~ In n0 B)); [ | tauto].
         assert (In a (a::A)). { apply in_eq. }
         apply H in H0; tauto.
       * left.
         intros.
         apply in_inv in H.
         destruct H; [rewrite H in n0; tauto |apply n in H; tauto].
    -- right.
       destruct (classic (forall n0 : nat, In n0 (a :: A) -> ~ In n0 B)); [ | tauto].
       assert (forall n: nat, In n A -> ~ In n B).
       { 
         intros.
         apply in_cons with (a:=a) in H0.
         apply H in H0.
         tauto.
       }
       tauto.
Qed.

Definition test_empty_intersect_Z (A B: list nat): Z :=
  if test_empty_intersect A B then 1%Z else 0%Z. 


(* 关键定义: 卷积的定义 *)
(* 第一个参数 U 是求和变量的枚举范围(全集) *)
(* 第四个参数, 是求和条件 "A cup B = X" 中的 X *)
(* A B 不交, 由 test_empty_intersect_Z A B 限制 *)
Definition Convolution_new (U: list (list nat)) (f g: list nat -> Z) (X: list nat): Z := 
  Summ_Of_List _ (fun A: list nat => Summ_Of_List _ (fun B: list nat => Z.mul (Z.mul (Z.mul (f A) (g B)) (test_eq_union_Z A B X)) (test_empty_intersect_Z A B)) U) U.


(* 关键定义: cover product 的定义 *)
(* 参数含义同卷积的定义 *)
Definition Cover_Product_new (U: list (list nat)) (f g: list nat -> Z) (X: list nat): Z :=
  Summ_Of_List _ (fun A: list nat => Summ_Of_List _ (fun B: list nat => Z.mul (Z.mul (f A) (g B)) (test_eq_union_Z A B X)) U) U. 


(* filter 的结果是原列表的子序列 *)
Lemma filter_subseq: forall (U: Type) (l: list U) (f: U -> bool),
  subseq (filter f l) l.
Proof.
  intros.
  induction l.
  - simpl.
    apply sub_nil.
  - simpl.
    destruct (f a).
    * apply sub_take; tauto.
    * apply sub_skip; tauto.
Qed.

Lemma Test_In_Union_b: forall (n: nat) (l1 l2: list nat), 
In n l1 \/ In n l2 <-> test_in_union_b l1 l2 n = true.
Proof.
  split; intros.
  - unfold test_in_union_b.
    destruct (test_in_union l1 l2 n). 
    -- tauto.
    -- tauto.
  - unfold test_in_union_b in *.
    destruct (test_in_union l1 l2 n) in *.
    -- tauto.
    --inversion H. 
Qed.

Lemma Test_Eq_Union_Z: forall (A B Y: list nat), 
  (Eq_Union A B Y <-> test_eq_union_Z A B Y = 1%Z) /\
  (~ Eq_Union A B Y <-> test_eq_union_Z A B Y = 0%Z).
Proof.
  split; split; intros; unfold test_eq_union_Z in *; destruct (test_eq_union A B Y) in *; unfold Eq_Union in *.
  - lia.
  - tauto.
  - tauto.
  - inversion H.
  - tauto.
  - lia.
  - inversion H.
  - tauto.
Qed.

Definition Minus (a : Z):Z := - a.
Definition PlusOne (a : nat): nat := a + 1.

(* 对应 f_i(X) := f(X) * [|X| = i] *)
Definition Check_i (i: nat) (f: list nat -> Z) (x: list nat) : Z := 
  Z.mul (f x) (Nat_eq_Z (Datatypes.length x) (i)).
  
End Def.
