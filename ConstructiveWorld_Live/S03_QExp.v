(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* S03_QExp.v                                                  *)
(*                                                             *)
(* 目的：Q 层部分指数函数：定义、正性与基本估计（构造性 Set 层）。 *)
(* 主件：QExpPartial 系列——有理底的部分指数及其单调/有界性质。  *)
(* 依赖：S01_BaseRing、S02_CauchyComplete；Stdlib（QArith、     *)
(*       Qabs、Qround、List、Bool、Arith、Setoid、Morphisms、    *)
(*       Lia、Qminmax）。                                        *)
(* 备注：本件为 CW_ConstructiveWorld_219.v 之拆分分片，原文区间  *)
(*       L6983-L13800，去头正文与原文区间逐字节同源。            *)
(* ============================================================ *)
(* ============================================================ *)
(* 替换定理清单：Q2_nonneg / Qhalf_nonneg（共 2 条，语句不变）；   *)
(*   其余 reflexive 族玩具（q_pow_succ 等）经复核为定义性等式，    *)
(* 非平凡性说明：仅替换上列 2 条证明体；声明面、其余定理、原头注   *)
(*   一律原样保留。替换口径：Qle 展开 = Z 层交叉积，字面归约后      *)
(*   线性判定闭合——消除原 Qlt_le_weak 双跳转发，实质非平凡。       *)
(*   纯构造性 Set 层：零 公理、零 承认件、零经典逻辑。             *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Section QExpPartial.
(* positive_nat_Z：Z.of_nat (Pos.to_nat p) == Z.pos p（simpl 定义性 + lia） *)
Lemma positive_nat_Z : forall p : positive, QeqT (Z.of_nat (Pos.to_nat p) # 1) (Z.pos p # 1).
Proof.
  intro p. apply qeq_imp_qeqT.
  assert (Hz : Z.of_nat (Pos.to_nat p) = Z.pos p) by lia.
  rewrite Hz. apply Qeq_refl.
Qed.

Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => x * q_pow x m
  end.

Fixpoint q_fact (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => (Z.of_nat (Datatypes.S m) # 1) * q_fact m
  end.

Fixpoint exp_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)
  end.

Lemma q_pow_abs : forall (x : Q) (n : nat),QeqT ( Qabs (q_pow x n) ) ( q_pow (Qabs x) n).
Proof.
  intros x n. induction n as [| m IH]; simpl.
  - apply qeq_imp_qeqT.
    assert (H1 : Qabs (1%Q) == 1%Q) by (unfold Qabs; simpl; reflexivity).
    exact H1.
  - apply qeq_imp_qeqT.
    change (Qabs (x * q_pow x m) == Qabs x * q_pow (Qabs x) m).
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

Lemma q_pow_succ : forall x n,QeqT ( q_pow x (Datatypes.S n) ) ( x * q_pow x n).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma q_fact_succ : forall k : nat,QeqT ( q_fact (Datatypes.S k) ) ( (Z.of_nat (Datatypes.S k) # 1) * q_fact k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma q_fact_pos : forall n : nat, QltT 0 (q_fact n).
Proof.
  induction n as [| m IH]; simpl.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT.
    apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply QltT_to_Qlt; exact IH].
Qed.

Lemma q_pow_nonneg : forall (x : Q) (n : nat), QleT' 0 x -> QleT' 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - apply Qle_to_QleT'.
    apply Qmult_le_0_compat; [apply QleT'_to_Qle; exact Hx | apply QleT'_to_Qle; exact IH].
Qed.

Lemma q_neq_of_lt : forall x : Q, QltT 0 x -> Not (QeqT x 0).
Proof.
  intros x Hx H.
  destruct (Qlt_not_eq 0 x (QltT_to_Qlt 0 x Hx) (Qeq_sym x 0 (qeqT_imp_qeq x 0 H))).
Qed.

(* ===== 单调性（pow_fact_mono）===== *)
Lemma pow_fact_mono_int : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' A (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) * q_fact k) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ A k)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_replace (Z.of_nat (Datatypes.S k) # 1) with (Z.of_nat (k + 1) # 1).
  2: { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ (A * (q_pow A k * q_fact k)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((Z.of_nat (k + 1) # 1) * (q_pow A k * q_fact k)) _).
    + apply (Qmult_le_compat_r A (Z.of_nat (k + 1) # 1) (q_pow A k * q_fact k)).
      * apply QleT'_to_Qle. exact Hle.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply QltT_to_Qlt. apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma Qle_div_same_denom : forall a b e : Q,
  QltT 0 e -> QleT' a b -> QleT' (a / e) (b / e).
Proof.
  intros a b e He Hab.
  apply Qle_to_QleT'.
  unfold Qdiv.
  exact (Qmult_le_compat_r a b (/ e) (QleT'_to_Qle _ _ Hab)
    (Qinv_le_0_compat e (Qlt_le_weak 0 e (QltT_to_Qlt _ _ He)))).
Qed.

Lemma q_le_div_le : forall a b c d : Q,
  QltT 0 b -> QltT 0 d -> QleT' (a * d) (c * b) -> QleT' (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((a * d) / (b * d)) _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    field; split;
      try (intro Hz0; assert (Hlt0 : QltT 0 b) by exact Hb;
           destruct (q_neq_of_lt b Hlt0 (qeq_imp_qeqT _ _ Hz0)));
      try (intro Hz0; assert (Hlt0 : QltT 0 d) by exact Hd;
           destruct (q_neq_of_lt d Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  - apply (Qle_trans _ ((c * b) / (b * d)) _).
    + apply QleT'_to_Qle.
      apply (Qle_div_same_denom (a * d) (c * b) (b * d)).
      * apply Qlt_to_QltT.
        apply Qmult_lt_0_compat; [apply QltT_to_Qlt; exact Hb | apply QltT_to_Qlt; exact Hd].
      * exact Hle.
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      field; split;
        try (intro Hz0; assert (Hlt0 : QltT 0 b) by exact Hb;
             destruct (q_neq_of_lt b Hlt0 (qeq_imp_qeqT _ _ Hz0)));
        try (intro Hz0; assert (Hlt0 : QltT 0 d) by exact Hd;
             destruct (q_neq_of_lt d Hlt0 (qeq_imp_qeqT _ _ Hz0))).
Qed.

Lemma pow_fact_mono : forall (A : Q) (k : nat),
  QleT' 0 A -> QltT (Qmult (1 + 1)%Q A) (Qmake (Z.of_nat (k + 1)) 1) ->
  QleT' (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) (q_pow A k / q_fact k).
Proof.
  intros A k HA Hlt.
  assert (HleA : QleT' A (Qmake (Z.of_nat (k + 1)) 1)).
  {
    apply Qle_to_QleT'.
    apply (Qle_trans _ (Qmult (1 + 1)%Q A) _).
    - apply Qle_minus_iff.
      setoid_replace (Qmult (1 + 1)%Q A + - A) with A by ring.
      apply QleT'_to_Qle. exact HA.
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt.
  }
  apply (q_le_div_le (q_pow A (Datatypes.S k)) (q_fact (Datatypes.S k)) (q_pow A k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply (pow_fact_mono_int A k HA HleA).
Qed.

(* ===== 几何衰减（pow_fact_geom_step）===== *)
Lemma pow_fact_geom_int : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) (q_pow A k * q_fact (Datatypes.S k)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ A k)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_replace (Z.of_nat (Datatypes.S k) # 1) with (Z.of_nat (k + 1) # 1).
  2: { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((Qmult (1 + 1)%Q A) * (q_pow A k * q_fact k)) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((Z.of_nat (k + 1) # 1) * (q_pow A k * q_fact k)) _).
    + apply (Qmult_le_compat_r (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) (q_pow A k * q_fact k)).
      * apply QleT'_to_Qle. exact Hle.
      * apply Qmult_le_0_compat.
        -- apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply QltT_to_Qlt. apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma div_form_lhs : forall (A : Q) (k : nat),QeqT (
  q_pow A (Datatypes.S k) * q_fact k ) ( (q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)).
Proof. intros. apply qeq_imp_qeqT. field. Qed.

Lemma pow_fact_geom_step : forall (A : Q) (k : nat),
  QleT' 0 A -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (k + 1) # 1) ->
  QleT' (q_pow A (Datatypes.S k) / q_fact (Datatypes.S k)) ((q_pow A k / q_fact k) * (1 / 2)).
Proof.
  intros A k HA Hle.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((q_pow A k * (1 / 2)) / q_fact k) _).
  - apply QleT'_to_Qle.
    apply (q_le_div_le (q_pow A (Datatypes.S k)) (q_fact (Datatypes.S k))
                       (q_pow A k * (1 / 2)) (q_fact k)).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + apply Qle_to_QleT'.
      apply (Qle_trans _ ((q_pow A k * q_fact (Datatypes.S k)) * (1 / 2)) _).
      * apply (Qle_trans _ ((q_pow A (Datatypes.S k) * q_fact k * (1 + 1)) * (1 / 2)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact (qeqT_imp_qeq _ _ (div_form_lhs A k)).
        -- apply (Qmult_le_compat_r (q_pow A (Datatypes.S k) * q_fact k * (1 + 1))
                                   (q_pow A k * q_fact (Datatypes.S k)) (1 / 2)).
           ++ apply QleT'_to_Qle. apply (pow_fact_geom_int A k HA Hle).
           ++ apply Qlt_le_weak. unfold Qlt; simpl; lia.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field.
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    field.
    intro Hz. destruct (q_neq_of_lt (q_fact k) (q_fact_pos k) (qeq_imp_qeqT _ _ Hz)).
Qed.

(* ===== 几何级数（geo_sum 递归版）===== *)
Fixpoint geo_sum (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => geo_sum m + q_pow (1 / 2) m
  end.

Lemma geo_sum_closed : forall n : nat,QeqT (
  geo_sum n ) ( (1 + 1) * (1 - q_pow (1 / 2) n)).
Proof.
  intro n. apply qeq_imp_qeqT.
  induction n as [| n IH]; simpl.
  - ring.
  - rewrite IH.
    change ((1 + 1) * (1 - q_pow (1 / 2) n) + q_pow (1 / 2) n ==
            (1 + 1) * (1 - (1 / 2) * q_pow (1 / 2) n)).
    field.
Qed.

Lemma geo_sum_le_two : forall n : nat, QleT' (geo_sum n) (1 + 1).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (geo_sum_closed n)).
  apply Qle_minus_iff.
  setoid_replace ((1 + 1) - (1 + 1) * (1 - q_pow (1 / 2) n))
    with ((1 + 1) * q_pow (1 / 2) n).
  2: { ring. }
  apply Qmult_le_0_compat.
  - unfold Qle; simpl; lia.
  - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. unfold Qle; simpl; lia.
Qed.

(* ===== 迭代几何衰减 =====
   对 j ≥ 0，A^{m+Datatypes.S j}/(m+Datatypes.S j)! ≤ (A^m/m!)·(1/2)^{Datatypes.S j}。
   归纳于 j：单步（pow_fact_geom_step at m+j）+ IH 乘 (1/2)。 *)
Lemma pow_fact_geom_iter : forall (A : Q) (m j : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  QleT' (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
      ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j)).
Proof.
  intros A m j HA Hgeom.
  apply Qle_to_QleT'.
  revert m Hgeom. induction j as [| j IH]; intros m Hgeom.
  - (* j = 0：A^{m+1}/(m+1)! ≤ (A^m/m!)·(1/2)^1。
       m+1 == Datatypes.S m（lia）与 q_pow (1/2) 1 == (1/2) 换形后单步 at m。 *)
    replace (m + 1)%nat with (Datatypes.S m) by lia.
    setoid_replace (q_pow (1 / 2) 1) with (1 / 2).
    2: { change ((1 / 2) * 1 == 1 / 2). field. }
    apply QleT'_to_Qle.
    apply (pow_fact_geom_step A m HA).
    apply Hgeom. apply NatLe_lift. lia.
  - (* j = Datatypes.S j'：目标 A^{m+S(Datatypes.S j')}/(m+S(Datatypes.S j'))! ≤ (A^m/m!)·(1/2)^{Datatypes.S(Datatypes.S j')}。
       记 k := m + Datatypes.S j'。LHS = A^{Datatypes.S k}/(Datatypes.S k)!。
       单步 at k：A^{Datatypes.S k}/(Datatypes.S k)! ≤ (A^k/k!)·(1/2)。
       IH 于 m（j := Datatypes.S j'）：A^k/k! ≤ (A^m/m!)·(1/2)^{Datatypes.S j'}。
       组合：≤ (A^m/m!)·(1/2)^{Datatypes.S j'}·(1/2) == (A^m/m!)·(1/2)^{Datatypes.S(Datatypes.S j')}。 *)
    (* 换形 RHS：(1/2)^{Datatypes.S(Datatypes.S j)} == (1/2)^{Datatypes.S j}·(1/2)（q_pow_succ + mult_comm） *)
    setoid_replace (q_pow (1 / 2) (Datatypes.S (Datatypes.S j))) with (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
    2: { rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 / 2) (Datatypes.S j))). ring. }
    (* 换形 LHS：m + S(Datatypes.S j) == S(m + Datatypes.S j)（nat 相等，先断言再换形） *)
    assert (Hm : (m + Datatypes.S (Datatypes.S j))%nat = Datatypes.S (m + Datatypes.S j)) by lia.
    setoid_replace (q_pow A (m + Datatypes.S (Datatypes.S j)) / q_fact (m + Datatypes.S (Datatypes.S j)))
      with (q_pow A (Datatypes.S (m + Datatypes.S j)) / q_fact (Datatypes.S (m + Datatypes.S j))).
    2: { rewrite Hm. reflexivity. }
    (* 目标：A^{S(m+Datatypes.S j)}/(S(m+Datatypes.S j))! ≤ (A^m/m!)·(1/2)^{Datatypes.S j}·(1/2)
       由单步 at (m+Datatypes.S j) 与 IH（A^{m+Datatypes.S j}/(m+Datatypes.S j)! ≤ (A^m/m!)·(1/2)^{Datatypes.S j}）。 *)
    apply (Qle_trans _ ((q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j)) * (1 / 2)) _).
    { (* A^{S(m+Datatypes.S j)}/(S(m+Datatypes.S j))! ≤ (A^{m+Datatypes.S j}/(m+Datatypes.S j)!)·(1/2)：单步 at (m+Datatypes.S j) *)
      apply QleT'_to_Qle.
      apply (pow_fact_geom_step A (m + Datatypes.S j) HA).
      apply (Hgeom (m + Datatypes.S j)%nat). apply NatLe_lift. lia. }
    { (* (A^{m+Datatypes.S j}/(m+Datatypes.S j)!)·(1/2) ≤ (A^m/m!)·(1/2)^{Datatypes.S j}·(1/2)：
         由 IH 于 m 乘 (1/2)（Qmult_le_compat_r），目标 RHS 结合序用 mult_assoc 换形 *)
      setoid_replace ((q_pow A m / q_fact m) * (q_pow (1 / 2) (Datatypes.S j) * (1 / 2)))
        with ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j) * (1 / 2)).
      2: { apply Qmult_assoc. }
      apply (Qmult_le_compat_r (q_pow A (m + Datatypes.S j) / q_fact (m + Datatypes.S j))
                               ((q_pow A m / q_fact m) * q_pow (1 / 2) (Datatypes.S j))
                               (1 / 2)).
      - exact (IH m Hgeom).
      - apply Qlt_le_weak. unfold Qlt; simpl; lia. }
Qed.

(* ============================================================ *)
(* 阶段 A 续：exp_partial_cauchy 主定理                        *)
(* 路线：A=|x| → 阿基米德 N0（2A ≤ (t+1)#1）→ 尾和三角          *)
(*   ≤ Σ A^{Datatypes.S k}/(Datatypes.S k)! ≤ (A^m/m!)·geo_sum ≤ (A^m/m!)·2         *)
(*   → 取 m ≥ N0 使 (A^m/m!)·2 < eps（(1/2)^t 衰减 + 阿基米德）  *)
(* 纯构造性：Set 层等同类型 Id + QltT（副本主文件 L57/L2943）   *)
(* 零 承认、零经典公理、sigT 信息性结论、可提取 OCaml          *)
(* ============================================================ *)

Lemma Q2_pos : QltT 0 (1 + 1)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt; simpl; lia. Qed.

Lemma Q2_nonneg : QleT' 0 (1 + 1)%Q.
Proof.
  apply Qle_to_QleT'.
  (* ToyR 替换：Z 层直构（消 Qlt_le_weak→Q2_pos 转发链）：
     Qle 展开 = 交叉积 Z.le，字面归约后线性判定闭合 *)
  unfold Qle.
  simpl.
  lia.
Qed.

Lemma Qhalf_pos : QltT 0 (1 / 2)%Q.
Proof. apply Qlt_to_QltT. unfold Qlt; simpl; lia. Qed.

Lemma Qhalf_nonneg : QleT' 0 (1 / 2)%Q.
Proof.
  apply Qle_to_QleT'.
  (* ToyR 替换：Z 层直构（消 Qlt_le_weak→Qhalf_pos 转发链）：
     Qle 展开 = 交叉积 Z.le，字面归约后线性判定闭合 *)
  unfold Qle.
  simpl.
  lia.
Qed.

Lemma Qle_of_nat : forall a b : nat, (a <= b)%nat ->
  QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  apply Qle_to_QleT'.
  unfold Qle; simpl; lia.
Qed.

Lemma Qlt_of_nat_lt : forall a b : nat, (a < b)%nat ->
  QltT (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b Hab.
  apply Qlt_to_QltT.
  unfold Qlt; simpl; lia.
Qed.

Lemma q_pow_wd : forall x y n,QeqT ( x ) ( y )->QeqT ( q_pow x n ) ( q_pow y n).
Proof.
  intros x y n Hxy. apply qeq_imp_qeqT.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite (qeqT_imp_qeq _ _ Hxy). reflexivity.
Qed.

Lemma q_pow_add : forall (x : Q) (a b : nat),QeqT ( q_pow x (a + b) ) ( q_pow x a * q_pow x b).
Proof.
  intros x a b. apply qeq_imp_qeqT.
  induction a as [| a IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma q_half_pow_le_one : forall k : nat, QleT' (q_pow (1 / 2)%Q k) 1.
Proof.
  intros k. apply Qle_to_QleT'.
  induction k as [| k IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (Qmult (1 / 2)%Q 1) _).
    + apply (Qmult_le_compat_nonneg (1 / 2)%Q (1 / 2)%Q (q_pow (1 / 2)%Q k) 1).
      * split; [apply QleT'_to_Qle; exact Qhalf_nonneg | apply Qle_refl].
      * split; [apply QleT'_to_Qle; apply (q_pow_nonneg (1 / 2)%Q k Qhalf_nonneg) | exact IH].
    + unfold Qle; simpl; lia.
Qed.

(* (1/2)·(1/(n+1)#1) == 1/(2·(n+1)#1)（field 恒等式独立引理） *)
Lemma half_inv_shift : forall n : nat,QeqT (
  (1 / 2)%Q * (1 / (Z.of_nat (n + 1) # 1)) ) (
  1 / ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))).
Proof.
  intro n. apply qeq_imp_qeqT.
  field.
  all: try (intro Hz0;
            assert (Hlt0 : QltT 0 (Z.of_nat (n + 1) # 1))
              by (apply (Qlt_of_nat_lt 0 (n + 1)); lia);
            destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  all: try (intro Hz0;
            assert (Hlt0 : QltT 0 ((1 + 1)%Q * (Z.of_nat (n + 1) # 1)))
              by (apply Qlt_to_QltT;
                  apply (Qmult_lt_0_compat (1 + 1)%Q (Z.of_nat (n + 1) # 1));
                  [ apply QltT_to_Qlt; exact Q2_pos
                  | apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (n + 1)); lia ]);
            destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
Qed.

(* (1+1)%Q·(n+1)#1 == (2(n+1))#1（Qmake 直接计算 + lia，避开 Z 乘法 match 残渣） *)
Lemma Q2_mul_nat : forall n : nat,QeqT (
  (1 + 1)%Q * (Z.of_nat (n + 1) # 1) ) ( Z.of_nat (2 * (n + 1)) # 1).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  change ((1 + 1)%Q) with (Qmake 2 1).
  unfold Qeq. cbn [Qnum Qden Qmult]. lia.
Qed.

(* (1/2)^n ≤ 1/(n+1)#1（归纳 + 除法比较三明治） *)
Lemma q_half_pow_le_inv : forall n : nat,
  QleT' (q_pow (1 / 2)%Q n) (1 / (Z.of_nat (n + 1) # 1)).
Proof.
  intro n. induction n as [| n IH].
  - simpl. apply Qle_to_QleT'. unfold Qle; simpl; lia.
  - assert (Hn : (Datatypes.S n + 1)%nat = (n + 2)%nat) by lia. rewrite Hn.
    simpl. apply Qle_to_QleT'.
    change ((1 / 2)%Q * q_pow (1 / 2)%Q n <= 1 / (Z.of_nat (n + 2) # 1)).
    apply (Qle_trans _ ((1 / 2)%Q * (1 / (Z.of_nat (n + 1) # 1))) _).
    + apply (Qmult_le_compat_nonneg (1 / 2)%Q (1 / 2)%Q (q_pow (1 / 2)%Q n)
                                    (1 / (Z.of_nat (n + 1) # 1))).
      * split; [exact (QleT'_to_Qle _ _ Qhalf_nonneg) | apply Qle_refl].
      * split; [exact (QleT'_to_Qle _ _ (q_pow_nonneg (1 / 2)%Q n Qhalf_nonneg))
               | exact (QleT'_to_Qle _ _ IH)].
    + apply (Qle_trans _ (1 / ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (half_inv_shift n)).
      * apply QleT'_to_Qle.
        apply (q_le_div_le 1 ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))
                            1 (Z.of_nat (n + 2) # 1)).
        -- apply Qlt_to_QltT.
           apply (Qmult_lt_0_compat (1 + 1)%Q (Z.of_nat (n + 1) # 1)).
           ++ apply QltT_to_Qlt. apply Q2_pos.
           ++ apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (n + 1)). lia.
        -- apply (Qlt_of_nat_lt 0 (n + 2)). lia.
        -- (* 1·(n+2)#1 ≤ 1·((1+1)·(n+1)#1)：setoid 消 1· 因子，Qle_of_nat 收尾 *)
           apply Qle_to_QleT'.
           setoid_rewrite (Qmult_1_l (Z.of_nat (n + 2) # 1)).
           setoid_rewrite (Qmult_1_l ((1 + 1)%Q * (Z.of_nat (n + 1) # 1))).
           apply (Qle_trans _ (Z.of_nat (2 * (n + 1)) # 1) _).
           ++ apply QleT'_to_Qle. apply Qle_of_nat. lia.
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              apply Qeq_sym. apply qeqT_imp_qeq. apply Q2_mul_nat.
Qed.

(* 阿基米德（Set 层）：∃N, ∀t ≥ N, 2A ≤T (t+1)#1（Qarchimedean + positive_nat_Z；完全构造论证 NatLe/QleT' 化） *)
Lemma q_arch_geom : forall A : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)).
Proof.
  intro A.
  destruct (Qarchimedean (Qmult (1 + 1)%Q A)) as [p Hp].
  exists (Pos.to_nat p).
  intros t Ht.
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (Z.pos p # 1) _).
  - exact Hp.
  - setoid_rewrite <- (qeqT_imp_qeq _ _ (positive_nat_Z p)).
    apply QltT_to_Qlt. apply (Qlt_of_nat_lt (Pos.to_nat p) (t + 1)).
    apply NatLe_drop in Ht. lia.
Qed.

(* 衰减：∀C ≥ 0, ∀eps > 0, ∃t, C·(1/2)^{S t} < eps *)
(* 衰减（Set 层）：∀C ≥T 0, ∀eps >T 0, ∃t, C·(1/2)^{S t} <T eps（完全构造论证 QleT'/QltT 化） *)
Lemma arch_decay : forall (C eps : Q), QleT' 0 C -> QltT 0 eps ->
  sigT (fun t : nat => QltT (C * q_pow (1 / 2)%Q (Datatypes.S t)) eps).
Proof.
  intros C eps HC Hep.
  destruct (Qarchimedean (C / eps)) as [p Hp].
  exists (Pos.to_nat p).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (C * (1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1))) _).
  - apply (Qle_trans _ (q_pow (1 / 2)%Q (Datatypes.S (Pos.to_nat p)) * C) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1)) * C) _).
      * apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (Datatypes.S (Pos.to_nat p)))
                                 (1 / (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1)) C).
        -- apply QleT'_to_Qle. apply (q_half_pow_le_inv (Datatypes.S (Pos.to_nat p))).
        -- exact (QleT'_to_Qle _ _ HC).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qlt_shift_div_r C (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) eps).
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (Datatypes.S (Pos.to_nat p) + 1)); lia.
    + apply (Qlt_le_trans _ (eps * (Z.pos p # 1)) _).
      * pose proof (Qmult_lt_compat_r (C / eps) (Z.pos p # 1) eps (QltT_to_Qlt _ _ Hep) Hp) as Hm.
        assert (Hf : (C / eps) * eps == C) by (field; intro Hz0; destruct (q_neq_of_lt eps Hep (qeq_imp_qeqT _ _ Hz0))).
        setoid_rewrite Hf in Hm.
        setoid_rewrite (Qmult_comm (Z.pos p # 1) eps) in Hm.
        exact Hm.
      * apply (Qle_trans _ ((Z.pos p # 1) * eps) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) * eps) _).
           ++ apply (Qmult_le_compat_r (Z.pos p # 1)
                                      (Z.of_nat (Datatypes.S (Pos.to_nat p) + 1) # 1) eps).
              ** setoid_rewrite <- (qeqT_imp_qeq _ _ (positive_nat_Z p)).
                 apply QleT'_to_Qle. apply (Qle_of_nat (Pos.to_nat p) (Datatypes.S (Pos.to_nat p) + 1)). lia.
              ** apply Qlt_le_weak. exact (QltT_to_Qlt _ _ Hep).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.
(* Qabs 的除法分解 *)
Lemma q_abs_div : forall a b : Q,QeqT ( Qabs (a / b) ) ( Qabs a / Qabs b).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qdiv.
  rewrite Qabs_Qmult. rewrite Qabs_Qinv. reflexivity.
Qed.

(* |x^{Datatypes.S n}/(Datatypes.S n)!| == A^{Datatypes.S n}/(Datatypes.S n)!（A := |x|） *)
Lemma q_abs_pow_fact : forall x n,QeqT (
  Qabs (q_pow x (Datatypes.S n) / q_fact (Datatypes.S n)) ) ( q_pow (Qabs x) (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intros x n. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (q_abs_div _ _)).
  rewrite (qeqT_imp_qeq _ _ (q_pow_abs _ _)).
  rewrite (Qabs_pos (q_fact (Datatypes.S n))
                    (Qlt_le_weak 0 (q_fact (Datatypes.S n))
                       (QltT_to_Qlt 0 (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n))))).
  reflexivity.
Qed.

(* 0 ≤ A^m/m! *)
Lemma q_pow_fact_nonneg : forall A m, QleT' 0 A -> QleT' 0 (q_pow A m / q_fact m).
Proof.
  intros A m HA.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle. apply (q_le_div_le 0 1 (q_pow A m) (q_fact m)).
  - vm_compute. reflexivity.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ 0 _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (q_pow A m) _).
      * apply QleT'_to_Qle. apply q_pow_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 0 ≤ (A^m/m!)·2 *)
Lemma q_pow_fact2_nonneg : forall A m, QleT' 0 A -> QleT' 0 ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m HA.
  apply Qle_to_QleT'.
  exact (Qmult_le_compat_r 0 (q_pow A m / q_fact m) (1 + 1)%Q
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg A m HA)) (QleT'_to_Qle _ _ Q2_nonneg)).
Qed.

(* (1/2)^a ≤ (1/2)^b（a ≥ b） *)
Lemma q_half_pow_mono : forall a b : nat, (b <= a)%nat ->
  QleT' (q_pow (1 / 2)%Q a) (q_pow (1 / 2)%Q b).
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  assert (Ha : (a = b + (a - b))%nat) by lia.
  rewrite Ha. rewrite (qeqT_imp_qeq _ _ (q_pow_add (1 / 2)%Q b (a - b))).
  apply (Qle_trans _ (q_pow (1 / 2)%Q (a - b) * q_pow (1 / 2)%Q b) _).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ (1 * q_pow (1 / 2)%Q b) _).
    + apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (a - b)) 1 (q_pow (1 / 2)%Q b)).
      * apply QleT'_to_Qle. apply q_half_pow_le_one.
      * apply QleT'_to_Qle. apply (q_pow_nonneg (1 / 2)%Q b Qhalf_nonneg).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ===== exp_tail：尾和 Σ_{k=m}^{n-1} x^{Datatypes.S k}/(Datatypes.S k)!（guard 版） ===== *)
Fixpoint exp_tail (m : nat) (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => exp_tail m n' x + (if Nat.leb m n' then q_pow x (Datatypes.S n') / q_fact (Datatypes.S n') else 0)
  end.

Fixpoint exp_tail_abs (m : nat) (n : nat) (A : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => exp_tail_abs m n' A + (if Nat.leb m n' then q_pow A (Datatypes.S n') / q_fact (Datatypes.S n') else 0)
  end.

Lemma q_div_wd : forall a b c : Q,QeqT ( a ) ( b )->QeqT ( a / c ) ( b / c).
Proof.
  intros a b c H. apply qeq_imp_qeqT. unfold Qdiv.
  apply qeqT_imp_qeq in H. rewrite H. reflexivity.
Qed.

Lemma exp_tail_abs_wd : forall (m n : nat) (A B : Q),QeqT ( A ) ( B )->QeqT ( exp_tail_abs m n A ) ( exp_tail_abs m n B).
Proof.
  intros m n A B HAB. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E; rewrite IH.
    + rewrite (qeqT_imp_qeq _ _ (q_pow_wd A B (Datatypes.S n) HAB)). reflexivity.
    + reflexivity.
Qed.

(* n ≤ m ⟹ 尾和为零 *)
Lemma exp_tail_le_m : forall m n x, (n <= m)%nat ->QeqT ( exp_tail m n x ) ( 0).
Proof.
  intros m n x Hn. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (IH Hn'). ring.
Qed.

Lemma exp_tail_abs_le_m : forall m n A, (n <= m)%nat ->QeqT ( exp_tail_abs m n A ) ( 0).
Proof.
  intros m n A Hn. apply qeq_imp_qeqT. induction n as [| n IH]; simpl.
  - reflexivity.
  - destruct (Nat.leb m n) eqn:E.
    + exfalso. apply Nat.leb_le in E. lia.
    + assert (Hn' : (n <= m)%nat) by lia.
      rewrite (IH Hn'). ring.
Qed.

(* 差恒等式：m ≤ n ⟹ ep n - ep m == tail m n x（归纳组装） *)
Lemma exp_partial_diff_tail : forall m n x, (m <= n)%nat ->QeqT (
  exp_partial n x - exp_partial m x ) ( exp_tail m n x).
Proof.
  intros m n x Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply qeq_imp_qeqT. assert (Hm0 : (m = 0)%nat) by lia. subst m. reflexivity.
  - apply qeq_imp_qeqT. simpl.
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      assert (Hring : exp_partial n x + q_pow x (Datatypes.S n) / q_fact (Datatypes.S n) - exp_partial m x ==
                      (exp_partial n x - exp_partial m x) + q_pow x (Datatypes.S n) / q_fact (Datatypes.S n)).
      { ring. }
      rewrite Hring. rewrite (qeqT_imp_qeq _ _ (IH E)). reflexivity.
    + apply Nat.leb_gt in E.
      assert (Hm : (m = Datatypes.S n)%nat) by lia. subst m.
      simpl.
      assert (Hle : (n <= Datatypes.S n)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_le_m (Datatypes.S n) n x Hle)).
      ring.
Qed.

(* 三角不等式：|tail| ≤ tail_abs *)
Lemma exp_tail_abs_le : forall m n x,
  QleT' (Qabs (exp_tail m n x)) (exp_tail_abs m n (Qabs x)).
Proof.
  intros m n x. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - unfold Qle; simpl; lia.
  - destruct (Nat.leb m n) eqn:E.
    + apply (Qle_trans _ (Qabs (exp_tail m n x) + Qabs (q_pow x (Datatypes.S n) / q_fact (Datatypes.S n))) _).
      * apply Qabs_triangle.
      * apply Qplus_le_compat;
          [ exact IH
          | (apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; apply (qeqT_imp_qeq _ _ (q_abs_pow_fact x n))) ].
    + setoid_rewrite (Qplus_0_r (exp_tail_abs m n (Qabs x))).
      apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_tail m n x + 0) (exp_tail m n x)). ring.
      * exact IH.
Qed.

(* 尾和 ≤ (A^m/m!)·geo_sum (Datatypes.S (n-m))（归纳于 n，geo_sum 中间界） *)
Lemma exp_tail_abs_geom : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))).
Proof.
  intros A m n HA Hgeom Hmn.
  revert Hmn.
  induction n as [| n IH]; intros Hmn.
  - apply Qle_to_QleT'. assert (Hm0 : (m = 0)%nat) by lia. subst m.
    simpl. unfold Qle; simpl; lia.
  - (* 仅展开 exp_tail_abs（勿 simpl 整个目标，避免 geo_sum 指标变形） *)
    apply Qle_to_QleT'.
    change (exp_tail_abs m (Datatypes.S n) A)
      with (exp_tail_abs m n A + (if Nat.leb m n then q_pow A (Datatypes.S n) / q_fact (Datatypes.S n) else 0)).
    destruct (Nat.leb m n) eqn:Emn.
    + apply Nat.leb_le in Emn.
      apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))
                          + (q_pow A m / q_fact m) * q_pow (1 / 2)%Q (Datatypes.S (n - m))) _).
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _ (IH Emn)).
        -- apply (Qle_trans _ (q_pow A (m + Datatypes.S (n - m)) / q_fact (m + Datatypes.S (n - m))) _).
           ++ apply QleT'_to_Qle. apply qeq_le.
           apply qeq_imp_qeqT.
              assert (Hn : (Datatypes.S n = m + Datatypes.S (n - m))%nat) by lia.
              rewrite Hn. reflexivity.
           ++ exact (QleT'_to_Qle _ _ (pow_fact_geom_iter A m (n - m) HA Hgeom)).
      * replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S (Datatypes.S (n - m)))%nat by lia.
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        change (geo_sum (Datatypes.S (Datatypes.S (n - m))))
          with (geo_sum (Datatypes.S (n - m)) + q_pow (1 / 2)%Q (Datatypes.S (n - m))).
        ring.
    + apply Nat.leb_gt in Emn.
      assert (Hle : (n <= m)%nat) by lia.
      rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m m n A Hle)).
      replace (Datatypes.S ((Datatypes.S n) - m))%nat with (Datatypes.S 0)%nat by lia.
      simpl.
      apply (Qle_trans _ (q_pow A m / q_fact m) _).
      * apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* 尾和 ≤ (A^m/m!)·2（geo_sum ≤ 2 收尾） *)
Lemma exp_tail_abs_geom2 : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m n HA Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((q_pow A m / q_fact m) * geo_sum (Datatypes.S (n - m))) _).
  - apply QleT'_to_Qle. apply exp_tail_abs_geom; assumption.
  - apply (Qle_trans _ (geo_sum (Datatypes.S (n - m)) * (q_pow A m / q_fact m)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((1 + 1)%Q * (q_pow A m / q_fact m)) _).
      * apply (Qmult_le_compat_r (geo_sum (Datatypes.S (n - m))) (1 + 1)%Q (q_pow A m / q_fact m)).
        -- apply QleT'_to_Qle. apply geo_sum_le_two.
        -- apply QleT'_to_Qle. apply q_pow_fact_nonneg. exact HA.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* A^b/b! ≤ (A^{N0}/N0!)·(1/2)^{b-N0}（b ≥ N0，iter 一步跳） *)
Lemma pow_fact_decay : forall (A : Q) (N0 b : nat),
  QleT' 0 A ->
  (forall t : nat, NatLe N0 t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (N0 <= b)%nat ->
  QleT' (q_pow A b / q_fact b) ((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0)).
Proof.
  intros A N0 b HA Hgeom HNb.
  apply Qle_to_QleT'.
  destruct (Nat.sub b N0) as [| j] eqn:E.
  - assert (Hb : (b = N0)%nat) by lia. subst b.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. simpl. ring.
  - assert (Hb : (b = N0 + Datatypes.S j)%nat) by lia. subst b.
    exact (QleT'_to_Qle _ _ (pow_fact_geom_iter A N0 j HA Hgeom)).
Qed.

(* 最终衰减：(A^b/b!)·2 < eps（b ≥ N0 + S t，C·(1/2)^{S t} < eps） *)
Lemma exp_tail_arch : forall (A : Q) (N0 t b : nat) (eps : Q),
  QleT' 0 A ->
  (forall u : nat, NatLe N0 u -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (u + 1) # 1)) ->
  QltT 0 eps ->
  QltT (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (Datatypes.S t)) eps ->
  (N0 + Datatypes.S t <= b)%nat ->
  QltT ((q_pow A b / q_fact b) * (1 + 1)%Q) eps.
Proof.
  intros A N0 t b eps HA Hgeom Hep Hdec Hb.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0)) * (1 + 1)%Q) _).
  - apply (Qmult_le_compat_r (q_pow A b / q_fact b)
                             ((q_pow A N0 / q_fact N0) * q_pow (1 / 2)%Q (b - N0))
                             (1 + 1)%Q).
    + apply QleT'_to_Qle. apply pow_fact_decay; [exact HA | exact Hgeom | lia].
    + apply QleT'_to_Qle. apply Q2_nonneg.
  - apply (Qle_lt_trans _ (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (Datatypes.S t)) _).
    + apply (Qle_trans _ (((q_pow A N0 / q_fact N0) * (1 + 1)%Q) * q_pow (1 / 2)%Q (b - N0)) _).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (q_pow (1 / 2)%Q (b - N0) * ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_pow (1 / 2)%Q (Datatypes.S t) * ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)) _).
           ++ apply (Qmult_le_compat_r (q_pow (1 / 2)%Q (b - N0)) (q_pow (1 / 2)%Q (Datatypes.S t))
                                      ((q_pow A N0 / q_fact N0) * (1 + 1)%Q)).
              ** apply QleT'_to_Qle. apply (q_half_pow_mono (b - N0) (Datatypes.S t)). lia.
              ** apply QleT'_to_Qle. apply (q_pow_fact2_nonneg A N0 HA).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + exact (QltT_to_Qlt _ _ Hdec).
Qed.

(* 主界：m ≤ n ⟹ |ep n - ep m| ≤ (A^m/m!)·2 *)
Lemma exp_partial_diff_bound : forall (x A : Q) (m n : nat),QeqT (
  A ) ( Qabs x )->
  QleT' 0 A ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q A) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (exp_partial n x - exp_partial m x)) ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros x A m n HxA HAp Hgeom Hmn.
  apply Qle_to_QleT'.
  assert (Hsym : QeqT (Qabs x) A)
    by (apply qeq_imp_qeqT; apply Qeq_sym; apply qeqT_imp_qeq; exact HxA).
  apply (Qle_trans _ (exp_tail_abs m n A) _).
  - apply (Qle_trans _ (exp_tail_abs m n (Qabs x)) _).
    + apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_partial n x - exp_partial m x) (exp_tail m n x)).
        apply qeqT_imp_qeq. apply exp_partial_diff_tail. exact Hmn.
      * apply QleT'_to_Qle. apply exp_tail_abs_le.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (exp_tail_abs_wd _ _ _ _ Hsym)).
  - apply QleT'_to_Qle. apply exp_tail_abs_geom2; assumption.
Qed.

(* ===== 主定理：exp 部分和是柯西序列（Set 层、零 承认） ===== *)
Lemma exp_partial_cauchy : forall (x : Q) (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT (Qabs (exp_partial m x - exp_partial n x)) eps).
Proof.
  intros x eps Hep.
  set (A := Qabs x).
  assert (HA : Qle 0 A) by (unfold A; apply Qabs_nonneg).
  destruct (q_arch_geom A) as [N0 HN0].
  set (C := (q_pow A N0 / q_fact N0) * (1 + 1)%Q).
  assert (HC : QleT' 0 C) by (unfold C; apply q_pow_fact2_nonneg; exact (Qle_to_QleT' _ _ HA)).
  destruct (arch_decay C eps HC Hep) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - (* m ≤ n：以 m 为底 *)
    assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    assert (Hbound : Qle (Qabs (exp_partial n x - exp_partial m x))
                         ((q_pow A m / q_fact m) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound x A m n).
      - apply qeq_imp_qeqT. reflexivity.
      - exact (Qle_to_QleT' _ _ HA).
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow A m / q_fact m) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch A N0 t m eps (Qle_to_QleT' _ _ HA) (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (Qabs (exp_partial n x - exp_partial m x)) _).
    + apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
      rewrite (Qabs_Qminus (exp_partial m x) (exp_partial n x)). reflexivity.
    + exact (Qle_lt_trans _ ((q_pow A m / q_fact m) * (1 + 1)%Q) _ Hbound Hlt).
  - (* n < m：以 n 为底，|ep m - ep n| 直接就是 bound 的结论形态 *)
    assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (exp_partial m x - exp_partial n x))
                         ((q_pow A n / q_fact n) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound x A n m).
      - apply qeq_imp_qeqT. reflexivity.
      - exact (Qle_to_QleT' _ _ HA).
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow A n / q_fact n) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch A N0 t n eps (Qle_to_QleT' _ _ HA) (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow A n / q_fact n) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

End QExpPartial.
(* ============================================================ *)
(* 工程③阶段 B：Q 层缺环 + Real 层 exp（合并自 probe_exp2.v）   *)
(* ============================================================ *)
(* ================= Q 层缺环 ================= *)

(* 1. 幂单调：0 ≤ A ≤ B ⟹ A^n ≤ B^n *)
Lemma q_pow_mono : forall (A B : Q) (n : nat),
  QleT' 0 A -> QleT' A B -> QleT' (q_pow A n) (q_pow B n).
Proof.
  intros A B n HA HAB. apply Qle_to_QleT'. induction n as [| m IH]; simpl.
  - exact (Qle_refl 1).
  - exact (Qmult_le_compat_nonneg A B (q_pow A m) (q_pow B m)
  (conj (QleT'_to_Qle _ _ HA) (QleT'_to_Qle _ _ HAB))
  (conj (QleT'_to_Qle _ _ (q_pow_nonneg A m HA)) IH)).
Qed.

(* 2. exp 级数：exp_series n B = Σ_{j=0}^{n} B^j / j!（与 exp_partial n x 定义性同构） *)
Fixpoint exp_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_series m B + q_pow B (Datatypes.S m) / q_fact (Datatypes.S m)
  end.

(* 3. 单步单调：0 ≤ B ⟹ exp_series n B ≤ exp_series (S n) B（非负项） *)
Lemma exp_series_step_mono : forall (B : Q) (n : nat), QleT' 0 B ->
  QleT' (exp_series n B) (exp_series (Datatypes.S n) B).
Proof.
  intros B n HB. apply Qle_to_QleT'. simpl.
  exact (Qle_plus_nonneg_r (exp_series n B)
  (q_pow B (Datatypes.S n) / q_fact (Datatypes.S n))
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg B (Datatypes.S n) HB))).
Qed.

(* 4. 链式单调：n ≤ m ⟹ exp_series n B ≤ exp_series m B *)
Lemma exp_series_mono : forall (B : Q) (n m : nat), QleT' 0 B -> (n <= m)%nat ->
  QleT' (exp_series n B) (exp_series m B).
Proof.
  intros B n m HB Hnm. apply Qle_to_QleT'. induction Hnm as [| m' _ IHIH].
  - exact (Qle_refl (exp_series n B)).
  - exact (Qle_trans (exp_series n B) (exp_series m' B)
  (exp_series (Datatypes.S m') B) IHIH (QleT'_to_Qle _ _ (exp_series_step_mono B m' HB))).
Qed.

(* 5. 尾和非负：0 ≤ A ⟹ 0 ≤ exp_tail_abs m n A *)
Lemma exp_tail_abs_nonneg : forall (m n : nat) (A : Q), QleT' 0 A -> QleT' 0 (exp_tail_abs m n A).
Proof.
  intros m n A HA. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - exact (Qle_refl 0).
  - destruct (Nat.leb m n) eqn:E.
  + exact (Qle_trans 0 (exp_tail_abs m n A)
  (exp_tail_abs m n A + (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n)))
  IH (Qle_plus_nonneg_r (exp_tail_abs m n A)
  (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n))
  (QleT'_to_Qle _ _ (q_pow_fact_nonneg A (Datatypes.S n) HA)))).
  + exact (Qle_trans 0 (exp_tail_abs m n A) (exp_tail_abs m n A + 0) IH
  (Qle_plus_nonneg_r (exp_tail_abs m n A) 0 (Qle_refl 0))).
Qed.

(* 6. 尾和单调（第二参数）：0 ≤ A ≤ B ⟹ exp_tail_abs m n A ≤ exp_tail_abs m n B *)
Lemma exp_tail_abs_mono : forall (m n : nat) (A B : Q), QleT' 0 A -> QleT' A B ->
  QleT' (exp_tail_abs m n A) (exp_tail_abs m n B).
Proof.
  intros m n A B HA HAB. apply Qle_to_QleT'. induction n as [| n IH]; simpl.
  - exact (Qle_refl 0).
  - destruct (Nat.leb m n) eqn:E.
  + exact (Qplus_le_compat (exp_tail_abs m n A) (exp_tail_abs m n B)
  (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n))
  (q_pow B (Datatypes.S n) / q_fact (Datatypes.S n)) IH
  (QleT'_to_Qle _ _ (Qle_div_same_denom (q_pow A (Datatypes.S n)) (q_pow B (Datatypes.S n))
  (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n))
  (q_pow_mono A B (Datatypes.S n) HA HAB)))).
  + exact (Qle_trans (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
  (exp_tail_abs m n B + 0)
  (QleT'_to_Qle _ _ (qeq_imp_qle (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
  (qeq_imp_qeqT (exp_tail_abs m n A + 0) (exp_tail_abs m n A)
   (Qplus_0_r (exp_tail_abs m n A)))))
  (Qle_trans (exp_tail_abs m n A) (exp_tail_abs m n B)
  (exp_tail_abs m n B + 0) IH
  (Qle_plus_nonneg_r (exp_tail_abs m n B) 0 (Qle_refl 0)))).
Qed.

(* 7b. nat 后继字面量恒等式：(S k)#1 + 1 == (S(S k))#1 *)
Lemma q_succ_add : forall (k : nat),QeqT (
  Qplus (Z.of_nat (Datatypes.S k) # 1) 1 ) ( Z.of_nat (Datatypes.S (Datatypes.S k)) # 1).
Proof.
  intros k.
  apply qeq_imp_qeqT.
  assert (Hn : Z.add (Z.of_nat (Datatypes.S k)) 1 = Z.of_nat (Datatypes.S (Datatypes.S k))) by lia.
  unfold Qeq, Qplus, Qred. simpl.
  rewrite (Pos.mul_1_r (PosDef.Pos.of_succ_nat k)).
  rewrite (Pos.mul_1_r (PosDef.Pos.add (PosDef.Pos.of_succ_nat k) 1)).
  rewrite (Pos.mul_1_r (PosDef.Pos.succ (PosDef.Pos.of_succ_nat k))).
  apply f_equal. apply Pos.add_1_r.
Qed.

(* 7. 幂差分界（S n 形态，无下溢）：|x^{S n} − y^{S n}| ≤ |x−y|·((S n)#1·B^n) *)
Lemma q_pow_diff_bound : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (q_pow x (Datatypes.S n) - q_pow y (Datatypes.S n)))
      (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S n) # 1) (q_pow B n))).
Proof.
  intros x y B n HB Hx Hy.
  assert (HB' : Qle 0 B) by (apply QleT'_to_Qle; exact HB).
  assert (Hx' : Qle (Qabs x) B) by (apply QleT'_to_Qle; exact Hx).
  apply Qle_to_QleT'.
  induction n as [| m IH].
  - (* n = 0：|x^1 − y^1| = |x−y| ≤ |x−y|·(1#1·B^0) *)
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ x 0)), (qeqT_imp_qeq _ _ (q_pow_succ y 0)).
    setoid_replace (q_pow x 0) with 1 by reflexivity.
    assert (Hxy : Qmult x 1 - Qmult y 1 == x - y) by ring.
    apply (Qle_trans _ (Qabs (x - y)) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (Qmult x 1 - Qmult y 1) (x - y)). exact Hxy. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_1_r. }
  - (* n = S m：拆分 x·x^{Sm} − y·y^{Sm}，三角 + IH *)
    assert (Halg : q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m)) ==
                   x * (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)) + (x - y) * q_pow y (Datatypes.S m)).
    { simpl. ring. }
    setoid_rewrite Halg.
    apply (Qle_trans _ (Qabs (Qmult x (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))) +
                        Qabs (Qmult (x - y) (q_pow y (Datatypes.S m)))) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qplus (Qmult (Qabs x) (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))))
                                (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
      * apply Qplus_le_compat.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
        -- apply (Qle_trans _ (Qmult (Qabs (x - y)) (Qabs (q_pow y (Datatypes.S m)))) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
           ++ apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                            (Qabs (q_pow y (Datatypes.S m))) (q_pow B (Datatypes.S m))).
              ** split; [apply Qabs_nonneg | apply Qle_refl].
              ** split; [apply Qabs_nonneg | (rewrite (qeqT_imp_qeq _ _ (q_pow_abs _ _)); apply (QleT'_to_Qle _ _); apply q_pow_mono; [apply Qle_to_QleT'; apply Qabs_nonneg | exact Hy])].
      * apply (Qle_trans _ (Qplus (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
        -- apply Qplus_le_compat.
           ++ apply (Qle_trans _ (Qmult B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))) _).
              ** apply (Qmult_le_compat_r (Qabs x) B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))).
                 ---- exact Hx'.
                 ---- apply Qabs_nonneg.
              ** apply (Qmult_le_compat_nonneg B B
                                            (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))
                                            (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m)))).
                 ---- split; [exact HB' | apply Qle_refl].
                 ---- split; [apply Qabs_nonneg | exact IH].
           ++ (* 第二项 |x−y|·B^{Sm} ≤ |x−y|·B^{Sm}：refl（上层已换形） *)
              apply Qle_refl.
        -- (* 代数：B·(|x−y|·(Sm#1·B^m)) + |x−y|·B^{Sm} == |x−y|·((S(S m))#1·B^{S m}) *)
           setoid_replace (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m)))).
           2: { assert (Hbs : q_pow B (Datatypes.S m) == B * q_pow B m) by (apply qeqT_imp_qeq; apply q_pow_succ).
                setoid_rewrite Hbs. ring. }
           setoid_replace (Qplus (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m))))
                                 (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m)))).
           2: ring.
           setoid_replace (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))).
           2: { setoid_rewrite (qeqT_imp_qeq _ _ (q_succ_add m)). reflexivity. }
           apply Qle_refl.
Qed.

(* 8. 比率约分：((S k)#1·B^k)·/((S k)!) == B^k·/(k!) *)
Lemma q_ratio_cancel_succ : forall (B : Q) (k : nat),QeqT (
  Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
        (Qinv (q_fact (Datatypes.S k)))
  ) ( q_pow B k * Qinv (q_fact k)).
Proof.
  intros B k.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (Datatypes.S k) # 1) (q_fact k)).
  setoid_replace (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
                        (Qmult (Qinv (Z.of_nat (Datatypes.S k) # 1)) (Qinv (q_fact k))))
    with (Qmult (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (Qinv (Z.of_nat (Datatypes.S k) # 1))) (q_pow B k)) (Qinv (q_fact k))).
  2: ring.
  rewrite (Qmult_inv_r (Z.of_nat (Datatypes.S k) # 1)).
  - ring.
  - unfold Qeq. simpl. lia.
Qed.

(* 9. 尾差 ≤ 尾和：n ≤ k ⟹ exp_series k B − exp_series n B ≤ exp_tail_abs n k B *)
Lemma exp_series_tail_le : forall (B : Q) (n k : nat), QleT' 0 B -> (n <= k)%nat ->
  QleT' (exp_series k B - exp_series n B) (exp_tail_abs n k B).
Proof.
  intros B n k HB Hnk.
  apply Qle_to_QleT'.
  revert n Hnk.
  induction k as [| k IH]; intros n Hnk.
  - (* k = 0：n = 0 *)
    assert (Hn0 : n = 0%nat) by lia. subst n. simpl.
    apply Qle_refl.
  - simpl.
    destruct (Nat.leb n k) eqn:E.
    + apply Nat.leb_le in E.
      setoid_replace (exp_series k B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k) - exp_series n B)
        with (exp_series k B - exp_series n B + q_pow B (Datatypes.S k) / q_fact (Datatypes.S k)) by ring.
      apply (Qplus_le_compat (exp_series k B - exp_series n B) (exp_tail_abs n k B)
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))
                             (q_pow B (Datatypes.S k) / q_fact (Datatypes.S k))).
      { apply IH. lia. }
      { apply Qle_refl. }
    + apply Nat.leb_gt in E.
      (* k < n：差 ≤ 0 ≤ 尾和非负 *)
      apply (Qle_trans _ 0 _).
      * (* exp_series (S k) B − exp_series n B ≤ 0：mono（S k ≤ n） *)
        apply Qle_minus_iff.
        setoid_replace (0 + - (exp_series (Datatypes.S k) B - exp_series n B))
          with (exp_series n B - exp_series (Datatypes.S k) B) by ring.
        setoid_replace (exp_series n B - exp_series (Datatypes.S k) B)
          with (exp_series n B + - exp_series (Datatypes.S k) B) by ring.
        apply (proj1 (Qle_minus_iff (exp_series (Datatypes.S k) B) (exp_series n B))).
        apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | lia].
      * (* 0 ≤ exp_tail_abs n k B + 0 *)
        setoid_replace (exp_tail_abs n k B + 0) with (exp_tail_abs n k B) by ring.
        apply (QleT'_to_Qle _ _). apply exp_tail_abs_nonneg. exact HB.
Qed.

(* 10. exp 部分和 Lipschitz（S n 形态）：|x|,|y| ≤ B ⟹
       |ep_{S n} x − ep_{S n} y| ≤ |x−y|·exp_series n B *)
Lemma exp_partial_lipschitz_succ : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (exp_partial (Datatypes.S n) x - exp_partial (Datatypes.S n) y))
      (Qmult (Qabs (x - y)) (exp_series n B)).
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  induction n as [| m IH].
  - (* n = 0：|ep_1 x − ep_1 y| = |x − y| ≤ |x−y|·exp_series 0 B = |x−y|·1 *)
    setoid_replace (exp_series 0 B) with 1.
    2: reflexivity.
    assert (H1 : exp_partial 1 x - exp_partial 1 y == x - y).
    { simpl. unfold Qdiv. simpl. field. }
    apply (Qle_trans _ (Qabs (x - y)) _).
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_wd (exp_partial 1 x - exp_partial 1 y) (x - y)). exact H1. }
    { apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_1_r. }
  - (* n = S m *)
    assert (Hstep1 : exp_partial (Datatypes.S (Datatypes.S m)) x ==
                     exp_partial (Datatypes.S m) x + q_pow x (Datatypes.S (Datatypes.S m)) / q_fact (Datatypes.S (Datatypes.S m))).
    { reflexivity. }
    assert (Hstep2 : exp_partial (Datatypes.S (Datatypes.S m)) y ==
                     exp_partial (Datatypes.S m) y + q_pow y (Datatypes.S (Datatypes.S m)) / q_fact (Datatypes.S (Datatypes.S m))).
    { reflexivity. }
    assert (Hsplit : exp_partial (Datatypes.S (Datatypes.S m)) x - exp_partial (Datatypes.S (Datatypes.S m)) y ==
                     (exp_partial (Datatypes.S m) x - exp_partial (Datatypes.S m) y) +
                     (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))) * Qinv (q_fact (Datatypes.S (Datatypes.S m)))).
    { setoid_rewrite Hstep1. setoid_rewrite Hstep2. unfold Qdiv. ring. }
    setoid_rewrite Hsplit.
    apply (Qle_trans _ (Qabs (exp_partial (Datatypes.S m) x - exp_partial (Datatypes.S m) y) +
                        Qabs (Qmult (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m)))
                                   (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))) _).
    + apply Qabs_triangle.
    + (* ≤ |x−y|·(exp_series m B + B^{S m}/(S m)!) == |x−y|·exp_series (S m) B *)
      apply (Qle_trans _ (Qplus (Qmult (Qabs (x - y)) (exp_series m B))
                                (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m))))) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- (* |(x^{S(S m)}−y^{S(S m)})·/((S(S m))!)| ≤ |x−y|·(B^{S m}·/((S m)!)) *)
           apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                     (Qinv (q_fact (Datatypes.S (Datatypes.S m))))) _).
           ++ (* |a·/(f)| ≤ |a|·|/(f)| == |a|·/(f)（f > 0 ⟹ /f > 0） *)
              apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                        (Qabs (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))) _).
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_Qmult.
              ** apply (Qmult_le_compat_nonneg (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                                (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                                (Qabs (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                                                (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                 --- split; [apply Qabs_nonneg | apply Qle_refl].
                 --- split.
                     ---- apply Qabs_nonneg.
                     ---- assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                          { apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos. }
                          apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (Qabs_pos (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) Hinvpos)).
           ++ (* |x^{S(S m)}−y^{S(S m)}|·/((S(S m))!) ≤ |x−y|·(B^{S m}·/((S m)!)) *)
              apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                        (Qinv (q_fact (Datatypes.S (Datatypes.S m))))) _).
              ** apply (Qmult_le_compat_r (Qabs (q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m))))
                                          (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                          (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                  --- apply (QleT'_to_Qle _ _). apply (q_pow_diff_bound x y B (Datatypes.S m)); assumption.
                  --- apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                    apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos.
              ** (* (|x−y|·((S(S m))#1·B^{S m}))·/((S(S m))!) ≤ |x−y|·(B^{S m}·/((S m)!)) *)
                 setoid_replace (Qmult (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))))
                                       (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                   with (Qmult (Qabs (x - y)) (Qmult (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                     (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))).
                 2: ring.
                  apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                            (Qmult (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                   (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
                                            (Qmult (q_pow B (Datatypes.S m)) (Qinv (q_fact (Datatypes.S m))))).
                  --- split; [apply Qabs_nonneg | apply Qle_refl].
                  --- split.
                      ---- apply (Qmult_le_0_compat (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))
                                                    (Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
                           { apply (Qmult_le_0_compat (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m))).
                             - apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)). unfold Qlt; simpl; lia.
                              - apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact HB. }
                            { apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m))))). apply Qinv_lt_0_compat. apply (QltT_to_Qlt _ _). apply q_fact_pos. }
                      ---- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply (qeqT_imp_qeq _ _ (q_ratio_cancel_succ B (Datatypes.S m))).
      * (* 合并：|x−y|·(exp_series m B + B^{S m}/(S m)!) == |x−y|·exp_series (S m) B *)
        setoid_replace (Qplus (Qmult (Qabs (x - y)) (exp_series m B))
                              (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m)))))
          with (Qmult (Qabs (x - y)) (exp_series m B + q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m)))).
        2: ring.
        apply QleT'_to_Qle. apply qeq_le.
        apply qeq_imp_qeqT.
        change (exp_series (Datatypes.S m) B) with (exp_series m B + q_pow B (Datatypes.S m) * Qinv (q_fact (Datatypes.S m))).
        reflexivity.
Qed.

(* 11. 有界差分（≤ 版）：|y| ≤ B、m ≤ n ⟹ |ep_n y − ep_m y| ≤ (B^m/m!)·2 *)
Lemma exp_partial_diff_bound_le : forall (x B : Q) (m n : nat),
  QleT' 0 B -> QleT' (Qabs x) B ->
  (forall t : nat, NatLe m t -> QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)) ->
  (m <= n)%nat ->
  QleT' (Qabs (exp_partial n x - exp_partial m x)) ((q_pow B m / q_fact m) * (1 + 1)%Q).
Proof.
  intros x B m n HB Hx Hgeom Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (exp_tail_abs m n B) _).
  - apply (Qle_trans _ (exp_tail_abs m n (Qabs x)) _).
    + apply (Qle_trans _ (Qabs (exp_tail m n x)) _).
      * apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
        apply (Qabs_wd (exp_partial n x - exp_partial m x) (exp_tail m n x)).
        apply (qeqT_imp_qeq _ _ (exp_partial_diff_tail m n x Hmn)).
      * apply (QleT'_to_Qle _ _). apply exp_tail_abs_le.
    + apply (QleT'_to_Qle _ _). apply exp_tail_abs_mono; [apply Qle_to_QleT'; apply Qabs_nonneg | exact Hx].
  - apply (QleT'_to_Qle _ _). apply exp_tail_abs_geom2; assumption.
Qed.

(* 12. 一致柯西模：|y| ≤ B ⟹ ep_m y 与 ep_n y 的模统一（m,n ≥ N） *)
Lemma exp_partial_cauchy_bounded : forall (B : Q) (eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    forall y : Q, QleT' (Qabs y) B ->
      QltT (Qabs (exp_partial m y - exp_partial n y)) eps).
Proof.
  intros B eps HB Hep.
  destruct (q_arch_geom B) as [N0 HN0].
  set (C := (q_pow B N0 / q_fact N0) * (1 + 1)%Q).
  assert (HC : Qle 0 C) by (unfold C; apply (QleT'_to_Qle _ _); apply q_pow_fact2_nonneg; exact HB).
  destruct (arch_decay C eps (Qle_to_QleT' _ _ HC) Hep) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn y Hy.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  destruct (Nat.leb m n) eqn:Emn.
  - assert (Hmn : (m <= n)%nat) by (apply Nat.leb_le; exact Emn).
    assert (Hbound : Qle (Qabs (exp_partial n y - exp_partial m y))
                         ((q_pow B m / q_fact m) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound_le y B m n); try exact HB; try exact Hy.
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hmn. }
    assert (Hlt : Qlt ((q_pow B m / q_fact m) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch B N0 t m eps HB (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (exp_partial n y - exp_partial m y)) _).
  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite (Qabs_Qminus (exp_partial m y) (exp_partial n y)). reflexivity.
  + exact (Qle_lt_trans _ ((q_pow B m / q_fact m) * (1 + 1)%Q) _ Hbound Hlt).
  - assert (Hnm : (n <= m)%nat) by (apply Nat.leb_gt in Emn; lia).
    assert (Hbound : Qle (Qabs (exp_partial m y - exp_partial n y))
                         ((q_pow B n / q_fact n) * (1 + 1)%Q)).
    { apply (QleT'_to_Qle _ _). apply (exp_partial_diff_bound_le y B n m); try exact HB; try exact Hy.
      - intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia.
      - exact Hnm. }
    assert (Hlt : Qlt ((q_pow B n / q_fact n) * (1 + 1)%Q) eps).
    { apply (QltT_to_Qlt _ _). apply (exp_tail_arch B N0 t n eps HB (fun u Hu => HN0 u Hu) Hep Hdec). lia. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow B n / q_fact n) * (1 + 1)%Q) _ Hbound Hlt).
Qed.

(* 13. exp 级数一致界：0 ≤ B ⟹ ∃C ≥ 1, ∀n, exp_series n B ≤ C *)
Lemma exp_series_arch : forall (B : Q), QleT' 0 B ->
  sigT (fun C : Q => And (QleT' 1 C) (forall n : nat, QleT' (exp_series n B) C)).
Proof.
  intros B HB.
  destruct (q_arch_geom B) as [N0 HN0].
  set (C := exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q).
  exists C.
  split.
  - (* 1 ≤ C *)
    apply Qle_to_QleT'.
    unfold C.
    apply (Qle_trans _ (exp_series N0 B) _).
    + setoid_replace 1 with (exp_series 0 B).
      2: reflexivity.
      apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | lia].
    + apply (Qle_plus_nonneg_r (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
      apply (QleT'_to_Qle _ _). apply q_pow_fact2_nonneg. exact HB.
  - (* forall n, exp_series n B ≤ C *)
    intro n.
    apply Qle_to_QleT'.
    destruct (Nat.leb n N0) eqn:En.
    + apply Nat.leb_le in En.
      apply (Qle_trans _ (exp_series N0 B) _).
      * apply (QleT'_to_Qle _ _). apply exp_series_mono; [exact HB | exact En].
      * unfold C. apply (Qle_plus_nonneg_r (exp_series N0 B) ((q_pow B N0 / q_fact N0) * (1 + 1)%Q)).
        apply (QleT'_to_Qle _ _). apply q_pow_fact2_nonneg. exact HB.
    + apply Nat.leb_gt in En.
      apply (Qle_trans _ (exp_series N0 B + (q_pow B N0 / q_fact N0) * (1 + 1)%Q) _).
      * apply (Qle_trans _ (exp_series N0 B + exp_tail_abs N0 n B) _).
        -- (* exp_series n B ≤ exp_series N0 B + exp_tail_abs N0 n B ⟺ 差 ≤ 尾 *)
           apply Qle_minus_iff.
           setoid_replace (exp_series N0 B + exp_tail_abs N0 n B + - exp_series n B)
             with (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B)) by ring.
           setoid_replace (exp_tail_abs N0 n B - (exp_series n B - exp_series N0 B))
             with (exp_tail_abs N0 n B + - (exp_series n B - exp_series N0 B)) by ring.
           apply (proj1 (Qle_minus_iff (exp_series n B - exp_series N0 B) (exp_tail_abs N0 n B))).
            apply (QleT'_to_Qle _ _). apply (exp_series_tail_le B N0 n HB). lia.
        -- apply (Qplus_le_compat _ _ _ _); [apply Qle_refl | apply (QleT'_to_Qle _ _); apply (exp_tail_abs_geom2 B N0 n HB)].
           { intros u Hu. apply NatLe_drop in Hu. apply (HN0 u). apply NatLe_lift. lia. }
           { lia. }
      * unfold C. apply Qle_refl.
Qed.

(* ================= Real 层：exp 实例化 ================= *)

(* 14. Lipschitz 一般版（含 m = 0）：|x|,|y| ≤ B ⟹ |ep_m x − ep_m y| ≤ |x−y|·exp_series m B *)
Lemma exp_partial_lipschitz : forall (x y B : Q) (m : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (exp_partial m x - exp_partial m y))
      (Qmult (Qabs (x - y)) (exp_series m B)).
Proof.
  intros x y B m HB Hx Hy.
  apply Qle_to_QleT'.
  destruct m as [| m'].
  - (* m = 0：|1 − 1| = 0 ≤ |x−y|·1 *)
    assert (Hz : Qabs (exp_partial 0 x - exp_partial 0 y) == 0).
    { change (Qabs (1%Q - 1%Q) == 0). assert (Hm : 1%Q - 1%Q == 0) by reflexivity. rewrite Hm. reflexivity. }
    rewrite Hz.
    apply (Qmult_le_0_compat (Qabs (x - y)) 1).
    + apply Qabs_nonneg.
    + apply QleT'_to_Qle. apply Qle_0_1.
  - (* m = S m'：lipschitz_succ + mono（exp_series m' B ≤ exp_series (S m') B） *)
    apply (Qle_trans _ (Qmult (Qabs (x - y)) (exp_series m' B)) _).
    + apply (QleT'_to_Qle _ _). exact (exp_partial_lipschitz_succ x y B m' HB Hx Hy).
    + apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                    (exp_series m' B) (exp_series (Datatypes.S m') B)).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- assert (Hpos : Qlt 0 (exp_series m' B)).
           { apply (Qlt_le_trans _ 1 _); [reflexivity | (setoid_replace 1 with (exp_series 0 B) by reflexivity; apply (QleT'_to_Qle _ _); apply exp_series_mono; [exact HB | lia])]. }
           apply (Qlt_le_weak 0 (exp_series m' B)). exact Hpos.
        -- apply (QleT'_to_Qle _ _). apply exp_series_step_mono. exact HB.
Qed.

(* 15. real_exp 定义：exp 部分和对角序列（柯西性构造性证明，零 承认） *)
Definition cauchy_real_exp (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n : nat => exp_partial n (u n)).
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  (* exp_series_arch：Set 输入（qltT_leT' 弱化，无降级） *)
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  (* N1：Hu (eps/(2C))——正性 Set 链 *)
  destruct (Hu (eps / (2 * C))%Q) as [N1 HN1].
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  (* N2：exp_partial_cauchy_bounded（Set 输入） *)
  assert (Heps2 : QltT 0 (eps / 2)).
  { apply (qltT_div_pos eps 2). exact Heps. exact qltT_0_2. }
  destruct (exp_partial_cauchy_bounded M (eps / 2)%Q (qltT_leT' 0 M HMpos) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros m n Hm Hn.
  (* 分裂等式（ring）→ Set 目标左侧换形 *)
  apply (qltT_eq_compat_l (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                 (exp_partial m (u n) - exp_partial n (u n))))
                          (Qabs (exp_partial m (u m) - exp_partial n (u n)))
                          eps).
  - apply qeq_imp_qeqT. apply Qabs_wd. ring.
  - (* Set 链：三角 + 项1 ≤T |Δu|·C + 项2 <T eps/2，和 <T eps/2+eps/2 == eps *)
    assert (HtriT : QleT' (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                 (exp_partial m (u n) - exp_partial n (u n))))
                          (Qabs (exp_partial m (u m) - exp_partial m (u n)) +
                           Qabs (exp_partial m (u n) - exp_partial n (u n)))).
    { apply Qle_to_QleT'. apply Qabs_triangle. }
    assert (Ht1T : QleT' (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                         (Qabs (u m - u n) * C)).
    { apply (qleT'_trans (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                         (Qabs (u m - u n) * exp_series m M)
                         (Qabs (u m - u n) * C)).
      - apply (exp_partial_lipschitz (u m) (u n) M m (qltT_leT' 0 M HMpos) (HM m) (HM n)).
      - apply (qleT'_mult_compat_l (exp_series m M) C (Qabs (u m - u n))).
        + apply qabs_nonnegT.
        + apply HC. }
    assert (Ht2T : QltT (Qabs (exp_partial m (u n) - exp_partial n (u n))) (eps / 2)).
    { apply (HN2 m n).
      - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)].
      - apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)].
      - exact (HM n). }
    (* |Δu|·C <T eps/2：|Δu| <T eps/(2C) 且 C >T 0，乘后右换 == eps/2 *)
    assert (Ht3T : QltT (Qabs (u m - u n) * C) (eps / 2)).
    { apply (qltT_leT'_ltT (Qabs (u m - u n) * C) ((eps / (2 * C)) * C) (eps / 2)).
      - apply (qltT_mult_ltT_compat_r (Qabs (u m - u n)) (eps / (2 * C)) C).
        + exact HCposT.
        + apply (HN1 m n).
          * apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hm)].
          * apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _); [lia | exact (NatLe_drop _ _ Hn)].
      - apply qeq_leT'.
        assert (Hf : (eps / (2 * C)) * C == eps / 2).
        { field.
          intro Hz.
          exact (Qlt_not_eq 0 C (QltT_to_Qlt 0 C HCposT) (Qeq_sym C 0 Hz)). }
        apply qeq_imp_qeqT. exact Hf. }
    (* 结论：三角和 = 项1+项2 <T |Δu|·C+eps/2 <T eps/2+eps/2 ==T eps *)
    apply (qleT'_ltT_ltT (Qabs (exp_partial m (u m) - exp_partial m (u n) +
                                (exp_partial m (u n) - exp_partial n (u n))))
                         (Qabs (exp_partial m (u m) - exp_partial m (u n)) +
                          Qabs (exp_partial m (u n) - exp_partial n (u n)))
                         eps);
      [ exact HtriT
      | apply (qltT_leT'_ltT _ (eps / 2 + eps / 2) eps);
        [ apply (qltT_leT'_ltT _ (Qabs (u m - u n) * C + eps / 2) _);
          [ apply (qleT'_plus_ltT_ltT (Qabs (exp_partial m (u m) - exp_partial m (u n)))
                                      (Qabs (u m - u n) * C)
                                      (Qabs (exp_partial m (u n) - exp_partial n (u n)))
                                      (eps / 2));
            [ exact Ht1T | exact Ht2T ]
          | apply qltT_leT';
            apply (qltT_plus_leT'_ltT (Qabs (u m - u n) * C) (eps / 2) (eps / 2) (eps / 2));
            [ exact Ht3T | apply qleT'_refl ] ]
        | apply qeq_leT'; apply qeq_imp_qeqT;
          assert (Hf3 : eps / 2 + eps / 2 == eps) by field;
          exact Hf3 ] ].
Defined.

(* ===== B3：exp 字段 ===== *)

(* exp_partial 在 0 处恒为 1：ep_n 0 == 1（0^k = 0 for k ≥ 1） *)
Lemma exp_partial_zero : forall n,QeqT ( exp_partial n 0 ) ( 1).
Proof.
  intros.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH.
    assert (Hpow : q_pow 0 (Datatypes.S m) == 0).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ 0 m)). ring. }
    rewrite Hpow.
    unfold Qdiv.
    rewrite (Qmult_0_l (Qinv (q_fact (Datatypes.S m)))).
    ring.
Qed.

(* ===== cauchy_real_exp_pos：exp 部分和最终正性 ===== *)

(* 成对和：1 + Σ_{k=1}^{m} [(−a)^{2k−1}/(2k−1)! + (−a)^{2k}/(2k)!] *)
Fixpoint exp_pair_alt (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => exp_pair_alt m' a +
                      (q_pow (- a) (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) +
                       q_pow (- a) (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))
  end.

(* 偶次截断 == 成对和：exp_partial (2m) (-a) == exp_pair_alt m a *)
Lemma exp_even_pair : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) ) ( exp_pair_alt m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - simpl. reflexivity.
  - assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    simpl.
    setoid_rewrite IH.
    unfold Qdiv.
    ring.
Qed.

(* 偶次幂：(−a)^{2k} == a^{2k}（符号消失） *)
Lemma q_pow_neg_even : forall a k,QeqT ( q_pow (- a) (2 * k) ) ( q_pow a (2 * k)).
Proof.
  intros a k.
  apply qeq_imp_qeqT.
  induction k as [| k IH].
  - simpl. reflexivity.
  - assert (Hidx : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
    rewrite Hidx.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (- a) (Datatypes.S (2 * k)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ a (Datatypes.S (2 * k)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (- a) (2 * k))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ a (2 * k))).
    setoid_rewrite IH.
    ring.
Qed.

(* 奇次幂：(−a)^{2k+1} == −a^{2k+1} *)
Lemma q_pow_neg_odd : forall a k,QeqT (
  q_pow (- a) (Datatypes.S (2 * k)) ) ( - q_pow a (Datatypes.S (2 * k))).
Proof.
  intros a k.
  apply qeq_imp_qeqT.
  transitivity ((- a) * q_pow (- a) (2 * k)%nat).
  - apply (qeqT_imp_qeq _ _ (q_pow_succ (- a) (2 * k)%nat)).
  - transitivity ((- a) * q_pow a (2 * k)%nat).
    + setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a k)). reflexivity.
    + transitivity (- (a * q_pow a (2 * k)%nat)).
      * ring.
      * setoid_rewrite <- (qeqT_imp_qeq _ _ (q_pow_succ a (2 * k)%nat)). reflexivity.
Qed.

(* 成对项非负（正尾）：a ≥ 2k ⟹ (−a)^{2k−1}/(2k−1)! + (−a)^{2k}/(2k)! ≥ 0 *)
Lemma exp_pair_term_nonneg : forall (a : Q) (k : nat),
  QleT' 0 a -> QleT' (Z.of_nat (2 * Datatypes.S k) # 1) a ->
  QleT' 0 (q_pow (- a) (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)) +
         q_pow (- a) (Datatypes.S (Datatypes.S (2 * k))) / q_fact (Datatypes.S (Datatypes.S (2 * k)))).
Proof.
  intros a k Ha Hk.
  apply Qle_to_QleT'.
  (* 奇次负、偶次正（Qeq 侧换形，Qle 用 Qle_trans 桥） *)
  apply (Qle_trans _ (q_pow a (2 * Datatypes.S k) / q_fact (2 * Datatypes.S k) +
                     - (q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)))) _).
  - (* 0 ≤ C/D − (A/B) ⟺ A/B ≤ C/D（A := a^{2k+1}, B := (2k+1)!, C := a^{2k+2}, D := (2k+2)!） *)
    apply (proj1 (Qle_minus_iff (q_pow a (Datatypes.S (2 * k)) / q_fact (Datatypes.S (2 * k)))
                                (q_pow a (2 * Datatypes.S k) / q_fact (2 * Datatypes.S k)))).
    apply (QleT'_to_Qle _ _).
    apply (q_le_div_le (q_pow a (Datatypes.S (2 * k))) (q_fact (Datatypes.S (2 * k)))
                       (q_pow a (2 * Datatypes.S k)) (q_fact (2 * Datatypes.S k))).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + (* A·D ≤ C·B：D == (2·S k)#1·B、C == a·A，消去 A·B ≥ 0 后由 Hk *)
      apply Qle_to_QleT'.
      assert (Hidx : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
      rewrite Hidx.
      setoid_replace (q_pow a (Datatypes.S (Datatypes.S (2 * k))))
        with (a * q_pow a (Datatypes.S (2 * k))).
      2: { apply (qeqT_imp_qeq _ _ (q_pow_succ a (Datatypes.S (2 * k)))). }
      setoid_replace (q_fact (Datatypes.S (Datatypes.S (2 * k))))
        with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) * q_fact (Datatypes.S (2 * k))).
      2: { apply (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (2 * k)))). }
      setoid_replace (q_pow a (Datatypes.S (2 * k)) *
                      ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) * q_fact (Datatypes.S (2 * k))))
        with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
              (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      2: ring.
      setoid_replace (a * q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))
        with (a * (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      2: ring.
      apply (Qmult_le_compat_r (Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) a
                               (q_pow a (Datatypes.S (2 * k)) * q_fact (Datatypes.S (2 * k)))).
      * apply (Qle_trans _ (Z.of_nat (2 * Datatypes.S k) # 1) _).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. change ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) == (Z.of_nat (2 * Datatypes.S k) # 1)). unfold Qeq. simpl. lia.
        -- exact (QleT'_to_Qle _ _ Hk).
      * apply Qmult_le_0_compat.
        -- apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact Ha.
        -- apply (Qlt_le_weak 0 (q_fact (Datatypes.S (2 * k)))). apply (QltT_to_Qlt _ _). apply q_fact_pos.
  - (* 换形等价：P' == P（qeq_le） *)
    apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a k)).
    assert (Hidx2 : (2 * Datatypes.S k)%nat = Datatypes.S (Datatypes.S (2 * k))) by lia.
    rewrite <- Hidx2.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S k))).
    unfold Qdiv.
    ring.
Qed.

(* cauchy_real_exp 0 == 1：逐点相等（ep_n 0 == 1 == one 序列） *)
Lemma cauchy_real_exp_zero : real_eq (cauchy_real_exp real_zero) real_one.
Proof.
  intro eps. intro Heps.
  exists 0%nat.
  intros n Hn.
  simpl.
  (* 目标：QltT (Qabs (exp_partial n 0 - 1)) eps *)
  assert (H1 : exp_partial n 0 - 1 == 0).
  { rewrite (qeqT_imp_qeq _ _ (exp_partial_zero n)). ring. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
  - apply QleT'_to_Qle. apply qeq_le.
  apply qeq_imp_qeqT.
    apply (Qabs_wd (exp_partial n 0 - 1) 0). exact H1.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* 工程③ 阶段 B3：E/O 拆分 + corr 结构 + altf 交错和（probe_exp3 嵌入，备份 80） *)
(* 目标链：esq_eq_corr（E_m²−O_m² == 1 + corr m a）→ exp_even_neg_nonneg *)
(*        → exp_partial_tail_pos → cauchy_real_exp_pos（RealInterface exp_neg_pos 字段） *)
(* 零 承认 / 纯构造性 Set 层。 *)
Section QExpEOSplit.
#[export] Instance Qinv_comp_proper : Proper (Qeq ==> Qeq) Qinv := Qinv_comp.

(* 注册 q_pow 的 setoid 形态（q_pow_wd 是 Lemma 非 Instance） *)
#[export] Instance q_pow_comp_proper : Proper (Qeq ==> eq ==> Qeq) q_pow :=
  fun x y Hxy n m Hnm =>
    match Hnm with eq_refl =>
      qeqT_imp_qeq (q_pow x n) (q_pow y n) (q_pow_wd x y n (qeq_imp_qeqT x y Hxy)) end.

(* ============ 基础设施：E/O 拆分 ============ *)

(* 偶次部分：E_m(a) = Σ_{k=0}^{m} a^{2k}/(2k)! *)
Fixpoint e_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => e_sum m' a + q_pow a (2 * Datatypes.S m') / q_fact (2 * Datatypes.S m')
  end.

(* 奇次部分：O_m(a) = Σ_{k=0}^{m−1} a^{2k+1}/(2k+1)! *)
Fixpoint o_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 0%Q
  | Datatypes.S m' => o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))
  end.

(* E/O 递推 *)
Lemma e_sum_succ : forall (a : Q) (m : nat),QeqT (
  e_sum (Datatypes.S m) a ) ( e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma o_sum_succ : forall (a : Q) (m : nat),QeqT (
  o_sum (Datatypes.S m) a ) ( o_sum m a + q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 偶次截断 = E − O：S_{2m}(−a) == e_sum m a − o_sum m a *)
Lemma e_o_split_even : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) ) ( e_sum m a - o_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - reflexivity.
  - (* S_{2m+2}(−a) = S_{2m}(−a) + (−a)^{2m+1}/(2m+1)! + (−a)^{2m+2}/(2m+2)! *)
    assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (2 * m))) (- a) ==
            exp_partial (2 * m) (- a) +
            q_pow (- a) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) +
            q_pow (- a) (Datatypes.S (Datatypes.S (2 * m))) / q_fact (Datatypes.S (Datatypes.S (2 * m)))).
    { reflexivity. }
    rewrite Hstep.
    setoid_rewrite IH.
    (* 展开 e_sum/o_sum 侧：用 succ 引理保持 2·S m 字面形态，再 rewrite Hidx *)
    setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
    rewrite Hidx.
    (* 奇次幂符号：(−a)^{S(2m)} == −a^{S(2m)} *)
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd a m)).
    (* 偶次幂符号：(−a)^{S(S(2m))} == a^{S(S(2m))}：先把索引换回 2·S m 形态 *)
    rewrite <- Hidx.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even a (Datatypes.S m))).
    unfold Qdiv. ring.
Qed.

(* 偶次截断正参数 = E + O：S_{2m}(a) == e_sum m a + o_sum m a *)
Lemma e_o_split_pos : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) a ) ( e_sum m a + o_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH].
  - reflexivity.
  - assert (Hidx : (2 * Datatypes.S m)%nat = Datatypes.S (Datatypes.S (2 * m))) by lia.
    rewrite Hidx.
    assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (2 * m))) a ==
            exp_partial (2 * m) a +
            q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) +
            q_pow a (Datatypes.S (Datatypes.S (2 * m))) / q_fact (Datatypes.S (Datatypes.S (2 * m)))).
    { reflexivity. }
    rewrite Hstep.
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
    rewrite Hidx.
    unfold Qdiv. ring.
Qed.

(* ============ 核心：离散凸性/极值引理 ============ *)

(* 平方非负：0 ≤ x·x（Q 层 unfold 直证；n·n 非线性需 nia） *)
Lemma q_square_nonneg : forall x : Q, QleT' 0 (x * x).
Proof.
  intro x. apply Qle_to_QleT'. unfold Qle, Qmult. destruct x as [n d]. simpl. nia.
Qed.

(* 括号项（j ≥ 1）：brk2 k j a := 2·a^{2k+2j}·[1/((2k+1)!(2j−1)!) − 1/((2k+2)!(2j−2)!)] *)
Definition brk2 (k j : nat) (a : Q) : Q :=
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
  2 * q_pow a (2 * k + 2 * j) /
    (q_fact (2 * k + 2) * q_fact (2 * j - 2)).

(* 内和：inner2 k J a := Σ_{j=1}^{J} brk2 k j a *)
Fixpoint inner2 (k J : nat) (a : Q) : Q :=
  match J with
  | 0%nat => 0
  | Datatypes.S J' => inner2 k J' a + brk2 k (Datatypes.S J') a
  end.

(* kloop m k a := Σ_{k'=k}^{2m−1} inner2 k' (2m−k') a —— k 递减递归（J 依赖不变的外层 m） *)
Fixpoint kloop (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => if Nat.leb m k then inner2 k (2 * m - k) a + kloop m k' a else 0
  end.

(* 校正和：corr m a := kloop m (2m−1) a = Σ_{k=m}^{2m−1} Σ_{j=1}^{2m−k} brk2 k j a *)
Definition corr (m : nat) (a : Q) : Q := kloop m (2 * m - 1) a.

(* 结构：inner2 单步 *)
Lemma inner2_succ : forall (k J : nat) (a : Q),QeqT (
  inner2 k (Datatypes.S J) a ) ( inner2 k J a + brk2 k (Datatypes.S J) a).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 结构：kloop 单步（S k ≥ m 时加项；kloop 分支条件用外层 k = S k'） *)
Lemma kloop_succ : forall (m k : nat) (a : Q),
  (m <= Datatypes.S k)%nat ->QeqT (
  kloop m (Datatypes.S k) a ) ( inner2 (Datatypes.S k) (2 * m - Datatypes.S k) a + kloop m k a).
Proof.
  intros m k a Hmk. simpl.
  apply qeq_imp_qeqT.
  assert (Hleb : Nat.leb m (Datatypes.S k) = true)
    by (apply (proj2 (Nat.leb_le m (Datatypes.S k))); exact Hmk).
  rewrite Hleb. reflexivity.
Qed.

(* inv 反变保序：0<x、0<y、y≤x ⟹ inv x ≤ inv y（构造性：Qle_lt_or_eq 分情况） *)
Lemma q_inv_le_contravar : forall (x y : Q),
  QltT 0 x -> QltT 0 y -> QleT' y x -> QleT' (Qinv x) (Qinv y).
Proof.
  intros x y Hx Hy Hyx.
  apply Qle_to_QleT'.
  assert (Hx' : Qlt 0 x) by (apply QltT_to_Qlt; exact Hx).
  assert (Hy' : Qlt 0 y) by (apply QltT_to_Qlt; exact Hy).
  assert (Hyx' : Qle y x) by (apply QleT'_to_Qle; exact Hyx).
  destruct (Qle_lt_or_eq y x Hyx') as [Hlt | Heq].
  - exact (Qlt_le_weak (Qinv x) (Qinv y)
    (proj1 (Qinv_lt_contravar y x Hy' Hx') Hlt)).
  - exact (QleT'_to_Qle (Qinv x) (Qinv y) (qeq_le (Qinv x) (Qinv y)
    (qeq_imp_qeqT (Qinv x) (Qinv y)
    (Qeq_sym (Qinv y) (Qinv x) (Qinv_comp y x Heq))))).
Qed.

(* 阶乘对比较：1≤j、2j−1 ≤ 2k+2 ⟹ (2k+1)!(2j−1)! ≤ (2k+2)!(2j−2)! *)
Lemma q_fact_pair_le : forall (k j : nat), (1 <= j)%nat -> (2 * j <= 2 * k + 3)%nat ->
  QleT' (q_fact (2 * k + 1) * q_fact (2 * j - 1))
      (q_fact (2 * k + 2) * q_fact (2 * j - 2)).
Proof.
  intros k j Hj1 Hkj.
  apply Qle_to_QleT'.
  assert (Hidx1 : Datatypes.S (2 * k + 1) = (2 * k + 2)%nat) by lia.
  assert (Hidx2 : Datatypes.S (2 * j - 2) = (2 * j - 1)%nat) by lia.
  assert (Hf1 : q_fact (2 * k + 2) ==
          (Z.of_nat (2 * k + 2) # 1) * q_fact (2 * k + 1)).
  { rewrite <- Hidx1. apply (qeqT_imp_qeq _ _ (q_fact_succ (2 * k + 1))). }
  assert (Hf2 : q_fact (2 * j - 1) ==
          (Z.of_nat (2 * j - 1) # 1) * q_fact (2 * j - 2)).
  { rewrite <- Hidx2. apply (qeqT_imp_qeq _ _ (q_fact_succ (2 * j - 2))). }
  setoid_replace (q_fact (2 * k + 1) * q_fact (2 * j - 1)) with
    ((Z.of_nat (2 * j - 1) # 1) * (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  2: { setoid_rewrite Hf2. ring. }
  setoid_replace (q_fact (2 * k + 2) * q_fact (2 * j - 2)) with
    ((Z.of_nat (2 * k + 2) # 1) * (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  2: { setoid_rewrite Hf1. ring. }
  apply (Qmult_le_compat_r (Z.of_nat (2 * j - 1) # 1) (Z.of_nat (2 * k + 2) # 1)
                           (q_fact (2 * k + 1) * q_fact (2 * j - 2))).
  - unfold Qle. simpl. lia.
  - apply (Qmult_le_0_compat (q_fact (2 * k + 1)) (q_fact (2 * j - 2)));
      apply (Qlt_le_weak 0 (q_fact _)); apply (QltT_to_Qlt _ _); apply q_fact_pos.
Qed.

(* 括号项非负：0 ≤ a、1≤j、2j ≤ 2k+3 ⟹ 0 ≤ brk2 k j a *)
Lemma brk2_nonneg : forall (a : Q) (k j : nat),
  QleT' 0 a -> (1 <= j)%nat -> (2 * j <= 2 * k + 3)%nat -> QleT' 0 (brk2 k j a).
Proof.
  intros a k j Ha Hj1 Hkj.
  apply Qle_to_QleT'.
  unfold brk2.
  (* 拆成 2a^{2k+2j}·[1/((2k+1)!(2j−1)!) − 1/((2k+2)!(2j−2)!)]，括号 ≥ 0 *)
  apply (Qle_trans _ (2 * q_pow a (2 * k + 2 * j) *
      (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
       Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))) _).
  - (* 0 ≤ M：两因子非负 *)
    apply (Qmult_le_0_compat (2 * q_pow a (2 * k + 2 * j))
             (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1)) -
              Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))).
    + apply (Qmult_le_0_compat 2 (q_pow a (2 * k + 2 * j))).
      * apply (Qlt_le_weak 0 2). unfold Qlt; simpl; lia.
      * apply (QleT'_to_Qle _ _). apply q_pow_nonneg. exact Ha.
    + (* 括号：inv B − inv D ≥ 0 ⟺ inv D ≤ inv B（B ≤ D 反变保序） *)
      assert (HBD := q_fact_pair_le k j Hj1 Hkj).
      apply (proj1 (Qle_minus_iff (Qinv (q_fact (2 * k + 2) * q_fact (2 * j - 2)))
                                  (Qinv (q_fact (2 * k + 1) * q_fact (2 * j - 1))))).
      apply (QleT'_to_Qle _ _).
      apply (q_inv_le_contravar (q_fact (2 * k + 2) * q_fact (2 * j - 2))
                                (q_fact (2 * k + 1) * q_fact (2 * j - 1))).
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat (q_fact (2 * k + 2)) (q_fact (2 * j - 2)));
          apply QltT_to_Qlt; apply q_fact_pos.
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat (q_fact (2 * k + 1)) (q_fact (2 * j - 1)));
          apply QltT_to_Qlt; apply q_fact_pos.
      * exact HBD.
  - (* M ≤ brk2：换形等价（unfold Qdiv 后 ring） *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* 内和非负：0 ≤ a、2J ≤ 2k+3 ⟹ 0 ≤ inner2 k J a *)
Lemma inner2_nonneg : forall (a : Q) (k J : nat),
  QleT' 0 a -> (2 * J <= 2 * k + 3)%nat -> QleT' 0 (inner2 k J a).
Proof.
  intros a k J Ha HJ.
  apply Qle_to_QleT'.
  induction J as [| J IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (inner2 k J a) _).
    + apply IH. lia.
    + apply (Qle_plus_nonneg_r (inner2 k J a) (brk2 k (Datatypes.S J) a)).
      apply (QleT'_to_Qle _ _). apply brk2_nonneg; try exact Ha.
      * lia.  (* 1 ≤ S J *)
      * assert (Hj : (2 * Datatypes.S J <= 2 * k + 3)%nat) by lia.
        exact Hj.
Qed.

(* kloop 无条件非负：0 ≤ a ⟹ 0 ≤ kloop m k a（k < m 的项为 0，k ≥ m 的项非负） *)
Lemma kloop_nonneg : forall (a : Q) (m k : nat), QleT' 0 a -> QleT' 0 (kloop m k a).
Proof.
  intros a m k Ha.
  apply Qle_to_QleT'.
  induction k as [| k' IH]; simpl.
  - apply Qle_refl.
  - destruct (Nat.leb m (Datatypes.S k')) eqn:E.
    + apply (Qle_trans _ (kloop m k' a) _).
      * exact IH.
      * setoid_replace (inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a + kloop m k' a)
          with (kloop m k' a + inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a) by ring.
        apply (Qle_plus_nonneg_r (kloop m k' a) (inner2 (Datatypes.S k') (2 * m - Datatypes.S k') a)).
        apply (QleT'_to_Qle _ _). apply inner2_nonneg; try exact Ha.
        apply Nat.leb_le in E.
        (* 2(2m − S k') ≤ 2(S k')+3 ⟸ S k' ≥ m *)
        assert (Hmid : (2 * (2 * m - Datatypes.S k') <= 2 * Datatypes.S k' + 3)%nat) by lia.
        exact Hmid.
    + apply Qle_refl.
Qed.

(* 校正和非负：0 ≤ a ⟹ 0 ≤ corr m a *)
Lemma corr_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (corr m a).
Proof.
  intros a m Ha. unfold corr. exact (kloop_nonneg a m (2 * m - 1) Ha).
Qed.

(* ============ 主恒等式：E_m² − O_m² == 1 + corr m a（核心） ============ *)

(* 交错阶乘和：altf N := Σ_{u=0}^{N} (−1)^u/(u!(N−u)!) —— (1−1)^N 展开的系数 *)
Fixpoint altf_aux (N u : nat) : Q :=
  match u with
  | 0%nat => Qinv (q_fact N)
  | Datatypes.S u' => altf_aux N u' +
      q_pow (-1) (Datatypes.S u') / (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u'))
  end.
Definition altf (N : nat) : Q := altf_aux N N.

(* 阶乘前驱：1≤u ⟹ u! == u#1·(u−1)! *)
Lemma q_fact_pred : forall u, (1 <= u)%nat ->QeqT (
  q_fact u ) ( (Z.of_nat u # 1) * q_fact (u - 1)).
Proof.
  intros u Hu.
  apply qeq_imp_qeqT.
  destruct u as [| u']; [lia | ].
  replace (Datatypes.S u' - 1)%nat with u' by lia.
  apply (qeqT_imp_qeq _ _ (q_fact_succ u')).
Qed.

(* altf 的 Pascal 型分解引理：u ≥ 1、u ≤ N−1 时
   N/(u!(N−u)!) == 1/((u−1)!(N−u)!) + 1/(u!(N−u−1)!) *)
Lemma pascal_split : forall (N u : nat),
  (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact u * q_fact (N - u)) ) (
  Qinv (q_fact (u - 1) * q_fact (N - u)) + Qinv (q_fact u * q_fact (N - u - 1))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  assert (Hf1 : q_fact u == (Z.of_nat u # 1) * q_fact (u - 1)) by (apply qeqT_imp_qeq; apply q_fact_pred; exact Hu1).
  assert (HNu : (1 <= N - u)%nat) by lia.
  assert (Hf2 : q_fact (N - u) == (Z.of_nat (N - u) # 1) * q_fact (N - u - 1))
    by (apply qeqT_imp_qeq; apply q_fact_pred; exact HNu).
  assert (Hsum : (Z.of_nat N # 1) == (Z.of_nat u # 1) + (Z.of_nat (N - u) # 1)).
  { unfold Qeq. simpl. lia. }
  assert (Hn1 : ~ (Z.of_nat u # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat u # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn2 : ~ (Z.of_nat (N - u) # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat (N - u) # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn3 : ~ q_fact (u - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (u - 1)) (qeq_imp_qeqT _ _ Hz0))).
  assert (Hn4 : ~ q_fact (N - u - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (N - u - 1)) (qeq_imp_qeqT _ _ Hz0))).
  (* 换形（Qinv_comp_proper 已注册，可进 Qinv） *)
  setoid_rewrite Hf1.
  setoid_rewrite Hf2.
  (* Qinv 乘积展开（原始形态模式，# 需括号） *)
  setoid_rewrite (Qinv_mult_distr ((Z.of_nat u # 1) * q_fact (u - 1))
                                  ((Z.of_nat (N - u) # 1) * q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat u # 1) (q_fact (u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (N - u) # 1) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (q_fact (u - 1))
                                  ((Z.of_nat (N - u) # 1) * q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (N - u) # 1) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr ((Z.of_nat u # 1) * q_fact (u - 1)) (q_fact (N - u - 1))).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat u # 1) (q_fact (u - 1))).
  (* N == A+B；原子化后 field 收尾（field 认 Qinv，非零给 HnA/HnB） *)
  setoid_replace (Z.of_nat N # 1) with ((Z.of_nat u # 1) + (Z.of_nat (N - u) # 1))
    by exact Hsum.
  set (A := Z.of_nat u # 1).
  set (B := Z.of_nat (N - u) # 1).
  set (I3 := Qinv (q_fact (u - 1))).
  set (I4 := Qinv (q_fact (N - u - 1))).
  assert (HnA : ~ A == 0) by (unfold A; exact Hn1).
  assert (HnB : ~ B == 0) by (unfold B; exact Hn2).
  field.
  split; [exact HnA | exact HnB].
Qed.

(* 交错和为零：N ≥ 1 ⟹ Σ_{u=0}^{N} (−1)^u/(u!(N−u)!) == 0（Pascal 归纳）
   证明路线（下轮）：altf_scal（(N#1)·altf N == 0）——逐项 pascal_split_mul +
   重排（第一和 = −altf_aux (N−1) (N−1)、第二和 = altf_aux (N−1) (N−1) − 1/(N−1)!）
   + 边界项（u=0 的 N#1/N! 与第二和边界 1/(N−1)!、u=N 的 (−1)^N/(N−1)!、符号相消
   (−1)^{N−1}+(−1)^N=0）抵消；再用 Qmult_integral（N#1·altf N == 0 且 N#1≠0）收尾。
   骨架见判例卡。 *)

(* pascal_split 两边乘 c 的版本（altf 逐项分解用） *)
Lemma pascal_split_mul : forall (N u : nat) (c : Q),
  (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  c * ((Z.of_nat N # 1) * Qinv (q_fact u * q_fact (N - u))) ) (
  c * (Qinv (q_fact (u - 1) * q_fact (N - u)) + Qinv (q_fact u * q_fact (N - u - 1)))).
Proof.
  intros N u c Hu1 HuN.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (pascal_split N u Hu1 HuN)).
  ring.
Qed.

(* 相邻符号相消：(−1)^N + (−1)^{S N} == 0 *)
Lemma q_pow_neg_alt : forall N,QeqT ( q_pow (-1) N + q_pow (-1) (Datatypes.S N) ) ( 0).
Proof.
  intro N.
  apply qeq_imp_qeqT.
  induction N as [| N IH].
  - simpl. ring.
  - simpl.
    setoid_replace ((-1) * q_pow (-1) N + (-1) * q_pow (-1) (Datatypes.S N))
      with ((q_pow (-1) N + q_pow (-1) (Datatypes.S N)) * (-1)) by ring.
    setoid_rewrite IH.
    ring.
Qed.

(* N#1/N! == 1/(N−1)!（q_fact_pred 约分） *)
Lemma q_fact_div_pred : forall N, (1 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact N) ) ( Qinv (q_fact (N - 1))).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  assert (Hf := qeqT_imp_qeq _ _ (q_fact_pred N HN)).
  assert (Hn : ~ (Z.of_nat N # 1) == 0) by (intro Hz0; assert (Hlt0 : QltT 0 (Z.of_nat N # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia); destruct (q_neq_of_lt _ Hlt0 (qeq_imp_qeqT _ _ Hz0))).
  assert (Hfq : ~ q_fact (N - 1) == 0) by (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos (N - 1)) (qeq_imp_qeqT _ _ Hz0))).
  setoid_rewrite Hf.
  setoid_rewrite (Qinv_mult_distr (Z.of_nat N # 1) (q_fact (N - 1))).
  set (A := Z.of_nat N # 1).
  set (I := Qinv (q_fact (N - 1))).
  assert (HnA : ~ A == 0) by (unfold A; exact Hn).
  field.
  exact HnA.
Qed.

(* 第一和：s1 N u := Σ_{u'=1}^{u} (−1)^{u'}·Qinv(q_fact (u'−1)·q_fact (N−u')) *)
Fixpoint s1 (N u : nat) : Q :=
  match u with
  | 0%nat => 0
  | Datatypes.S u' => s1 N u' +
      q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u' - 1) * q_fact (N - Datatypes.S u'))
  end.

(* 第二和：s2 N u := Σ_{u'=1}^{u} (−1)^{u'}·Qinv(q_fact u'·q_fact (N−u'−1)) *)
Fixpoint s2 (N u : nat) : Q :=
  match u with
  | 0%nat => 0
  | Datatypes.S u' => s2 N u' +
      q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u' - 1))
  end.

(* altf_aux 递推：u ≤ N−1 ⟹ altf_aux N (S u) == altf_aux N u + 项 *)
Lemma altf_aux_succ : forall N u,QeqT (
  altf_aux N (Datatypes.S u) ) ( altf_aux N u +
  q_pow (-1) (Datatypes.S u) * Qinv (q_fact (Datatypes.S u) * q_fact (N - Datatypes.S u))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 第一和重排：1 ≤ u ≤ N ⟹ s1 N u == −altf_aux (N−1) (u−1) *)
Lemma s1_eq : forall N u, (1 <= u)%nat -> (u <= N)%nat ->QeqT (
  s1 N u ) ( - altf_aux (N - 1) (u - 1)).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 与 Hu1 矛盾 *)
  - destruct u' as [| u''].
    + (* u = 1：s1 N 1 == −altf_aux (N−1) 0 *)
      simpl.
      setoid_rewrite (Qmult_1_l (q_fact (N - 1))).
      set (I := Qinv (q_fact (N - 1))).
      ring.
    + (* u = S (S u'')：递推 *)
      assert (Hidx1 : (Datatypes.S (Datatypes.S u'') - 1)%nat = Datatypes.S u'') by lia.
      assert (Hidx2 : (N - Datatypes.S (Datatypes.S u'') = (N - 1) - Datatypes.S u'')%nat) by lia.
      assert (Hs1 : s1 N (Datatypes.S (Datatypes.S u'')) ==
              s1 N (Datatypes.S u'') +
              q_pow (-1) (Datatypes.S (Datatypes.S u'')) *
                Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      { reflexivity. }
      rewrite Hs1.
      rewrite Hidx1.
      rewrite Hidx2.
      assert (IHu' : s1 N (Datatypes.S u'') == - altf_aux (N - 1) (Datatypes.S u'' - 1)).
      { apply IHu; lia. }
      setoid_rewrite IHu'.
      assert (Haux := qeqT_imp_qeq _ _ (altf_aux_succ (N - 1)%nat u'')).
      setoid_rewrite Haux.
      assert (Hidx3 : (Datatypes.S u'' - 1)%nat = u'') by lia.
      rewrite Hidx3.
      setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (Datatypes.S u''))).
      set (J := Qinv (q_fact (Datatypes.S u'') * q_fact ((N - 1) - Datatypes.S u''))).
      set (K := altf_aux (N - 1) u'').
      ring.
Qed.
(* 第二和重排：1 ≤ u ≤ N−1 ⟹ s2 N u == altf_aux (N−1) u − Qinv (q_fact (N−1)) *)
Lemma s2_eq : forall N u, (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  s2 N u ) ( altf_aux (N - 1) u - Qinv (q_fact (N - 1))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 与 Hu1 矛盾 *)
  - destruct u' as [| u''].
    + (* u = 1 *)
      simpl.
      assert (Hn2 : ((N - 1) - 1 = N - 2)%nat) by lia.
      rewrite Hn2.
      field.
      split; intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
    + (* u = S (S u'')：递推 *)
      assert (Hidx2 : (N - Datatypes.S (Datatypes.S u'') - 1 = (N - 1) - Datatypes.S (Datatypes.S u''))%nat) by lia.
      assert (Hs2 : s2 N (Datatypes.S (Datatypes.S u'')) ==
              s2 N (Datatypes.S u'') +
              q_pow (-1) (Datatypes.S (Datatypes.S u'')) *
                Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      { reflexivity. }
      rewrite Hs2.
      rewrite Hidx2.
      assert (IHu' : s2 N (Datatypes.S u'') == altf_aux (N - 1) (Datatypes.S u'') - Qinv (q_fact (N - 1))).
      { apply IHu; lia. }
      setoid_rewrite IHu'.
      assert (Haux := qeqT_imp_qeq _ _ (altf_aux_succ (N - 1)%nat (Datatypes.S u''))).
      setoid_rewrite Haux.
      set (I2 := Qinv (q_fact (N - 1))).
      set (K := altf_aux (N - 1) (Datatypes.S u'')).
      set (J := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact ((N - 1) - Datatypes.S (Datatypes.S u'')))).
      ring.
Qed.

(* pascal_split 特例 u=1（归一形态：q_fact 0 → 1、q_fact 1 → 1、N−1−1 → N−2；需 N ≥ 2） *)
Lemma pascal_split_one : forall N, (2 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * Qinv (q_fact 1 * q_fact (N - 1)) ) (
  Qinv (1 * q_fact (N - 1)) + Qinv (1 * q_fact (N - 2))).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  assert (Hps := qeqT_imp_qeq _ _ (pascal_split N 1 ltac:(lia) ltac:(lia))).
  assert (Hf12 : (N - 1 - 1 = N - 2)%nat) by lia.
  setoid_replace (Qinv (1 * q_fact (N - 2))) with (Qinv (1 * q_fact (N - 1 - 1))).
  2: { rewrite <- Hf12. reflexivity. }
  exact Hps.
Qed.

(* (N#1)·altf_aux N u 的逐项分解：1 ≤ u ≤ N−1 ⟹
   (N#1)·altf_aux N u == (N#1)·Qinv(q_fact N) + s1 N u + s2 N u *)
Lemma altf_scal_aux : forall N u, (1 <= u)%nat -> (u <= N - 1)%nat ->QeqT (
  (Z.of_nat N # 1) * altf_aux N u ) (
  (Z.of_nat N # 1) * Qinv (q_fact N) + s1 N u + s2 N u).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  induction u as [| u' IHu].
  - lia.  (* u = 0 与 Hu1 矛盾 *)
  - destruct u' as [| u''].
    + (* u = 1 *)
      simpl (altf_aux N 1).
      assert (Hps1 := qeqT_imp_qeq _ _ (pascal_split_one N ltac:(lia))).
      assert (Hs1' : s1 N 1 == q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1))).
      { change (0 + q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1)) ==
                q_pow (-1) 1 * Qinv (q_fact (1 - 1) * q_fact (N - 1))).
        set (I := Qinv (q_fact (1 - 1) * q_fact (N - 1))).
        ring. }
      assert (Hs2' : s2 N 1 == q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1))).
      { change (0 + q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1)) ==
                q_pow (-1) 1 * Qinv (q_fact 1 * q_fact (N - 1 - 1))).
        set (I := Qinv (q_fact 1 * q_fact (N - 1 - 1))).
        ring. }
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      setoid_replace (q_pow (-1) 1) with (-1) by reflexivity.
      assert (Hf11 : (1 - 1 = 0)%nat) by lia.
      assert (Hf12 : (N - 1 - 1 = N - 2)%nat) by lia.
      rewrite Hf11. rewrite Hf12.
      assert (Hq0 : q_fact 0 == 1) by reflexivity.
      setoid_rewrite Hq0.
      setoid_replace ((Z.of_nat N # 1) * (Qinv (q_fact N) + (-1) * Qinv (q_fact 1 * q_fact (N - 1))))
        with ((Z.of_nat N # 1) * Qinv (q_fact N) + (-1) * ((Z.of_nat N # 1) * Qinv (q_fact 1 * q_fact (N - 1)))).
      2: { set (A := Z.of_nat N # 1). set (I0 := Qinv (q_fact N)). set (I1 := Qinv (q_fact 1 * q_fact (N - 1))). ring. }
      setoid_rewrite Hps1.
      set (A := Z.of_nat N # 1).
      set (I0 := Qinv (q_fact N)).
      set (I1 := Qinv (1 * q_fact (N - 1))).
      set (I2 := Qinv (1 * q_fact (N - 2))).
      ring.
    + (* u = S (S u'')：递推 *)
      assert (Hsucc := qeqT_imp_qeq _ _ (altf_aux_succ N (Datatypes.S u''))).
      setoid_rewrite Hsucc.
      assert (Hps := qeqT_imp_qeq _ _ (pascal_split_mul N (Datatypes.S (Datatypes.S u'')) (q_pow (-1) (Datatypes.S (Datatypes.S u''))) ltac:(lia) ltac:(lia))).
      setoid_replace ((Z.of_nat N # 1) * (altf_aux N (Datatypes.S u'') +
          q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))))
        with ((Z.of_nat N # 1) * altf_aux N (Datatypes.S u'') +
             q_pow (-1) (Datatypes.S (Datatypes.S u'')) * ((Z.of_nat N # 1) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u''))))).
      2: { set (I3 := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))). ring. }
      setoid_rewrite Hps.
      setoid_rewrite (IHu ltac:(lia) ltac:(lia)).
      assert (Hs1' : s1 N (Datatypes.S (Datatypes.S u'')) ==
              s1 N (Datatypes.S u'') + q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      { reflexivity. }
      assert (Hs2' : s2 N (Datatypes.S (Datatypes.S u'')) ==
              s2 N (Datatypes.S u'') + q_pow (-1) (Datatypes.S (Datatypes.S u'')) * Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      { reflexivity. }
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      set (I0 := Qinv (q_fact N)).
      set (J := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      set (K := Qinv (q_fact (Datatypes.S (Datatypes.S u'') - 1) * q_fact (N - Datatypes.S (Datatypes.S u'')))).
      set (L := Qinv (q_fact (Datatypes.S (Datatypes.S u'')) * q_fact (N - Datatypes.S (Datatypes.S u'') - 1))).
      ring.
Qed.

(* altf_aux 差分：1 ≤ u ≤ N ⟹ altf_aux N u == altf_aux N (u−1) + (−1)^u·Qinv(q_fact u·q_fact (N−u)) *)
Lemma altf_aux_diff : forall N u, (1 <= u)%nat -> (u <= N)%nat ->QeqT (
  altf_aux N u ) ( altf_aux N (u - 1) + q_pow (-1) u * Qinv (q_fact u * q_fact (N - u))).
Proof.
  intros N u Hu1 HuN.
  apply qeq_imp_qeqT.
  destruct u as [| u']; [lia | ].
  change (altf_aux N u' + q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u')) ==
          altf_aux N (Datatypes.S u' - 1) + q_pow (-1) (Datatypes.S u') * Qinv (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u'))).
  assert (Hsu : (Datatypes.S u' - 1 = u')%nat) by lia.
  rewrite Hsu.
  reflexivity.
Qed.

(* (N#1)·altf N == 0：N ≥ 1（Pascal 分解 + 重排 + 边界抵消） *)
Lemma altf_scal : forall N, (1 <= N)%nat ->QeqT (
  (Z.of_nat N # 1) * altf N ) ( 0).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  unfold altf.
  destruct N as [| N'].
  - lia.
  - destruct N' as [| N''].
    + (* N = 1：直接算 *)
      simpl. field.
      all: try (intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0))).
      all: try (match goal with |- ~ (?X == 0) =>
                  intro Hz0;
                  assert (Hlt0 : QltT 0 X) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia);
                  destruct (q_neq_of_lt X Hlt0 (qeq_imp_qeqT _ _ Hz0)) end).
    + (* N = S (S N'')：组装（destruct 后 N 失效，set 恢复） *)
      set (N := Datatypes.S (Datatypes.S N'')).
      (* altf_aux N N == altf_aux N (N−1) + (−1)^N·Qinv(q_fact N·q_fact (N−N)) *)
      assert (Hstep : altf_aux N N == altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))).
      { change (altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N)) ==
                altf_aux N (N - 1) + q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))).
        reflexivity. }
      setoid_rewrite Hstep.
      (* (N#1)·(altf_aux N (N−1) + 尾项) 分配 *)
      setoid_replace ((Z.of_nat N # 1) * (altf_aux N (N - 1) +
          q_pow (-1) N * Qinv (q_fact N * q_fact (N - N))))
        with ((Z.of_nat N # 1) * altf_aux N (N - 1) +
             (Z.of_nat N # 1) * (q_pow (-1) N * Qinv (q_fact N * q_fact (N - N)))) by ring.
      assert (Hdec := qeqT_imp_qeq _ _ (altf_scal_aux N (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_rewrite Hdec.
      (* 中间和 = s1 N (N−1) + s2 N (N−1)——用 s1_eq/s2_eq 重排 *)
      assert (Hs1' := qeqT_imp_qeq _ _ (s1_eq N (N - 1)%nat ltac:(lia) ltac:(lia))).
      assert (Hs2' := qeqT_imp_qeq _ _ (s2_eq N (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_rewrite Hs1'. setoid_rewrite Hs2'.
      (* (N#1)·Qinv(q_fact N) == Qinv(q_fact (N−1)) *)
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_div_pred N HN)).
      (* 尾项：(N#1)·((−1)^N·Qinv(q_fact N·q_fact (N−N)))——N−N = 0 *)
      assert (Hnn : (N - N = 0)%nat) by lia.
      rewrite Hnn.
      (* (N#1)·((−1)^N·Qinv(q_fact N·q_fact 0)) == (−1)^N·Qinv(q_fact (N−1))（q_fact_div_pred + q_fact 0） *)
      setoid_replace ((Z.of_nat N # 1) * (q_pow (-1) N * Qinv (q_fact N * q_fact 0)))
        with (q_pow (-1) N * ((Z.of_nat N # 1) * Qinv (q_fact N * q_fact 0))) by ring.
      assert (Hq0 : q_fact 0 == 1) by reflexivity.
      setoid_rewrite Hq0.
      setoid_rewrite (Qmult_1_r (q_fact N)).
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_div_pred N HN)).
      (* altf_aux (N−1) (N−1) 差分展开（altf_aux_diff，N−1 形态统一） *)
      assert (Hdiff := qeqT_imp_qeq _ _ (altf_aux_diff (N - 1)%nat (N - 1)%nat ltac:(lia) ltac:(lia))).
      setoid_replace (altf_aux (N - 1) (N - 1)) with
        (altf_aux (N - 1) (N - 1 - 1) + q_pow (-1) (N - 1) * Qinv (q_fact (N - 1) * q_fact (N - 1 - (N - 1)))) by exact Hdiff.
      assert (Hnn2 : ((N - 1) - (N - 1) = 0)%nat) by lia.
      rewrite Hnn2.
      setoid_rewrite Hq0.
      setoid_rewrite (Qmult_1_r (q_fact (N - 1))).
      (* 符号相消：(q_pow (−1) (N−1) + q_pow (−1) N)·I == 0 *)
      set (I := Qinv (q_fact (N - 1))).
      assert (Hneg : (q_pow (-1) (N - 1) + q_pow (-1) N) * I == 0).
      { assert (Hsucc : (N = Datatypes.S (N - 1))%nat) by lia.
        (* 只精确换 q_pow (-1) N 的索引形态，勿全局 rewrite（会把 N-1 内 N 也替换） *)
        setoid_replace (q_pow (-1) N) with (q_pow (-1) (Datatypes.S (N - 1))) by
          (apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) N (Datatypes.S (N - 1)) Hsucc)).
        setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_alt (N - 1))).
        ring. }
      transitivity ((q_pow (-1) (N - 1) + q_pow (-1) N) * I).
      * ring.
      * exact Hneg.
Qed.
Lemma altf_zero : forall N, (1 <= N)%nat ->QeqT ( altf N ) ( 0).
Proof.
  intros N HN.
  apply qeq_imp_qeqT.
  (* 用 (N#1)·altf N == 0 且 N#1 ≠ 0 *)
  assert (Hmul := qeqT_imp_qeq _ _ (altf_scal N HN)).
  destruct (Qmult_integral (Z.of_nat N # 1) (altf N) Hmul) as [Hz | Ha].
  - exfalso.
    assert (Hlt0 : QltT 0 (Z.of_nat N # 1)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
    destruct (q_neq_of_lt (Z.of_nat N # 1) Hlt0 (qeq_imp_qeqT _ _ Hz)).
  - exact Ha.
Qed.

Lemma esq_succ : forall (a : Q) (m : nat),QeqT (
  e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
  o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a ) (
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a) +
  (2 * e_sum m a * (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) +
   (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
   (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) -
   2 * o_sum m a * (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) -
   (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))) *
   (q_pow a (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))))).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m)).
  unfold Qdiv. ring.
Qed.

(* corr 单步：corr (S m) == corr m + Δ'（Δ' 与 esq_succ 的增量一致 —— 下轮系数匹配） *)

(* ============ 路线 A：双和展开（esq_sum/osq_sum） ============ *)

(* q_pow 指数加法：q_pow x (m+n) == q_pow x m · q_pow x n *)

(* 偶双和行：esq_row N i a := Σ_{j=0}^{i} a^{2N+2j}/((2N)!(2j)!)（固定行 N，列 j 到 i） *)
Fixpoint esq_row (N i : nat) (a : Q) : Q :=
  match i with
  | 0%nat => q_pow a (2 * N) / (q_fact (2 * N) * q_fact 0)
  | Datatypes.S i' => esq_row N i' a +
      q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i'))
  end.

(* 偶双和：esq_sum m a := Σ_{i=0}^{m} Σ_{j=0}^{m} a^{2i+2j}/((2i)!(2j)!) *)
Fixpoint esq_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 1%Q
  | Datatypes.S m' => esq_sum m' a +
      2 * esq_row (Datatypes.S m') m' a +
      q_pow a (2 * Datatypes.S m' + 2 * Datatypes.S m') /
        (q_fact (2 * Datatypes.S m') * q_fact (2 * Datatypes.S m'))
  end.

(* 奇双和行：osq_row N i a := Σ_{j=0}^{i} a^{2N+2j+2}/((2N+1)!(2j+1)!) *)
Fixpoint osq_row (N i : nat) (a : Q) : Q :=
  match i with
  | 0%nat => q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)
  | Datatypes.S i' => osq_row N i' a +
      q_pow a (2 * N + 2 * Datatypes.S i' + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i' + 1))
  end.

(* 奇双和：osq_sum m a := Σ_{i=0}^{m-1} Σ_{j=0}^{m-1} a^{2i+2j+2}/((2i+1)!(2j+1)!) *)
Fixpoint osq_sum (m : nat) (a : Q) : Q :=
  match m with
  | 0%nat => 0%Q
  | Datatypes.S m' => osq_sum m' a +
      (* 新增行/列（i=m' 或 j=m'，对称）== 2·osq_row m' m' − 对角（对角重复计一次） *)
      2 * osq_row m' m' a -
      q_pow a (2 * m' + 2 * m' + 2) / (q_fact (2 * m' + 1) * q_fact (2 * m' + 1))
  end.

(* 部分和乘单项 == 行求和：E_m(a)·a^{2N}/(2N)! == esq_row N m a *)
Lemma e_mul_term : forall (a : Q) (m N : nat),QeqT (
  e_sum m a * (q_pow a (2 * N) / q_fact (2 * N)) ) ( esq_row N m a).
Proof.
  intros a m N.
  apply qeq_imp_qeqT.
  induction m as [| m IH]; simpl.
  - (* m=0：E_0=1 ⟹ 1·T == esq_row N 0 = T *)
    field.
    all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
  - (* simpl 已展开 e_sum (S m) 与 esq_row N (S m)，直接换形 *)
    setoid_replace ((e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (q_pow a (2 * N) / q_fact (2 * N)))
      with (e_sum m a * (q_pow a (2 * N) / q_fact (2 * N)) +
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) * (q_pow a (2 * N) / q_fact (2 * N))) by ring.
    setoid_rewrite IH.
    (* 尾项恒等：q_pow 乘积累积（Hmul）+ Qinv 分母展开，transitivity 分步 *)
    assert (Hmul : q_pow a (2 * Datatypes.S m) * q_pow a (2 * N) == q_pow a (2 * N + 2 * Datatypes.S m)).
    { assert (Hc : (2 * Datatypes.S m + 2 * N = 2 * N + 2 * Datatypes.S m)%nat) by lia.
      apply Qeq_sym.
      rewrite <- Hc.
      apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m) (2 * N)). }
    setoid_replace (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m) *
        (q_pow a (2 * N) / q_fact (2 * N)))
      with (q_pow a (2 * N + 2 * Datatypes.S m) / (q_fact (2 * N) * q_fact (2 * Datatypes.S m))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (2 * Datatypes.S m) * q_pow a (2 * N)) *
                       (Qinv (q_fact (2 * Datatypes.S m)) * Qinv (q_fact (2 * N)))).
         - ring.
         - setoid_replace (q_pow a (2 * Datatypes.S m) * q_pow a (2 * N))
             with (q_pow a (2 * N + 2 * Datatypes.S m)) by exact Hmul.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * N)) (q_fact (2 * Datatypes.S m))).
           ring. }
    (* 主目标两侧定义性相同（simpl 展开形态 vs 字面形态）——reflexivity 收尾 *)
    reflexivity.
Qed.

(* 偶次部分和平方 == 偶双和：E_m² == esq_sum m a *)
Lemma e_sq_expand : forall (a : Q) (m : nat),QeqT (
  e_sum m a * e_sum m a ) ( esq_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m IH]; simpl.
  - ring.
  - setoid_rewrite (qeqT_imp_qeq _ _ (e_sum_succ a m)).
    (* (E_m + t)² == esq_sum m + 2·esq_row (S m) m + diag *)
    setoid_replace ((e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (e_sum m a + q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)))
      with (e_sum m a * e_sum m a +
            2 * (e_sum m a * (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m))) +
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
            (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m))) by ring.
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (e_mul_term a m (Datatypes.S m))).
    (* 对角项形态对齐：a^{2(S m)}·a^{2(S m)} == a^{2(S m)+2(S m)} *)
    assert (Hdiag : q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m) ==
                    q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m)).
    { apply Qeq_sym. apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m) (2 * Datatypes.S m)). }
    setoid_replace ((q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)) *
        (q_pow a (2 * Datatypes.S m) / q_fact (2 * Datatypes.S m)))
      with (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m) /
            (q_fact (2 * Datatypes.S m) * q_fact (2 * Datatypes.S m))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m)) *
                       (Qinv (q_fact (2 * Datatypes.S m)) * Qinv (q_fact (2 * Datatypes.S m)))).
         - ring.
         - setoid_replace (q_pow a (2 * Datatypes.S m) * q_pow a (2 * Datatypes.S m))
             with (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m)) by exact Hdiag.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * Datatypes.S m)) (q_fact (2 * Datatypes.S m))).
           ring. }
    reflexivity.
Qed.

(* ===== 奇侧双和展开（o_sq_expand，对称于 e_sq_expand） ===== *)

(* 奇行单步：osq_row N (S i) == osq_row N i + 尾项（j = S i） *)
Lemma osq_row_succ : forall (N i : nat) (a : Q),QeqT (
  osq_row N (Datatypes.S i) a ) ( osq_row N i a +
    q_pow a (2 * N + 2 * Datatypes.S i + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i + 1))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 偶行单步：esq_row N (S i) == esq_row N i + 尾项（j = S i）——对称 osq_row_succ *)
Lemma esq_row_succ : forall (N i : nat) (a : Q),QeqT (
  esq_row N (Datatypes.S i) a ) ( esq_row N i a +
    q_pow a (2 * N + 2 * Datatypes.S i) / (q_fact (2 * N) * q_fact (2 * Datatypes.S i))).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 奇部分和乘单项 == 奇行求和：O_{S m}(a)·a^{2N+1}/(2N+1)! == osq_row N m a
   （O_{S m} = Σ_{k=0}^{m} a^{2k+1}/(2k+1)!，乘 a^{2N+1}/(2N+1)! 后每项
   a^{2k+1+2N+1}/((2k+1)!(2N+1)!) == a^{2N+2k+2}/((2N+1)!(2k+1)!)，k 从 0..m == osq_row N m；
   数值验证 m=0：O_1=a、a·a^{2N+1}/(2N+1)! == a^{2N+2}/(2N+1)! == osq_row N 0 ✓） *)
Lemma o_mul_term : forall (a : Q) (m N : nat),QeqT (
  o_sum (Datatypes.S m) a * (q_pow a (2 * N + 1) / q_fact (2 * N + 1)) ) ( osq_row N m a).
Proof.
  intros a m N.
  apply qeq_imp_qeqT.
  induction m as [| m'' IH].
  - (* m=0：O_1 = a ⟹ a·a^{2N+1}/(2N+1)! == osq_row N 0 = a^{2N+2}/((2N+1)!·1!) *)
    simpl.
    setoid_replace (0 + a * 1 / (1 * 1)) with a.
    2: { unfold Qdiv. field. all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)). }
    setoid_replace (q_pow a (N + (N + 0) + 2)) with (a * q_pow a (N + (N + 0) + 1)).
    2: { change (q_pow a (N + (N + 0) + 2) == a * q_pow a (N + (N + 0) + 1)).
         assert (Hidx : (N + (N + 0) + 2 = Datatypes.S (N + (N + 0) + 1))%nat) by lia.
         rewrite Hidx. apply qeqT_imp_qeq. apply (q_pow_succ a (N + (N + 0) + 1)). }
    field.
    all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
  - setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a (Datatypes.S m''))).
    setoid_replace ((o_sum (Datatypes.S m'') a + q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m''))) *
        (q_pow a (2 * N + 1) / q_fact (2 * N + 1)))
      with (o_sum (Datatypes.S m'') a * (q_pow a (2 * N + 1) / q_fact (2 * N + 1)) +
            (q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m''))) *
            (q_pow a (2 * N + 1) / q_fact (2 * N + 1))) by ring.
    setoid_rewrite IH.
    assert (Hadd : q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1) ==
                   q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))).
    { apply Qeq_sym.
      assert (Hc : (Datatypes.S (2 * Datatypes.S m'') + (2 * N + 1) =
                    2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))%nat) by lia.
      rewrite <- Hc. apply qeqT_imp_qeq. apply (q_pow_add a (Datatypes.S (2 * Datatypes.S m'')) (2 * N + 1)). }
    setoid_replace (q_pow a (Datatypes.S (2 * Datatypes.S m'')) / q_fact (Datatypes.S (2 * Datatypes.S m'')) *
        (q_pow a (2 * N + 1) / q_fact (2 * N + 1)))
      with (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')) /
            (q_fact (2 * N + 1) * q_fact (Datatypes.S (2 * Datatypes.S m'')))).
    2: { unfold Qdiv.
         transitivity ((q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1)) *
                       (Qinv (q_fact (Datatypes.S (2 * Datatypes.S m''))) * Qinv (q_fact (2 * N + 1)))).
         - ring.
         - setoid_replace (q_pow a (Datatypes.S (2 * Datatypes.S m'')) * q_pow a (2 * N + 1))
             with (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))) by exact Hadd.
           setoid_rewrite (Qinv_mult_distr (q_fact (2 * N + 1)) (q_fact (Datatypes.S (2 * Datatypes.S m'')))).
           ring. }
    (* 目标侧 osq_row N (S m'') == osq_row N m'' + 尾项；索引换形（Fixpoint 归约索引形态不一致） *)
    assert (Hidx1 : (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'') =
                     2 * N + 2 * Datatypes.S m'' + 2)%nat) by lia.
    assert (Hidx2 : (Datatypes.S (2 * Datatypes.S m'') =
                     2 * Datatypes.S m'' + 1)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')))
      with (q_pow a (2 * N + 2 * Datatypes.S m'' + 2)).
    2: { change (q_pow a (2 * N + 1 + Datatypes.S (2 * Datatypes.S m'')) ==
                   q_pow a (2 * N + 2 * Datatypes.S m'' + 2)).
         exact (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * N + 1 + Datatypes.S (2 * Datatypes.S m''))%nat
                 (2 * N + 2 * Datatypes.S m'' + 2)%nat Hidx1). }
    rewrite Hidx2.
    reflexivity.
Qed.

(* 奇次部分和平方 == 奇双和：O_m² == osq_sum m a *)
Lemma o_sq_expand : forall (a : Q) (m : nat),QeqT (
  o_sum m a * o_sum m a ) ( osq_sum m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - simpl. ring.
  - setoid_rewrite (qeqT_imp_qeq _ _ (o_sum_succ a m')).
    setoid_replace ((o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) *
        (o_sum m' a + q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))))
      with (o_sum m' a * o_sum m' a +
            2 * (o_sum m' a * (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))) +
            (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) *
            (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))) by ring.
    setoid_rewrite IH.
    assert (Ht : q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) ==
                 q_pow a (2 * m' + 1) / q_fact (2 * m' + 1)).
    { assert (Hidx : (Datatypes.S (2 * m') = 2 * m' + 1)%nat) by lia.
      setoid_replace (q_pow a (Datatypes.S (2 * m')))
        with (q_pow a (2 * m' + 1)).
      2: { exact (q_pow_comp_proper a a (Qeq_refl a)
                   (Datatypes.S (2 * m'))%nat (2 * m' + 1)%nat Hidx). }
      rewrite Hidx.
      reflexivity. }
    setoid_rewrite Ht.
    destruct m' as [| m''].
    + simpl.
      field.
      all: intro Hz0; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz0)).
    + setoid_replace (o_sum (Datatypes.S m'') a * (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)))
        with (osq_row (Datatypes.S m'') (Datatypes.S m'') a -
              q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) /
              (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      2: { setoid_rewrite (qeqT_imp_qeq _ _ (o_mul_term a m'' (Datatypes.S m''))).
           apply Qeq_sym.
           setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ (Datatypes.S m'') m'' a)).
           ring. }
      assert (Ht2 : (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)) *
                    (q_pow a (2 * Datatypes.S m'' + 1) / q_fact (2 * Datatypes.S m'' + 1)) ==
                    q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) /
                    (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      { assert (Hadd : q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1) ==
                       q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
        { apply Qeq_sym. apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m'' + 1) (2 * Datatypes.S m'' + 1)). }
        assert (Hidx : (2 * Datatypes.S m'' + 1 + 2 * Datatypes.S m'' + 1 =
                        2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat) by lia.
        unfold Qdiv.
        transitivity ((q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1)) *
                      (Qinv (q_fact (2 * Datatypes.S m'' + 1)) * Qinv (q_fact (2 * Datatypes.S m'' + 1)))).
        - ring.
        - setoid_replace (q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1))
            with (q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)).
          2: { assert (Hadd2 : q_pow a (2 * Datatypes.S m'' + 1) * q_pow a (2 * Datatypes.S m'' + 1) ==
                               q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)).
               { apply Qeq_sym.
                 transitivity (q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
                 - assert (Hc : ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1) =
                                 2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat) by lia.
                   change (q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) ==
                           q_pow a ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))).
                   apply (q_pow_comp_proper a a (Qeq_refl a)
                           (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2)%nat
                           ((2 * Datatypes.S m'' + 1) + (2 * Datatypes.S m'' + 1))%nat
                           (eq_sym Hc)).
                 - apply qeqT_imp_qeq. apply (q_pow_add a (2 * Datatypes.S m'' + 1) (2 * Datatypes.S m'' + 1)). }
               exact Hadd2. }
          setoid_rewrite (Qinv_mult_distr (q_fact (2 * Datatypes.S m'' + 1)) (q_fact (2 * Datatypes.S m'' + 1))).
          ring. }
      setoid_rewrite Ht2.
      set (D := q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) *
                 Qinv (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      change (osq_sum (Datatypes.S m'') a +
              2 * (osq_row (Datatypes.S m'') (Datatypes.S m'') a - D) + D ==
              osq_sum (Datatypes.S m'') a +
              2 * osq_row (Datatypes.S m'') (Datatypes.S m'') a -
              q_pow a (2 * Datatypes.S m'' + 2 * Datatypes.S m'' + 2) *
              Qinv (q_fact (2 * Datatypes.S m'' + 1) * q_fact (2 * Datatypes.S m'' + 1))).
      subst D.
      ring.
Qed.

(* ============ corr 封闭和（kloop_ksum 链）：corr 的 Σ 形式 ============ *)
(* kloop (S m) (2m+1) 与 kloop m (2m−1) 的展开深度依赖 m，不可逐层 simpl；
   用递增和 ksum（kloop 的封闭形式）使 corr 差分可计算。 *)

(* kloop 的递增和形式：ksum m k a := Σ_{i=0}^{k−1} inner2 (m+i) (2m−(m+i)) *)
Fixpoint ksum (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => ksum m k' a + inner2 (m + k') (2 * m - (m + k')) a
  end.

(* ksum 单步（正向） *)
Lemma ksum_succ : forall (m k : nat) (a : Q),QeqT (
  ksum m (Datatypes.S k) a ) ( ksum m k a + inner2 (m + k) (2 * m - (m + k)) a).
Proof. intros. apply qeq_imp_qeqT. reflexivity. Qed.

(* 辅助：kloop m k 尾部（k < m 时为 0）——kloop_succ 的反向条件 *)
Lemma kloop_below : forall (m k : nat) (a : Q),
  (k < m)%nat ->QeqT ( kloop m k a ) ( 0).
Proof.
  intros m k a Hkm.
  apply qeq_imp_qeqT.
  destruct k as [| k']; [reflexivity |].
  (* k = S k' < m ⟹ Nat.leb m (S k') = false ⟹ kloop = 0 *)
  simpl.
  assert (Hleb : Nat.leb m (Datatypes.S k') = false).
  { apply Nat.leb_gt. lia. }
  rewrite Hleb. reflexivity.
Qed.

(* kloop m (m+k') == ksum m (k'+1)（kloop 从 m+k' 递减到 m 累加 == ksum 递增） *)
Lemma kloop_ksum : forall (m k' : nat) (a : Q),QeqT (
  kloop m (m + k') a ) ( ksum m (k' + 1) a).
Proof.
  intros m k' a.
  apply qeq_imp_qeqT.
  induction k' as [| k' IH].
  - (* k'=0：kloop m m == ksum m 1 == inner2 m (2m−m) == inner2 m m *)
    simpl.
    destruct m as [| m'].
    + simpl. reflexivity.  (* m=0：kloop 0 0 = 0；ksum 0 1 = inner2 0 0 = 0 *)
    + (* m = S m'：kloop (S m') (S m') == inner2 (S m') (2(S m') − S m') + kloop (S m') m'；
         kloop (S m') m' == 0（m' < S m'）；2(S m') − S m' == S m' *)
      assert (Hk : kloop (Datatypes.S m') (Datatypes.S m') a ==
                   inner2 (Datatypes.S m') (2 * Datatypes.S m' - Datatypes.S m') a +
                   kloop (Datatypes.S m') m' a).
      { apply qeqT_imp_qeq. apply kloop_succ. lia. }
      (* 先归约 S m' + 0 == S m'，再应用 Hk *)
      assert (Hadd0 : (Datatypes.S m' + 0 = Datatypes.S m')%nat) by lia.
      rewrite Hadd0.
      setoid_rewrite Hk.
      setoid_rewrite (qeqT_imp_qeq _ _ (kloop_below (Datatypes.S m') m' a ltac:(lia))).
      assert (Hidx : (2 * Datatypes.S m' - Datatypes.S m' = Datatypes.S m')%nat) by lia.
      rewrite Hidx.
      (* 目标：inner2 (S m') (S m') + 0 == 0 + inner2 (S m') (S m' + S m' − S m')；
         归约 S m' + S m' − S m' == S m' 后 ring *)
      assert (Hsub : (Datatypes.S m' + Datatypes.S m' - Datatypes.S m' = Datatypes.S m')%nat) by lia.
      rewrite Hsub.
      ring.
  - (* k' = S k'：kloop m (m + S k') == kloop m (S (m+k')) *)
    assert (Hadd : (m + Datatypes.S k' = Datatypes.S (m + k'))%nat) by lia.
    rewrite Hadd.
    assert (Hk : kloop m (Datatypes.S (m + k')) a ==
                 inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a +
                 kloop m (m + k') a).
    { apply qeqT_imp_qeq. apply kloop_succ. lia. }
    setoid_rewrite Hk.
    setoid_rewrite IH.
    (* ksum m (S k' + 1) == ksum m (k'+1) + inner2 (m + (k'+1)) ... *)
    assert (Hks : ksum m (Datatypes.S (k' + 1)) a ==
                  ksum m (k' + 1) a + inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    setoid_rewrite <- Hks.
    (* 尾项索引：S(m+k') == m + (k'+1)；2m − S(m+k') == 2m − (m+(k'+1)) *)
    assert (Hidx1 : (Datatypes.S (m + k') = m + (k' + 1))%nat) by lia.
    assert (Hidx2 : (2 * m - Datatypes.S (m + k') = 2 * m - (m + (k' + 1)))%nat) by lia.
    setoid_replace (inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a)
      with (inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
    2: { change (inner2 (Datatypes.S (m + k')) (2 * m - Datatypes.S (m + k')) a ==
                 inner2 (m + (k' + 1)) (2 * m - (m + (k' + 1))) a).
         rewrite Hidx1. reflexivity. }
    (* RHS ksum (S(k'+1)) 展开 == ksum (k'+1) + inner2（Hks）；交换律收尾 *)
    setoid_rewrite Hks.
    ring.
Qed.

(* corr m == ksum m m（corr m = kloop m (2m−1) = kloop m (m + (m−1)) = ksum m m，m ≥ 1） *)
Lemma corr_ksum : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT ( corr m a ) ( ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  unfold corr.
  (* kloop m (2m−1)：2m−1 == m + (m−1) *)
  assert (Hidx : (2 * m - 1 = m + (m - 1))%nat) by lia.
  rewrite Hidx.
  assert (Hk : kloop m (m + (m - 1)) a == ksum m (m - 1 + 1) a).
  { apply qeqT_imp_qeq. apply kloop_ksum. }
  setoid_rewrite Hk.
  assert (Hsub : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hsub.
  reflexivity.
Qed.

(* corr (S m) == ksum (S m) (S m)（corr (S m) = kloop (S m) (2(S m)−1) = kloop (S m) (S m + S m?)）
   2(S m) − 1 == S m + (S m − 1) == S m + m ⟹ ksum (S m) (m+1) *)
Lemma corr_succ_ksum : forall (a : Q) (m : nat),QeqT (
  corr (Datatypes.S m) a ) ( ksum (Datatypes.S m) (Datatypes.S m) a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  unfold corr.
  (* kloop (S m) (2(S m) − 1)；2(S m)−1 == S m + S m − 1 == S m + m *)
  assert (Hidx : (2 * Datatypes.S m - 1 = Datatypes.S m + m)%nat) by lia.
  rewrite Hidx.
  assert (Hk : kloop (Datatypes.S m) (Datatypes.S m + m) a == ksum (Datatypes.S m) (m + 1) a).
  { apply qeqT_imp_qeq. apply kloop_ksum. }
  setoid_rewrite Hk.
  assert (Hsub : (m + 1 = Datatypes.S m)%nat) by lia.
  rewrite Hsub.
  reflexivity.
Qed.

(* ============ corr_succ：corr 差分分解（ksum_diff） ============ *)

(* ksum 差分累积：ksum (S m) k == ksum m k + ksum_diff m k *)
Fixpoint ksum_diff (m k : nat) (a : Q) : Q :=
  match k with
  | 0%nat => 0
  | Datatypes.S k' => ksum_diff m k' a +
      (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a -
       inner2 (m + k') (2 * m - (m + k')) a)
  end.

Lemma ksum_diff_correct : forall (m k : nat) (a : Q),QeqT (
  ksum (Datatypes.S m) k a ) ( ksum m k a + ksum_diff m k a).
Proof.
  intros m k a.
  apply qeq_imp_qeqT.
  induction k as [| k' IH].
  - simpl. ring.
  - (* 展开 ksum_diff (S k')：定义性 == ksum_diff k' + (inner2 (S m + k') ... − inner2 (m + k') ...) *)
    change (ksum (Datatypes.S m) (Datatypes.S k') a ==
            ksum m (Datatypes.S k') a +
            (ksum_diff m k' a +
             (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a -
              inner2 (m + k') (2 * m - (m + k')) a))).
    assert (H1 : ksum (Datatypes.S m) (Datatypes.S k') a ==
                 ksum (Datatypes.S m) k' a + inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    assert (H2 : ksum m (Datatypes.S k') a ==
                 ksum m k' a + inner2 (m + k') (2 * m - (m + k')) a).
    { apply qeqT_imp_qeq. apply ksum_succ. }
    setoid_rewrite H1. setoid_rewrite H2. setoid_rewrite IH.
    ring.
Qed.

(* corr (S m) − corr m == ksum_diff m m + inner2 (2m+1) (2(S m)−(2m+1))（m ≥ 1） *)
Lemma corr_succ_decomp : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_ksum a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_ksum a m Hm)).
  assert (H1 : ksum (Datatypes.S m) (Datatypes.S m) a ==
               ksum (Datatypes.S m) m a + inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a).
  { apply qeqT_imp_qeq. apply ksum_succ. }
  setoid_rewrite H1.
  assert (H2 : ksum (Datatypes.S m) m a == ksum m m a + ksum_diff m m a).
  { apply qeqT_imp_qeq. apply ksum_diff_correct. }
  setoid_rewrite H2.
  (* 先归约 inner2 索引（S m + m == 2m+1、2·S m − (2m+1) == 1）再 ring *)
  assert (Hidx : (Datatypes.S m + m = 2 * m + 1)%nat) by lia.
  assert (Hj : (2 * Datatypes.S m - (2 * m + 1) = 1)%nat) by lia.
  (* 换 LHS inner2 索引：S m + m → 2m+1、2·S m − (S m + m) → 1 *)
  setoid_replace (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a)
    with (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
  2: { change (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a ==
               inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
       rewrite Hidx. reflexivity. }
  ring.
Qed.

(* ============ corr 论证基础设施：有界和 + 行匹配（备份 83 并入，来自 _dbg_kdr.v） ============ *)

(* 有界和：sum_upto n f = Σ_{i=0}^{n−1} f i（斜对角和的基础设施；封闭和推广判例） *)
Fixpoint sum_upto (n : nat) (f : nat -> Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => sum_upto n' f + f n'
  end.

(* q_fact 参数换形（nat 恒等 → Qeq；q_fact 参数形态 2·S N vs 2N+2 非定义性相等） *)
Lemma q_fact_nat_eq : forall (n m : nat), n = m ->QeqT ( q_fact n ) ( q_fact m).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* inner2 k J == Σ_{j=1}^{J} brk2 k j == sum_upto J (fun j => brk2 k (S j))——归纳于 J（k 固定） *)
Lemma inner2_sum_upto : forall (k J : nat) (a : Q),QeqT (
  inner2 k J a ) ( sum_upto J (fun j : nat => brk2 k (Datatypes.S j) a)).
Proof.
  intros k J a.
  apply qeq_imp_qeqT.
  induction J as [| J' IH].
  - reflexivity.
  - change (inner2 k (Datatypes.S J') a ==
            sum_upto J' (fun j : nat => brk2 k (Datatypes.S j) a) + brk2 k (Datatypes.S J') a).
    setoid_rewrite <- IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ k J' a)).
    ring.
Qed.

(* ksum_diff (S m) k == Σ_{k'=0}^{k−1} (inner2 (m+2+k') (m+2−k') − inner2 (m+1+k') (m+1−k'))
   ——归纳于 k（m 固定）：斜对角累积的封闭和表示 *)
Lemma ksum_diff_sum_upto : forall (m k : nat) (a : Q),QeqT (
  ksum_diff (Datatypes.S m) k a ) (
  sum_upto k (fun k' : nat =>
    inner2 (m + 2 + k') (m + 2 - k') a -
    inner2 (m + 1 + k') (m + 1 - k') a)).
Proof.
  intros m k a.
  apply qeq_imp_qeqT.
  induction k as [| k' IH].
  - reflexivity.
  - change (ksum_diff (Datatypes.S m) (Datatypes.S k') a ==
            sum_upto k' (fun k0 : nat =>
              inner2 (m + 2 + k0) (m + 2 - k0) a -
              inner2 (m + 1 + k0) (m + 1 - k0) a) +
            (inner2 (m + 2 + k') (m + 2 - k') a -
             inner2 (m + 1 + k') (m + 1 - k') a)).
    setoid_rewrite <- IH.
    change (ksum_diff (Datatypes.S m) (Datatypes.S k') a) with
      (ksum_diff (Datatypes.S m) k' a +
       (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a -
        inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a)).
    assert (H1 : (Datatypes.S (Datatypes.S m) + k' = m + 2 + k')%nat) by lia.
    assert (H2 : (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k') = m + 2 - k')%nat) by lia.
    assert (H3 : (Datatypes.S m + k' = m + 1 + k')%nat) by lia.
    assert (H4 : (2 * Datatypes.S m - (Datatypes.S m + k') = m + 1 - k')%nat) by lia.
    setoid_replace (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a)
      with (inner2 (m + 2 + k') (m + 2 - k') a).
    2: { change (inner2 (Datatypes.S (Datatypes.S m) + k') (2 * Datatypes.S (Datatypes.S m) - (Datatypes.S (Datatypes.S m) + k')) a ==
                 inner2 (m + 2 + k') (m + 2 - k') a).
         rewrite H2. rewrite H1. reflexivity. }
    setoid_replace (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a)
      with (inner2 (m + 1 + k') (m + 1 - k') a).
    2: { change (inner2 (Datatypes.S m + k') (2 * Datatypes.S m - (Datatypes.S m + k')) a ==
                 inner2 (m + 1 + k') (m + 1 - k') a).
         rewrite H4. rewrite H3. reflexivity. }
    ring.
Qed.

(* 行匹配：−inner2 N i == 2·esq_row (S N) i − 2·osq_row N (i−1) − 2T
   ——归纳于 i、行 N 固定（ksum_diff_row 归纳步分解第 1 块；Python 数值+符号验证 N,i≤5） *)
Lemma rows_vs_inner_i : forall (a : Q) (N i : nat),
  (1 <= i)%nat ->QeqT (
  - inner2 N i a ) (
    2 * esq_row (Datatypes.S N) i a -
    2 * osq_row N (i - 1) a -
    2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))).
Proof.
  intros a N i Hi.
  apply qeq_imp_qeqT.
  destruct i as [| i'].
  - lia.
  - induction i' as [| i'' IH2].
    + setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ N 0 a)).
      setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_succ (Datatypes.S N) 0 a)).
      change (inner2 N 0 a) with 0.
      change (esq_row (Datatypes.S N) 0 a) with
        (q_pow a (2 * Datatypes.S N) / (q_fact (2 * Datatypes.S N) * q_fact 0)).
      change (brk2 N 1 a) with
        (2 * q_pow a (2 * N + 2 * 1) / (q_fact (2 * N + 1) * q_fact (2 * 1 - 1)) -
         2 * q_pow a (2 * N + 2 * 1) / (q_fact (2 * N + 2) * q_fact (2 * 1 - 2))).
      change (osq_row N (1 - 1) a) with
        (q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)).
      assert (H2 : (2 * Datatypes.S N = 2 * N + 2)%nat) by lia.
      assert (H4 : (2 * Datatypes.S N + 2 = 2 * N + 4)%nat) by lia.
      assert (Hb : (2 * N + 2 * 1 = 2 * N + 2)%nat) by lia.
      assert (Ht : (2 * N + 2 * 1 + 2 = 2 * N + 4)%nat) by lia.
      setoid_replace (q_pow a (2 * Datatypes.S N)) with (q_pow a (2 * N + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N)%nat (2 * N + 2)%nat H2). }
      setoid_replace (q_pow a (2 * Datatypes.S N + 2)) with (q_pow a (2 * N + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N + 2)%nat (2 * N + 4)%nat H4). }
      setoid_replace (q_pow a (2 * N + 2 * 1)) with (q_pow a (2 * N + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * 1)%nat (2 * N + 2)%nat Hb). }
      setoid_replace (q_pow a (2 * N + 2 * 1 + 2)) with (q_pow a (2 * N + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * 1 + 2)%nat (2 * N + 4)%nat Ht). }
      setoid_replace (q_fact (2 * Datatypes.S N)) with (q_fact (2 * N + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1 - 1)) with (q_fact 1).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1 - 2)) with (q_fact 0).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * 1)) with (q_fact 2).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      change (q_fact 0) with 1.
      change (q_fact 1) with 1.
      change (q_fact 2) with 2.
      unfold Qdiv.
      ring.
    + assert (Hi' : (1 <= Datatypes.S i'')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_succ N (Datatypes.S i'') a)).
      setoid_replace (- (inner2 N (Datatypes.S i'') a + brk2 N (Datatypes.S (Datatypes.S i'')) a))
        with (- inner2 N (Datatypes.S i'') a - brk2 N (Datatypes.S (Datatypes.S i'')) a) by ring.
      unfold brk2.
      setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_succ (Datatypes.S N) (Datatypes.S i'') a)).
      setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ N i'' a)).
      setoid_rewrite (IH2 Hi').
      assert (H6 : (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i'') =
                    2 * N + 2 * i'' + 6)%nat) by lia.
      assert (H6b : (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2 =
                     2 * N + 2 * i'' + 6)%nat) by lia.
      assert (H4 : (2 * N + 2 * Datatypes.S (Datatypes.S i'') =
                    2 * N + 2 * i'' + 4)%nat) by lia.
      assert (H4b : (2 * N + 2 * Datatypes.S i'' + 2 =
                     2 * N + 2 * i'' + 4)%nat) by lia.
      setoid_replace (q_pow a (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i'')))
        with (q_pow a (2 * N + 2 * i'' + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * Datatypes.S N + 2 * Datatypes.S (Datatypes.S i''))%nat
                   (2 * N + 2 * i'' + 6)%nat H6). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S (Datatypes.S i'')))
        with (q_pow a (2 * N + 2 * i'' + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S (Datatypes.S i''))%nat
                   (2 * N + 2 * i'' + 4)%nat H4). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S i'' + 2))
        with (q_pow a (2 * N + 2 * i'' + 4)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S i'' + 2)%nat
                   (2 * N + 2 * i'' + 4)%nat H4b). }
      setoid_replace (q_pow a (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2))
        with (q_pow a (2 * N + 2 * i'' + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * N + 2 * Datatypes.S (Datatypes.S i'') + 2)%nat
                   (2 * N + 2 * i'' + 6)%nat H6b). }
      setoid_replace (q_fact (2 * Datatypes.S N)) with (q_fact (2 * N + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * Datatypes.S (Datatypes.S i'') - 1))
        with (q_fact (2 * Datatypes.S i'' + 1)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * Datatypes.S (Datatypes.S i'') - 2))
        with (q_fact (2 * Datatypes.S i'')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      assert (Hsub : (Datatypes.S i'' - 1 = i'')%nat) by lia.
      setoid_replace (osq_row N (Datatypes.S i'' - 1) a) with (osq_row N i'' a).
      2: { change (osq_row N (Datatypes.S i'' - 1) a == osq_row N i'' a).
           rewrite Hsub. reflexivity. }
      unfold Qdiv.
      ring.
Qed.

(* ============ 有界和换元引理族（备份 84 并入，来自 _dbg_kdr.v） ============ *)

(* 线性：Σ(f+g) == Σf + Σg——归纳于 n *)
Lemma sum_upto_plus : forall (n : nat) (f g : nat -> Q),QeqT (
  sum_upto n (fun i => f i + g i) ) ( sum_upto n f + sum_upto n g).
Proof.
  intros n f g.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - change (sum_upto n' (fun i => f i + g i) + (f n' + g n') ==
            sum_upto n' f + f n' + (sum_upto n' g + g n')).
    setoid_rewrite IH.
    ring.
Qed.

Lemma sum_upto_zero : forall (n : nat),QeqT ( sum_upto n (fun _ => 0) ) ( 0).
Proof.
  intros n.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* 外延：逐点相等 → 和相等 *)
Lemma sum_upto_ext : forall (n : nat) (f g : nat -> Q),
  (forall i,QeqT ( f i ) ( g i)) ->QeqT ( sum_upto n f ) ( sum_upto n g).
Proof.
  intros n f g H.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. setoid_rewrite IH. setoid_rewrite (qeqT_imp_qeq _ _ (H n')). reflexivity.
Qed.

(* 首项移出：Σ_{i=0}^{n} h i == h 0 + Σ_{i=0}^{n−1} h (i+1)——归纳于 n（换元基础） *)
Lemma sum_upto_rot : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto (Datatypes.S n) h ) ( h 0%nat + sum_upto n (fun i => h (Datatypes.S i))).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - simpl. ring.
  - change (sum_upto (Datatypes.S n') h + h (Datatypes.S n') ==
            h 0%nat + sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))).
    setoid_rewrite IH.
    change (sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))) with
      (sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
    ring.
Qed.

(* 移位反向：Σ_{i=0}^{n−1} h (n−i) == Σ_{i=0}^{n−1} h (i+1)——归纳步用 sum_upto_rot *)
Lemma sum_upto_shift_rev : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto n (fun i => h (n - i)%nat) ) ( sum_upto n (fun i => h (Datatypes.S i))).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => h (Datatypes.S n' - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => h (Datatypes.S n' - Datatypes.S i)%nat) (fun i => h (n' - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - Datatypes.S i = n' - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    setoid_rewrite IH.
    change (h (Datatypes.S n' - 0)%nat) with (h (Datatypes.S n')).
    change (sum_upto (Datatypes.S n') (fun i => h (Datatypes.S i))) with
      (sum_upto n' (fun i => h (Datatypes.S i)) + h (Datatypes.S n')).
    ring.
Qed.

(* 反向和：Σ_{i=0}^{n−1} h (n−1−i) == Σ_{i=0}^{n−1} h i *)
Lemma sum_upto_rev : forall (n : nat) (h : nat -> Q),QeqT (
  sum_upto n (fun i => h (n - 1 - i)%nat) ) ( sum_upto n h).
Proof.
  intros n h.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => h (Datatypes.S n' - 1 - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => h (Datatypes.S n' - 1 - Datatypes.S i)%nat) (fun i => h (n' - 1 - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - 1 - Datatypes.S i = n' - 1 - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    assert (Hn : (Datatypes.S n' - 1 = n')%nat) by lia.
    rewrite Hn.
    setoid_rewrite IH.
    assert (Hz : (n' - 0 = n')%nat) by lia.
    rewrite Hz.
    change (sum_upto (Datatypes.S n') h) with (sum_upto n' h + h n').
    ring.
Qed.

(* 矩形区域换序：Σ_i Σ_j f i j == Σ_j Σ_i f i j——归纳于 m（n 固定） *)
Lemma sum_upto_rect_swap : forall (m n : nat) (f : nat -> nat -> Q),QeqT (
  sum_upto m (fun i => sum_upto n (fun j => f i j)) ) (
  sum_upto n (fun j => sum_upto m (fun i => f i j))).
Proof.
  intros m n f.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - simpl. apply Qeq_sym. apply qeqT_imp_qeq. apply sum_upto_zero.
  - change (sum_upto m' (fun i => sum_upto n (fun j => f i j)) + sum_upto n (fun j => f m' j) ==
            sum_upto n (fun j => sum_upto (Datatypes.S m') (fun i => f i j))).
    setoid_rewrite IH.
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n (fun j => sum_upto (Datatypes.S m') (fun i => f i j)) (fun j => sum_upto m' (fun i => f i j) + f m' j) Hprm)).
    2: { intro j. apply qeq_imp_qeqT. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_plus n (fun j => sum_upto m' (fun i => f i j)) (fun j => f m' j))).
    ring.
Qed.

(* ============ 双重和换序引理族（备份 85 并入，来自 _dbg_kdr.v） ============ *)

(* 带范围的外延：仅需 i < n 时逐点相等（S m'−i == S(m'−i) 类 lia 恒等只对 i ≤ m' 成立） *)
Lemma sum_upto_ext_below : forall (n : nat) (f g : nat -> Q),
  (forall i : nat, NatLe (Datatypes.S i) n ->QeqT ( f i ) ( g i)) ->QeqT ( sum_upto n f ) ( sum_upto n g).
Proof.
  intros n f g H.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    setoid_rewrite (IH (fun i : nat => fun Hi =>
                        H i (NatLe_lift _ _ (Nat.le_le_succ_r (Datatypes.S i) n' (NatLe_drop (Datatypes.S i) n' Hi))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (H n' (NatLe_lift _ _ (Nat.lt_succ_diag_r n')))).
    reflexivity.
Qed.

(* ============ ksum_diff_row 论证：corr 差分 == 行差分（备份 89 并入，来自 _dbg_kdr.v） ============ *)

(* ===== ksum_diff_row 直接证明（不归纳）：corr 差分 == 行差分 =====
   第一步检验：corr_succ_decomp 反向 + ksum_succ/ksum_diff_correct 链，看目标形态 *)
Lemma ksum_diff_row_step1 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  corr (Datatypes.S m) a - corr m a).
Proof.
  intros a m Hm. exact (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)))).
Qed.

(* 第二步：LHS == corr 差分 == ksum (S m) (S m) − ksum m m
   ——corr_succ_ksum / corr_ksum + ksum_succ + ksum_diff_correct 链 *)
Lemma ksum_diff_row_step2 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  ksum (Datatypes.S m) (Datatypes.S m) a - ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* corr_succ_decomp：LHS == corr (S m) − corr m *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  (* corr (S m) == ksum (S m) (S m)、corr m == ksum m m *)
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_ksum a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_ksum a m Hm)).
  reflexivity.
Qed.

(* 第三步：ksum (S m) (S m) 展开 == ksum (S m) m + inner2 (2m+1) 1（ksum_succ + 索引归约）
   ——目标：ksum_diff m m + inner2 (2m+1) 1 == ksum (S m) m + inner2 (2m+1) 1 − ksum m m *)
Lemma ksum_diff_row_step3 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) 1 a ) (
  ksum (Datatypes.S m) (Datatypes.S m) a - ksum m m a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* ksum (S m) (S m) == ksum (S m) m + inner2 (S m + m) (2·S m − (S m + m)) *)
  assert (Hk : ksum (Datatypes.S m) (Datatypes.S m) a ==
               ksum (Datatypes.S m) m a + inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a).
  { apply qeqT_imp_qeq. apply ksum_succ. }
  setoid_rewrite Hk.
  (* 归约 inner2 索引：S m + m == 2m+1、2·S m − (S m + m) == 1——先 Hj 后 Hidx（Hidx 全局替换会破坏 Hj 子项） *)
  assert (Hidx : (Datatypes.S m + m = 2 * m + 1)%nat) by lia.
  assert (Hj : (2 * Datatypes.S m - (Datatypes.S m + m) = 1)%nat) by lia.
  setoid_replace (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a)
    with (inner2 (2 * m + 1) 1 a).
  2: { change (inner2 (Datatypes.S m + m) (2 * Datatypes.S m - (Datatypes.S m + m)) a ==
               inner2 (2 * m + 1) 1 a).
       rewrite Hj. rewrite Hidx. reflexivity. }
  (* ksum (S m) m == ksum m m + ksum_diff m m（ksum_diff_correct） *)
  assert (Hd : ksum (Datatypes.S m) m a == ksum m m a + ksum_diff m m a).
  { apply qeqT_imp_qeq. apply ksum_diff_correct. }
  setoid_rewrite Hd.
  ring.
Qed.

(* ksum_diff 第一参数 Leibniz（m 非递归参数——仅 k 递归；m1 == m2 时定义性替换） *)
Lemma ksum_diff_nat_eq : forall (m1 m2 k : nat) (a : Q),
  m1 = m2 ->QeqT ( ksum_diff m1 k a ) ( ksum_diff m2 k a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* 步骤4检验：ksum_diff_row LHS 用 ksum_diff_sum_upto 展开（m−1 版本）
   ksum_diff m m == sum_upto m (inner2 (m+1+k') (m+1−k') − inner2 (m+k') (m−k')) *)
Lemma ksum_diff_row_step4 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a ) (
  sum_upto m (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* ksum_diff 第一参数替换：m == S(m−1)——ksum_diff_nat_eq（第二参数保持 m） *)
  assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
  assert (Hbr : ksum_diff m m a == ksum_diff (Datatypes.S (m - 1)) m a).
  { apply qeqT_imp_qeq. apply (ksum_diff_nat_eq m (Datatypes.S (m - 1)) m a Hsm). }
  setoid_rewrite Hbr.
  (* ksum_diff_sum_upto 于 N=m−1、k=m：ksum_diff (S(m−1)) m ==
     sum_upto m (inner2 (m+1+k')(m+1−k') − inner2 (m+k')(m−k')) *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_sum_upto (m - 1) m a)).
  (* ext_below 归约 brk2 参数（m−1+2+k' == m+1+k' 等） *)
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun k' => inner2 (m - 1 + 2 + k') (m - 1 + 2 - k') a - inner2 (m - 1 + 1 + k') (m - 1 + 1 - k') a) (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a) Hprm)).
  2: { intros k' Hk'. apply NatLe_drop in Hk'. apply qeq_imp_qeqT.
       assert (H1 : (m - 1 + 2 + k' = m + 1 + k')%nat) by lia.
       assert (H2 : (m - 1 + 2 - k' = m + 1 - k')%nat) by lia.
       assert (H3 : (m - 1 + 1 + k' = m + k')%nat) by lia.
       assert (H4 : (m - 1 + 1 - k' = m - k')%nat) by lia.
       setoid_rewrite H1. setoid_rewrite H2. setoid_rewrite H3. setoid_rewrite H4.
       reflexivity. }
  reflexivity.
Qed.

(* osq_row 第二参数 Leibniz（S(m−1) == m 桥） *)
Lemma osq_row_nat_eq2 : forall (N i1 i2 : nat) (a : Q),
  i1 = i2 ->QeqT ( osq_row N i1 a ) ( osq_row N i2 a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* RHS 闭合：行差分 == [esq_sum (S m) − esq_sum m] − [osq_sum (S m) − osq_sum m]
   2·esq_row (S m) m + Te² − 2·osq_row m (m−1) − To²，Te² = a^{4m+4}/((2m+2)!)²、To² = a^{4m+2}/((2m+1)!)²
   ——esq_sum/osq_sum 单步定义性 + osq_row_succ（osq_row m m == osq_row m (m−1) + To²） *)
Lemma row_diff_closed : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) ) (
  (esq_sum (Datatypes.S m) a - esq_sum m a) -
  (osq_sum (Datatypes.S m) a - osq_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* esq_sum (S m) == esq_sum m + 2·esq_row (S m) m + q_pow a (2·S m+2·S m)/((2·S m)!(2·S m)!)（定义性单步） *)
  change (esq_sum (Datatypes.S m) a) with
    (esq_sum m a + 2 * esq_row (Datatypes.S m) m a +
     q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m) /
       (q_fact (2 * Datatypes.S m) * q_fact (2 * Datatypes.S m))).
  (* osq_sum (S m) == osq_sum m + 2·osq_row m m − q_pow a (2m+2m+2)/((2m+1)!(2m+1)!)（定义性单步） *)
  change (osq_sum (Datatypes.S m) a) with
    (osq_sum m a + 2 * osq_row m m a -
     q_pow a (2 * m + 2 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  (* osq_row m m == osq_row m (S(m−1))（第二参数 nat_eq）再 osq_row_succ 展开 *)
  assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
  setoid_replace (osq_row m m a) with (osq_row m (Datatypes.S (m - 1)) a).
  2: { apply qeqT_imp_qeq. apply (osq_row_nat_eq2 m m (Datatypes.S (m - 1)) a Hsm). }
  setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_succ m (m - 1) a)).
  (* 归约 osq_row_succ 尾项：2m+2·S(m−1)+2 == 4m+2、2·S(m−1)+1 == 2m+1 *)
  assert (Hp3 : (2 * m + 2 * Datatypes.S (m - 1) + 2 = 4 * m + 2)%nat) by lia.
  assert (Hf3 : (2 * Datatypes.S (m - 1) + 1 = 2 * m + 1)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * Datatypes.S (m - 1) + 2))
    with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * m + 2 * Datatypes.S (m - 1) + 2)%nat (4 * m + 2)%nat Hp3). }
  setoid_replace (q_fact (2 * Datatypes.S (m - 1) + 1)) with (q_fact (2 * m + 1)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
  (* 归约 esq_sum 尾项：2·S m+2·S m == 4m+4、2·S m == 2m+2 *)
  assert (Hp1 : (2 * Datatypes.S m + 2 * Datatypes.S m = 4 * m + 4)%nat) by lia.
  assert (Hf1 : (2 * Datatypes.S m = 2 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * Datatypes.S m + 2 * Datatypes.S m))
    with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * Datatypes.S m + 2 * Datatypes.S m)%nat (4 * m + 4)%nat Hp1). }
  setoid_replace (q_fact (2 * Datatypes.S m)) with (q_fact (2 * m + 2)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
  (* 归约 osq_sum 尾项：2m+2m+2 == 4m+2 *)
  assert (Hp2 : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2))
    with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a)
               (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat Hp2). }
  ring.
Qed.

(* ksum_diff_row 主框架：corr 差分 == 行差分（经 esq_sum/osq_sum）
   LHS = corr (S m) − corr m（corr_succ_decomp 反向）
       = ksum (S m) (S m) − ksum m m（corr_succ_ksum/corr_ksum）
   RHS = 行差分（row_diff_closed）
        == [esq_sum(S m)−esq_sum m] − [osq_sum(S m)−osq_sum m]
        == (E_{S m}²−O_{S m}²) − (E_m²−O_m²)（e/o_sq_expand）
   中间桥：corr 差分 == E/O 平方差分（待配对论证；此处先证 RHS 侧闭合） *)
Lemma ksum_diff_row_rhs : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) ) (
  (e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
   o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a) -
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* e_sq_expand/o_sq_expand：目标含 e_sum²·−o_sum² 项——正向换 esq_sum/osq_sum（LHS==RHS 形式） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sq_expand a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sq_expand a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (e_sq_expand a (Datatypes.S m))).
  setoid_rewrite (qeqT_imp_qeq _ _ (o_sq_expand a (Datatypes.S m))).
  (* 目标 RHS 重排：esq_sum(S m) − osq_sum(S m) − (esq_sum m − osq_sum m)
     == (esq_sum(S m)−esq_sum m) − (osq_sum(S m)−osq_sum m)——setoid_replace + ring（纯原子） *)
  setoid_replace (esq_sum (Datatypes.S m) a - osq_sum (Datatypes.S m) a -
                  (esq_sum m a - osq_sum m a))
    with ((esq_sum (Datatypes.S m) a - esq_sum m a) -
          (osq_sum (Datatypes.S m) a - osq_sum m a)) by ring.
  (* 目标：行差分 == [esq_sum(S m)−esq_sum m] − [osq_sum(S m)−osq_sum m]——row_diff_closed 反向 *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (row_diff_closed a m Hm)).
  reflexivity.
Qed.

(* 移位+边界（二维）：Σ g (S i) (n−i) == Σ g i (n+1−i) + g n 1 − g 0 (n+1)
   ——归纳于 n（IH 对 ∀g，归纳步用 IH 于 g' = g∘S 处理双 S 错位） *)
Lemma sum_upto_shift_boundary : forall (n : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto n (fun i => g (Datatypes.S i) (n - i)%nat) ) (
  sum_upto n (fun i => g i (n + 1 - i)%nat) + g n 1%nat - g 0%nat (n + 1)%nat).
Proof.
  intros n.
  induction n as [| n' IH].
  - intros g. apply qeq_imp_qeqT. simpl. ring.
  - intros g. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => g (Datatypes.S i) (Datatypes.S n' - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => g (Datatypes.S (Datatypes.S i)) (Datatypes.S n' - Datatypes.S i)%nat) (fun i => g (Datatypes.S (Datatypes.S i)) (n' - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S n' - Datatypes.S i = n' - i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n' (fun i => g i (Datatypes.S n' + 1 - i)%nat))).
    rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext n' (fun i => g (Datatypes.S i) (Datatypes.S n' + 1 - Datatypes.S i)%nat) (fun i => g (Datatypes.S i) (n' + 1 - i)%nat) Hprm)).
    2: { intro i. apply qeq_imp_qeqT. assert (Hnat2 : (Datatypes.S n' + 1 - Datatypes.S i = n' + 1 - i)%nat) by lia.
         rewrite Hnat2. reflexivity. }
    setoid_rewrite (qeqT_imp_qeq _ _ (IH (fun i j => g (Datatypes.S i) j))).
    assert (Hn1 : (Datatypes.S n' = n' + 1)%nat) by lia.
    rewrite Hn1.
    assert (Hz1 : (n' + 1 - 0 = n' + 1)%nat) by lia.
    rewrite Hz1.
    assert (Hz2 : (n' + 1 + 1 - 0 = n' + 1 + 1)%nat) by lia.
    rewrite Hz2.
    ring.
Qed.

(* 行分解：Σ_{i=0}^{S m'} Σ_{j=1}^{S m'−i} g(i,j) == LHS(m') + Σ_{i=0}^{S m'} g i (m'+1−i) *)
Lemma sum_upto_row_succ : forall (m' : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto (Datatypes.S m') (fun i => sum_upto (Datatypes.S m' - i) (fun j => g i (Datatypes.S j))) ) (
  sum_upto m' (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j))) +
  sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)).
Proof.
  intros m' g.
  apply qeq_imp_qeqT.
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below (Datatypes.S m') (fun i => sum_upto (Datatypes.S m' - i) (fun j => g i (Datatypes.S j))) (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)) + g i (m' + 1 - i)%nat) Hprm)).
  2: { intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT.
       assert (Hnat : (Datatypes.S m' - i = Datatypes.S (m' - i))%nat) by lia.
       rewrite Hnat.
       change (sum_upto (m' - i) (fun j : nat => g i (Datatypes.S j)) +
               g i (Datatypes.S (m' - i)) ==
               sum_upto (m' - i) (fun j : nat => g i (Datatypes.S j)) + g i (m' + 1 - i)%nat).
       assert (Hnat2 : (Datatypes.S (m' - i) = m' + 1 - i)%nat) by lia.
       rewrite Hnat2.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (Datatypes.S m')
           (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)))
           (fun i => g i (m' + 1 - i)%nat))).
  assert (Hm : (m' - m' = 0)%nat) by lia.
  change (sum_upto (Datatypes.S m') (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j)))) with
    (sum_upto m' (fun i => sum_upto (m' - i) (fun j => g i (Datatypes.S j))) +
     sum_upto (m' - m') (fun j => g m' (Datatypes.S j))).
  rewrite Hm.
  simpl. ring.
Qed.

(* 列分解：Σ_{j=0}^{S m'} Σ_{i=0}^{S m'−S j} g(i,j) == RHS(m') + Σ_{i=0}^{S m'} g i (m'+1−i) *)
Lemma sum_upto_col_succ : forall (m' : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) ) (
  sum_upto m' (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) +
  sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)).
Proof.
  intros m' g.
  apply qeq_imp_qeqT.
  change (sum_upto (Datatypes.S m') (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))) with
    (sum_upto m' (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) +
     sum_upto (Datatypes.S m' - Datatypes.S m' + 1) (fun i => g i (Datatypes.S m'))).
  assert (Hlast : (Datatypes.S m' - Datatypes.S m' + 1 = 1)%nat) by lia.
  rewrite Hlast.
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m' (fun j => sum_upto (Datatypes.S m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j))) (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j)) Hprm)).
  2: { intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT.
       assert (Hnat : (Datatypes.S m' - Datatypes.S j + 1 = Datatypes.S (m' - j))%nat) by lia.
       rewrite Hnat.
       change (sum_upto (m' - j) (fun i : nat => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j) ==
               sum_upto (m' - Datatypes.S j + 1) (fun i : nat => g i (Datatypes.S j)) + g (m' - j)%nat (Datatypes.S j)).
       assert (Hnat2 : (m' - j = m' - Datatypes.S j + 1)%nat) by lia.
       rewrite Hnat2.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m'
           (fun j => sum_upto (m' - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))
           (fun j => g (m' - j)%nat (Datatypes.S j)))).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev m' (fun j => g (m' - j)%nat (Datatypes.S j)))).
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m' (fun k => g (m' - (m' - 1 - k))%nat (Datatypes.S (m' - 1 - k))) (fun k => g (Datatypes.S k) (m' - k)%nat) Hprm)).
  2: { intros k Hk. apply NatLe_drop in Hk. apply qeq_imp_qeqT.
       assert (Hx : (m' - (m' - 1 - k) = Datatypes.S k)%nat) by lia.
       rewrite Hx.
       assert (Hy : (Datatypes.S (m' - 1 - k) = m' - k)%nat) by lia.
       rewrite Hy.
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_shift_boundary m' g)).
  change (sum_upto (Datatypes.S m') (fun i => g i (m' + 1 - i)%nat)) with
    (sum_upto m' (fun i => g i (m' + 1 - i)%nat) + g m' (m' + 1 - m')%nat).
  assert (H1 : (m' + 1 - m' = 1)%nat) by lia.
  rewrite H1.
  simpl.
  assert (Hsm : (Datatypes.S m' = m' + 1)%nat) by lia.
  rewrite Hsm.
  ring.
Qed.

(* 标准三角形换序：Σ_{i=0}^{m−1} Σ_{j=1}^{m−i} g(i,j) == Σ_{j=1}^{m} Σ_{i=0}^{m−j} g(i,j)
   ——归纳于 m：LHS 用 row_succ、RHS 用 col_succ 分解（相同 D 抵消） *)
Lemma sum_upto_tri_swap_std : forall (m : nat) (g : nat -> nat -> Q),QeqT (
  sum_upto m (fun i => sum_upto (m - i) (fun j => g i (Datatypes.S j))) ) (
  sum_upto m (fun j => sum_upto (m - Datatypes.S j + 1) (fun i => g i (Datatypes.S j)))).
Proof.
  intros m.
  induction m as [| m' IH].
  - intros g. apply qeq_imp_qeqT. reflexivity.
  - intros g. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_row_succ m' g)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_col_succ m' g)).
    specialize (IH g).
    setoid_rewrite (qeqT_imp_qeq _ _ IH).
    ring.
Qed.

(* ============ 有界和分段引理（备份 86 并入，来自 _dbg_kdr.v） ============ *)
(* 一维移位+边界：Σ_{i=0}^{b−1} f (S a + i) == Σ_{i=0}^{b−1} f (a + i)%nat − f a + f (a+b)
   ——归纳于 b（sum_upto_add 的基础） *)
Lemma sum_upto_shift1 : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto b (fun i => f (Datatypes.S a + i)%nat) ) (
  sum_upto b (fun i => f (a + i)%nat) - f a + f (a + b)%nat).
Proof.
  intros a b f.
  apply qeq_imp_qeqT.
  induction b as [| b' IH].
  - (* b = 0：0 == 0 − f a + f (a+0)——a+0 == a（lia） *)
    assert (Hz : (a + 0 = a)%nat) by lia.
    rewrite Hz.
    change (sum_upto 0 (fun i : nat => f (Datatypes.S a + i)%nat)) with 0.
    change (sum_upto 0 (fun i : nat => f (a + i)%nat)) with 0.
    ring.
  - (* b = S b'：sum_upto (S b') (fun i => f (S a + i)) = sum_upto b' ... + f (S a + b') *)
    change (sum_upto b' (fun i => f (Datatypes.S a + i)%nat) + f (Datatypes.S a + b')%nat ==
            sum_upto (Datatypes.S b') (fun i => f (a + i)%nat) - f a + f (a + Datatypes.S b')%nat).
    setoid_rewrite IH.
    (* sum_upto (S b') (fun i => f (a+i)) = sum_upto b' (fun i => f (a+i)) + f (a + b')%nat *)
    change (sum_upto (Datatypes.S b') (fun i => f (a + i)%nat)) with
      (sum_upto b' (fun i => f (a + i)%nat) + f (a + b')%nat).
    (* 归约 S a + b' == S (a + b')、a + S b' == S (a + b') *)
    assert (H1 : (Datatypes.S a + b' = Datatypes.S (a + b'))%nat) by lia.
    rewrite H1.
    assert (H2 : (a + Datatypes.S b' = Datatypes.S (a + b'))%nat) by lia.
    rewrite H2.
    ring.
Qed.

(* 分段：Σ_{i=0}^{a+b−1} f i == Σ_{i=0}^{a−1} f i + Σ_{i=0}^{b−1} f (a + i)%nat——归纳于 a *)
Lemma sum_upto_add : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto (a + b) f ) ( sum_upto a f + sum_upto b (fun i => f (a + i)%nat)).
Proof.
  intros a b f.
  apply qeq_imp_qeqT.
  induction a as [| a' IH].
  - simpl. change (sum_upto b (fun i : nat => f i)) with (sum_upto b f). ring.
  - (* a = S a'：S a' + b == S (a' + b) *)
    assert (Had : (Datatypes.S a' + b = Datatypes.S (a' + b))%nat) by lia.
    rewrite Had.
    change (sum_upto (Datatypes.S (a' + b)) f ==
            sum_upto (Datatypes.S a') f + sum_upto b (fun i => f (Datatypes.S a' + i)%nat)).
    change (sum_upto (a' + b) f + f (a' + b)%nat ==
            sum_upto a' f + f a'%nat + sum_upto b (fun i => f (Datatypes.S a' + i)%nat)).
    setoid_rewrite IH.
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift1 a' b f)).
    ring.
Qed.

(* ============ min 版三角形换序引理族（备份 87 并入，来自 _dbg_kdr.v） ============ *)

(* sum_upto 参数 Leibniz 重写 + 按 j 分段（N == (N−m+1)+(m−1)——f 是参数故安全） *)
Lemma sum_upto_nat_eq : forall (n m : nat) (f : nat -> Q), n = m ->QeqT ( sum_upto n f ) ( sum_upto m f).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

(* ============ 配对论证：corr 差分行展开（备份 90 并入，来自 _dbg_kdr.v） ============ *)

Lemma esq_row_sum_upto : forall (N i : nat) (a : Q),QeqT (
  esq_row N i a ) (
  sum_upto (i + 1) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j)))).
Proof.
  intros N i a.
  apply qeq_imp_qeqT.
  induction i as [| i' IH].
  - (* i=0：esq_row N 0 == q_pow a (2N)/((2N)!·0!)；sum_upto 1 f == f 0 *)
    change (esq_row N 0 a) with (q_pow a (2 * N) / (q_fact (2 * N) * q_fact 0)).
    (* sum_upto (0+1) f == sum_upto 0 f + f 0 == 0 + f 0——simpl 展开 + ring *)
    assert (Hs : sum_upto (0 + 1) (fun j : nat => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) ==
                 q_pow a (2 * N + 2 * 0) / (q_fact (2 * N) * q_fact (2 * 0))).
    { simpl. ring. }
    rewrite Hs.
    assert (Hz : (2 * N + 2 * 0 = 2 * N)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * 0)) with (q_pow a (2 * N)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * N + 2 * 0)%nat (2 * N)%nat Hz). }
    change (q_fact (2 * 0)) with (q_fact 0).
    reflexivity.
  - (* i = S i'：esq_row N (S i') == esq_row N i' + q_pow a (2N+2·S i')/((2N)!(2·S i)!) *)
    change (esq_row N (Datatypes.S i') a) with
      (esq_row N i' a + q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i'))).
    (* sum_upto (S i' + 1) f == sum_upto (i' + 1) f + f (i' + 1) *)
    assert (Hsu : (Datatypes.S i' + 1 = Datatypes.S (i' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S i' + 1) (Datatypes.S (i' + 1))
              (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) Hsu)).
    change (sum_upto (Datatypes.S (i' + 1)) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j)))) with
      (sum_upto (i' + 1) (fun j => q_pow a (2 * N + 2 * j) / (q_fact (2 * N) * q_fact (2 * j))) +
       q_pow a (2 * N + 2 * (i' + 1)) / (q_fact (2 * N) * q_fact (2 * (i' + 1)))).
    setoid_rewrite IH.
    (* 归约尾项索引：2·S i' == 2·(i'+1)（q_pow/q_fact）——先 assert 尾项等式再 rewrite *)
    assert (Hp : (2 * Datatypes.S i' = 2 * (i' + 1))%nat) by lia.
    assert (Htail : q_pow a (2 * N + 2 * Datatypes.S i') / (q_fact (2 * N) * q_fact (2 * Datatypes.S i')) ==
                    q_pow a (2 * N + 2 * (i' + 1)) / (q_fact (2 * N) * q_fact (2 * (i' + 1)))).
    { assert (Hp1 : (2 * N + 2 * Datatypes.S i' = 2 * N + 2 * (i' + 1))%nat) by lia.
      setoid_rewrite (q_pow_comp_proper a a (Qeq_refl a)
                        (2 * N + 2 * Datatypes.S i')%nat (2 * N + 2 * (i' + 1))%nat Hp1).
      setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_nat_eq (2 * Datatypes.S i') (2 * (i' + 1)) Hp)).
      reflexivity. }
    setoid_rewrite Htail.
    reflexivity.
Qed.

Lemma osq_row_sum_upto : forall (N i : nat) (a : Q),QeqT (
  osq_row N i a ) (
  sum_upto (i + 1) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1)))).
Proof.
  intros N i a.
  apply qeq_imp_qeqT.
  induction i as [| i' IH].
  - (* i=0：osq_row N 0 == q_pow a (2N+2)/((2N+1)!·1!)；sum_upto 1 f == f 0 *)
    change (osq_row N 0 a) with (q_pow a (2 * N + 2) / (q_fact (2 * N + 1) * q_fact 1)).
    assert (Hs : sum_upto (0 + 1) (fun j : nat => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) ==
                 q_pow a (2 * N + 2 * 0 + 2) / (q_fact (2 * N + 1) * q_fact (2 * 0 + 1))).
    { simpl. ring. }
    rewrite Hs.
    assert (Hz : (2 * N + 2 * 0 + 2 = 2 * N + 2)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * 0 + 2)) with (q_pow a (2 * N + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * N + 2 * 0 + 2)%nat (2 * N + 2)%nat Hz). }
    assert (Hf : (2 * 0 + 1 = 1)%nat) by lia.
    setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity.
  - change (osq_row N (Datatypes.S i') a) with
      (osq_row N i' a + q_pow a (2 * N + 2 * Datatypes.S i' + 2) / (q_fact (2 * N + 1) * q_fact (2 * Datatypes.S i' + 1))).
    assert (Hsu : (Datatypes.S i' + 1 = Datatypes.S (i' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S i' + 1) (Datatypes.S (i' + 1))
              (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) Hsu)).
    change (sum_upto (Datatypes.S (i' + 1)) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1)))) with
      (sum_upto (i' + 1) (fun j => q_pow a (2 * N + 2 * j + 2) / (q_fact (2 * N + 1) * q_fact (2 * j + 1))) +
       q_pow a (2 * N + 2 * (i' + 1) + 2) / (q_fact (2 * N + 1) * q_fact (2 * (i' + 1) + 1))).
    setoid_rewrite IH.
    assert (Hp : (2 * N + 2 * Datatypes.S i' + 2 = 2 * N + 2 * (i' + 1) + 2)%nat) by lia.
    setoid_replace (q_pow a (2 * N + 2 * Datatypes.S i' + 2))
      with (q_pow a (2 * N + 2 * (i' + 1) + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * N + 2 * Datatypes.S i' + 2)%nat (2 * N + 2 * (i' + 1) + 2)%nat Hp). }
    assert (Hf : (2 * Datatypes.S i' + 1 = 2 * (i' + 1) + 1)%nat) by lia.
    setoid_replace (q_fact (2 * Datatypes.S i' + 1)) with (q_fact (2 * (i' + 1) + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity.
Qed.

Lemma inner2_expand : forall (a : Q) (N i : nat), (1 <= i)%nat ->QeqT (
  inner2 N i a ) (
  - 2 * esq_row (Datatypes.S N) i a
  + 2 * osq_row N (i - 1) a
  + 2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))).
Proof.
  intros a N i Hi.
  apply qeq_imp_qeqT.
  assert (Hr := qeqT_imp_qeq _ _ (rows_vs_inner_i a N i Hi)).
  (* Hr : −inner2 == 2esq − 2osq − 2T；目标 inner2 == −2esq + 2osq + 2T
     两侧取负：inner2 == −(2esq−2osq−2T))（用 Qeq_sym Hr 换 X，再 ring 归约） *)
  assert (Hopp : - (2 * esq_row (Datatypes.S N) i a
                    - 2 * osq_row N (i - 1) a
                    - 2 * q_pow a (2 * N + 2 * i + 2) / (q_fact (2 * N + 2) * q_fact (2 * i))) ==
                 inner2 N i a).
  { apply Qeq_sym.
    (* 目标：inner2 N i a == −(2esq−2osq−2T)——即 inner2 == −X。用 Hr 反向换 X *)
    setoid_rewrite <- Hr.  (* 目标中 −X 的 X → 2esq−2osq−2T？不——目标是 inner2 == −X *)
    ring. }
  setoid_rewrite <- Hopp.
  ring.
Qed.

Lemma corr_diff_expand : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  sum_upto m
    (fun k' =>
       - 2 * esq_row (m + 2 + k') (m + 1 - k') a
       + 2 * esq_row (m + 1 + k') (m - k') a
       + 2 * osq_row (m + 1 + k') (m - k') a
       - 2 * osq_row (m + k') (m - k' - 1) a
       + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
       - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k')))
  - 2 * esq_row (2 * m + 2) 1 a
  + 2 * osq_row (2 * m + 1) 0 a
  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* corr 差分 == ksum_diff m m + inner2 (2m+1) 1（corr_succ_decomp 反向 + 索引归约） *)
  assert (Hdec : corr (Datatypes.S m) a - corr m a ==
                 ksum_diff m m a + inner2 (2 * m + 1) 1 a).
  { assert (Hd2 : corr (Datatypes.S m) a - corr m a ==
                  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a).
    { apply qeqT_imp_qeq. apply (corr_succ_decomp a m Hm). }
    assert (Hj : (2 * Datatypes.S m - (2 * m + 1) = 1)%nat) by lia.
    setoid_replace (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a)
      with (inner2 (2 * m + 1) 1 a) in Hd2.
    2: { change (inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ==
                 inner2 (2 * m + 1) 1 a).
         rewrite Hj. reflexivity. }
    exact Hd2. }
  rewrite Hdec.
  (* ksum_diff m m == sum_upto m (inner2 (m+1+k') (m+1−k') − inner2 (m+k') (m−k'))（step4） *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_row_step4 a m Hm)).
  (* ext_below：逐 k' 用 rows_vs_inner_i 展开两个 inner2 *)
  rewrite (fun Hprm => qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun k' => inner2 (m + 1 + k') (m + 1 - k') a - inner2 (m + k') (m - k') a) (fun k' => - 2 * esq_row (m + 2 + k') (m + 1 - k') a + 2 * esq_row (m + 1 + k') (m - k') a + 2 * osq_row (m + 1 + k') (m - k') a - 2 * osq_row (m + k') (m - k' - 1) a + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k')) - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))) Hprm)).
  2: {
    intros k' Hk'. apply NatLe_drop in Hk'.
    apply qeq_imp_qeqT.
    (* rows_vs_inner_i：−inner2 N i == 2·esq_row (S N) i − 2·osq_row N (i−1) − 2T
       取反：inner2 N i == −2·esq_row (S N) i + 2·osq_row N (i−1) + 2T *)
    (* inner2 (m+1+k') (m+1−k')：N=m+1+k'，i=m+1−k' *)
    assert (Hr1 : inner2 (m + 1 + k') (m + 1 - k') a ==
                  - 2 * esq_row (m + 2 + k') (m + 1 - k') a
                  + 2 * osq_row (m + 1 + k') (m - k') a
                  + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))).
    { (* inner2_expand 于 N=m+1+k'、i=m+1−k'——正向 setoid_rewrite（LHS==RHS 形式） *)
      assert (Hi1 : (1 <= m + 1 - k')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (m + 1 + k') (m + 1 - k') Hi1)).
      (* 归约 esq_row 第一参数：S (m+1+k') == m+2+k'；osq_row 第二参数：m+1−k'−1 == m−k' *)
      assert (Hse : (Datatypes.S (m + 1 + k') = m + 2 + k')%nat) by lia.
      setoid_replace (esq_row (Datatypes.S (m + 1 + k')) (m + 1 - k') a)
        with (esq_row (m + 2 + k') (m + 1 - k') a).
      2: { change (esq_row (Datatypes.S (m + 1 + k')) (m + 1 - k') a ==
                   esq_row (m + 2 + k') (m + 1 - k') a).
           rewrite Hse. reflexivity. }
      assert (Hso : (m + 1 - k' - 1 = m - k')%nat) by lia.
      setoid_replace (osq_row (m + 1 + k') (m + 1 - k' - 1) a)
        with (osq_row (m + 1 + k') (m - k') a).
      2: { change (osq_row (m + 1 + k') (m + 1 - k' - 1) a ==
                   osq_row (m + 1 + k') (m - k') a).
           rewrite Hso. reflexivity. }
      (* q_pow 指数：2N+2i+2 == 4m+6；分母 (2N+2)!(2i)! == (2m+2k'+4)!(2m+2−2k')! *)
      assert (Hp : (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2 = 4 * m + 6)%nat) by lia.
      setoid_replace (q_pow a (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2))
        with (q_pow a (4 * m + 6)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * (m + 1 + k') + 2 * (m + 1 - k') + 2)%nat (4 * m + 6)%nat Hp). }
      assert (Hf1 : (2 * (m + 1 + k') + 2 = 2 * m + 2 * k' + 4)%nat) by lia.
      assert (Hf2 : (2 * (m + 1 - k') = 2 * m + 2 - 2 * k')%nat) by lia.
      setoid_replace (q_fact (2 * (m + 1 + k') + 2)) with (q_fact (2 * m + 2 * k' + 4)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * (m + 1 - k'))) with (q_fact (2 * m + 2 - 2 * k')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      ring. }
    (* inner2 (m+k') (m−k')：N=m+k'，i=m−k' *)
    assert (Hr2 : inner2 (m + k') (m - k') a ==
                  - 2 * esq_row (m + 1 + k') (m - k') a
                  + 2 * osq_row (m + k') (m - k' - 1) a
                  + 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))).
    { assert (Hi2 : (1 <= m - k')%nat) by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (m + k') (m - k') Hi2)).
      assert (Hse : (Datatypes.S (m + k') = m + 1 + k')%nat) by lia.
      setoid_replace (esq_row (Datatypes.S (m + k')) (m - k') a)
        with (esq_row (m + 1 + k') (m - k') a).
      2: { change (esq_row (Datatypes.S (m + k')) (m - k') a ==
                   esq_row (m + 1 + k') (m - k') a).
           rewrite Hse. reflexivity. }
      assert (Hp : (2 * (m + k') + 2 * (m - k') + 2 = 4 * m + 2)%nat) by lia.
      setoid_replace (q_pow a (2 * (m + k') + 2 * (m - k') + 2))
        with (q_pow a (4 * m + 2)).
      2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                   (2 * (m + k') + 2 * (m - k') + 2)%nat (4 * m + 2)%nat Hp). }
      assert (Hf1 : (2 * (m + k') + 2 = 2 * m + 2 * k' + 2)%nat) by lia.
      assert (Hf2 : (2 * (m - k') = 2 * m - 2 * k')%nat) by lia.
      setoid_replace (q_fact (2 * (m + k') + 2)) with (q_fact (2 * m + 2 * k' + 2)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      setoid_replace (q_fact (2 * (m - k'))) with (q_fact (2 * m - 2 * k')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      ring. }
    (* 目标：inner2 A − inner2 B == 行差(k')——rewrite Hr1 Hr2 后 ring *)
    setoid_rewrite Hr1. setoid_rewrite Hr2.
    ring. }
  (* 尾项：inner2 (2m+1) 1 用 rows_vs_inner_i 展开 *)
  assert (Htail : inner2 (2 * m + 1) 1 a ==
                  - 2 * esq_row (2 * m + 2) 1 a
                  + 2 * osq_row (2 * m + 1) 0 a
                  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
  { assert (Hi3 : (1 <= 1)%nat) by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (inner2_expand a (2 * m + 1) 1 Hi3)).
    assert (Hse : (Datatypes.S (2 * m + 1) = 2 * m + 2)%nat) by lia.
    setoid_replace (esq_row (Datatypes.S (2 * m + 1)) 1 a)
      with (esq_row (2 * m + 2) 1 a).
    2: { change (esq_row (Datatypes.S (2 * m + 1)) 1 a == esq_row (2 * m + 2) 1 a).
         rewrite Hse. reflexivity. }
    setoid_replace (osq_row (2 * m + 1) (1 - 1) a)
      with (osq_row (2 * m + 1) 0 a).
    2: { change (osq_row (2 * m + 1) (1 - 1) a == osq_row (2 * m + 1) 0 a).
         simpl. reflexivity. }
    assert (Hp : (2 * (2 * m + 1) + 2 * 1 + 2 = 4 * m + 6)%nat) by lia.
    setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * 1 + 2))
      with (q_pow a (4 * m + 6)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a)
                 (2 * (2 * m + 1) + 2 * 1 + 2)%nat (4 * m + 6)%nat Hp). }
    assert (Hf1 : (2 * (2 * m + 1) + 2 = 4 * m + 4)%nat) by lia.
    assert (Hf2 : (2 * 1 = 2)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1) + 2)) with (q_fact (4 * m + 4)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * 1)) with (q_fact 2).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    ring. }
  (* transitivity：LHS（sum_upto + inner2 尾项）== sum_upto + RHS_tail == 目标 RHS *)
  transitivity (sum_upto m
    (fun k' =>
       - 2 * esq_row (m + 2 + k') (m + 1 - k') a
       + 2 * esq_row (m + 1 + k') (m - k') a
       + 2 * osq_row (m + 1 + k') (m - k') a
       - 2 * osq_row (m + k') (m - k' - 1) a
       + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
       - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k')))
    - 2 * esq_row (2 * m + 2) 1 a
    + 2 * osq_row (2 * m + 1) 0 a
    + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2)).
  - (* LHS == 中间项：setoid_rewrite Htail 于 LHS 的 inner2 尾项 + ring（结合重排） *)
    setoid_rewrite Htail.
    ring.
  - reflexivity.
Qed.

Lemma sum_upto_split : forall (m N : nat) (f : nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto N f ) ( sum_upto (N - m + 1) f + sum_upto (m - 1) (fun j => f (N - m + 1 + j)%nat)).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  assert (Hadd : ((N - m + 1) + (m - 1) = N)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq N ((N - m + 1) + (m - 1)) f (eq_sym Hadd))).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_add (N - m + 1) (m - 1) f)).
  reflexivity.
Qed.

(* min 归约：j ≤ N−m 时 min(m−1, N−S j) = m−1；j > N−m 时 min = N−S j *)
Lemma min_lower : forall (m N j : nat), (1 <= m)%nat -> (m <= N)%nat -> (j <= N - m)%nat ->
  Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) (m - 1)%nat.
Proof.
  intros m N j Hm Hmn Hj.
  assert (Hle : ((m - 1) <= (N - Datatypes.S j))%nat) by lia.
  exact (eq_rect (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)
                 (fun z : nat => Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) z)
                 (@id_refl nat (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))
                 (m - 1)%nat
                 (Nat.min_l _ _ Hle)).
Qed.

Lemma min_upper : forall (m N j : nat), (1 <= m)%nat -> (m <= N)%nat -> (N - m < j)%nat ->
  Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) (N - Datatypes.S j)%nat.
Proof.
  intros m N j Hm Hmn Hj.
  assert (Hle : ((N - Datatypes.S j) <= (m - 1))%nat) by lia.
  exact (eq_rect (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)
                 (fun z : nat => Id (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) z)
                 (@id_refl nat (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))
                 (N - Datatypes.S j)%nat
                 (Nat.min_r _ _ Hle)).
Qed.

(* 逐列补齐：完整列 == min 列 + 补齐列（sum_upto_add + min 恒等——无 case） *)
Lemma sum_upto_min_pad : forall (m N j : nat) (f : nat -> Q),
  (j < N)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (N - Datatypes.S j + 1) f ) (
  sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1) f +
  sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
           (fun i => f ((Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1) + i)%nat)).
Proof.
  intros m N j f Hj Hm.
  apply qeq_imp_qeqT.
  assert (Hsum : (N - Datatypes.S j + 1 =
                  Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 +
                  (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat))%nat) by lia.
  rewrite Hsum.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_add (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)                     (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat) f)).
  reflexivity.
Qed.

(* 超额按列 == 尾行：Σ_j 补齐_j == Σ_{i=0}^{N−m−1} Σ_{j=1}^{N−m−i} f (m+i) j
   ——sum_upto_split 分段（j≤N−m 与 j>N−m）+ min 归约 + tri_swap_std（n=N−m 平移，反向） *)
Lemma excess_col_tail : forall (m N : nat) (f : nat -> nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto N (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                               (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) ) (
  sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_split m N           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j)))           Hm Hmn)).
  assert (Hpre1538_47 : (forall i : nat, NatLe (Datatypes.S i) (N - m + 1) ->QeqT ( (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) i ) ( (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat                              (fun i => f (m + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj.
     apply NatLe_drop in Hj.
       apply qeq_imp_qeqT.
       assert (Hjle : (j <= N - m)%nat) by lia.
       destruct (id_sym (min_lower m N j Hm Hmn Hjle)).
       apply qeqT_imp_qeq.
       apply (sum_upto_ext (N - Datatypes.S j - (m - 1))%nat
              (fun i => f (m - 1 + 1 + i)%nat (Datatypes.S j)) (fun i => f (m + i)%nat (Datatypes.S j))).
       intro i. apply qeq_imp_qeqT. assert (Hx : (m - 1 + 1 + i = m + i)%nat) by lia. rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m + 1)           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j)))
           (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat                              (fun i => f (m + i)%nat (Datatypes.S j))) Hpre1538_47)).
  assert (Hpre1538_46 : (forall i,QeqT ( (fun j => sum_upto (N - Datatypes.S (N - m + 1 + j) - Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat)%nat (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat + 1 + i)%nat (Datatypes.S (N - m + 1 + j)))) i ) ( (fun _ => 0) i))).
  {  intro j.
       apply qeq_imp_qeqT.
       assert (Hjg : (N - m < N - m + 1 + j)%nat) by lia.
       destruct (id_sym (min_upper m N (N - m + 1 + j) Hm Hmn Hjg)).
       assert (Hz : (N - Datatypes.S (N - m + 1 + j) - (N - Datatypes.S (N - m + 1 + j)) = 0)%nat) by lia.
       rewrite Hz.
       simpl. ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m - 1)           (fun j => sum_upto (N - Datatypes.S (N - m + 1 + j) - Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat)%nat
                             (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S (N - m + 1 + j))%nat + 1 + i)%nat (Datatypes.S (N - m + 1 + j))))           (fun _ => 0) Hpre1538_46)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_zero _)).
  assert (Hsm : (N - m + 1 = Datatypes.S (N - m))%nat) by lia.
  rewrite Hsm.
  change (sum_upto (Datatypes.S (N - m)) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat
                                                        (fun i => f (m + i)%nat (Datatypes.S j)))) with
    (sum_upto (N - m) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat
                                          (fun i => f (m + i)%nat (Datatypes.S j))) +
     sum_upto (N - Datatypes.S (N - m) - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S (N - m)))).
  assert (Hz : (N - Datatypes.S (N - m) - (m - 1) = 0)%nat) by lia.
  rewrite Hz.
  simpl.
  assert (Hpre1538_102 : (forall i : nat, NatLe (Datatypes.S i) (N - m) ->QeqT ( (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S j))) i ) ( (fun j => sum_upto (N - m - Datatypes.S j + 1) (fun i => f (m + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. assert (Hx : (N - Datatypes.S j - (m - 1) = N - m - Datatypes.S j + 1)%nat) by lia.
       rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m) (fun j => sum_upto (N - Datatypes.S j - (m - 1))%nat (fun i => f (m + i)%nat (Datatypes.S j))) (fun j => sum_upto (N - m - Datatypes.S j + 1) (fun i => f (m + i)%nat (Datatypes.S j))) Hpre1538_102)).
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_tri_swap_std (N - m) (fun i j => f (m + i)%nat j))).
  change (sum_upto (N - m)
            (fun i => sum_upto (N - m - i) (fun j => f (m + i)%nat (Datatypes.S j))) + 0 + 0 ==
          sum_upto (N - m) (fun i => sum_upto (N - m - i) (fun j => f (m + i)%nat (Datatypes.S j)))).
  ring.
Qed.

(* min 版三角形换序（补全法）：截断 LHS == min RHS
   ——截断+尾行==完整 LHS（sum_upto_add）→ tri_swap_std(n=N) → 完整 RHS==min RHS+Σ补齐
   （ext_below 逐列 + sum_upto_min_pad）→ Σ补齐==尾行（excess_col_tail） *)
Lemma sum_upto_tri_swap_min : forall (m N : nat) (f : nat -> nat -> Q),
  (1 <= m)%nat -> (m <= N)%nat ->QeqT (
  sum_upto m (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) ) (
  sum_upto N (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)))).
Proof.
  intros m N f Hm Hmn.
  apply qeq_imp_qeqT.
  setoid_replace (sum_upto m (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))))
    with (sum_upto N (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) -
          sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
  2: { assert (Hadd : (m + (N - m) = N)%nat) by lia.
       rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq N (m + (N - m)) (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))) (eq_sym Hadd))).
       setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add m (N - m) (fun i => sum_upto (N - i)%nat (fun j => f i (Datatypes.S j))))).
       assert (Hpre1538_101 : (forall i : nat, NatLe (Datatypes.S i) (N - m) ->QeqT ( (fun i => sum_upto (N - (m + i))%nat (fun j => f (m + i)%nat (Datatypes.S j))) i ) ( (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j))) i))).
       {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hx : (N - (m + i) = N - m - i)%nat) by lia.
            rewrite Hx. reflexivity. }
       rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (N - m) (fun i => sum_upto (N - (m + i))%nat (fun j => f (m + i)%nat (Datatypes.S j))) (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j))) Hpre1538_101)).
       ring. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_std N f)).
  assert (Hpre1538_45 : (forall i : nat, NatLe (Datatypes.S i) N ->QeqT ( (fun j => sum_upto (N - Datatypes.S j + 1)%nat (fun i => f i (Datatypes.S j))) i ) ( (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)) + sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) i))).
  {  intros j Hj.
       apply qeq_imp_qeqT.
       apply qeqT_imp_qeq.
       apply (sum_upto_min_pad m N j (fun i => f i (Datatypes.S j))).
       - exact (NatLe_drop (Datatypes.S j) N Hj). - exact Hm. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below N           (fun j => sum_upto (N - Datatypes.S j + 1)%nat (fun i => f i (Datatypes.S j)))
           (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)) +
                     sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))) Hpre1538_45)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus N           (fun j => sum_upto (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1)%nat (fun i => f i (Datatypes.S j)))
           (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat                              (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))))).
  setoid_replace (sum_upto N (fun j => sum_upto (N - Datatypes.S j - Nat.min (m - 1)%nat (N - Datatypes.S j)%nat)%nat
                                            (fun i => f (Nat.min (m - 1)%nat (N - Datatypes.S j)%nat + 1 + i)%nat (Datatypes.S j))))
    with (sum_upto (N - m)%nat (fun i => sum_upto (N - m - i)%nat (fun j => f (m + i)%nat (Datatypes.S j)))).
  2: { apply qeqT_imp_qeq. apply (excess_col_tail m N f Hm Hmn). }
  ring.
Qed.

(* ============ c1 逐列配对族（备份 88 并入，来自 _dbg_kdr.v）：c1 = ksum_diff (S m) m 展开配对 ============ *)

(* 负/差线性：sum_upto 对 - 与 -（c1 的 LHS 拆第一第二和需要） *)
Lemma sum_upto_neg : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun i => - f i) ) ( - sum_upto n f).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. setoid_rewrite IH. ring.
Qed.

Lemma sum_upto_minus : forall (n : nat) (f g : nat -> Q),QeqT (
  sum_upto n (fun i => f i - g i) ) ( sum_upto n f - sum_upto n g).
Proof.
  intros n f g.
  apply qeq_imp_qeqT.
  change (sum_upto n (fun i => f i + - g i) == sum_upto n f - sum_upto n g).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus n f (fun i => - g i))).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_neg n g)).
  ring.
Qed.

(* 列右移：Σ_{i=0}^{ub−1} brk2 (k+1+i) j == Σ_{i=0}^{ub} brk2 (k+i) j − brk2 k j（c1 逐列配对核心） *)
Lemma col_shift_right : forall (k j ub : nat) (a : Q),QeqT (
  sum_upto ub (fun i => brk2 (k + 1 + i) j a) ) (
  sum_upto (ub + 1) (fun i => brk2 (k + i) j a) - brk2 k j a).
Proof.
  intros k j ub a.
  apply qeq_imp_qeqT.
  assert (Hadd : (1 + ub = ub + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (ub + 1) (1 + ub) (fun i => brk2 (k + i) j a) (eq_sym Hadd))).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 1 ub (fun i => brk2 (k + i) j a))).
  simpl.
  assert (Hpre1538_44 : (forall i : nat, NatLe (Datatypes.S i) ub ->QeqT ( (fun i => brk2 (k + (1 + i)) j a) i ) ( (fun i => brk2 (k + 1 + i) j a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hx : (k + (1 + i) = k + 1 + i)%nat) by lia. rewrite Hx. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below ub           (fun i => brk2 (k + (1 + i)) j a) (fun i => brk2 (k + 1 + i) j a) Hpre1538_44)).
  assert (Hz : (k + 0 = k)%nat) by lia.
  rewrite Hz.
  ring.
Qed.

(* 列左移（col_shift_right 的逆）：Σ_{i=0}^{ub} brk2 (k+i) j == brk2 k j + Σ_{i=0}^{ub−1} brk2 (k+1+i) j *)
Lemma col_shift_left : forall (k j ub : nat) (a : Q),QeqT (
  sum_upto (ub + 1) (fun i => brk2 (k + i) j a) ) (
  brk2 k j a + sum_upto ub (fun i => brk2 (k + 1 + i) j a)).
Proof.
  intros k j ub a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (col_shift_right k j ub a)).
  ring.
Qed.

(* Q 环重排通用引理（ring 于变量——c1_col_mid 的 by ring 于 Fixpoint 原子不可靠的绕过） *)
Lemma q_ring_reorder : forall (X A B C : Q),QeqT ( X + A - B + C ) ( A + C - B + X).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

Lemma q_ring_reorder2 : forall (X A B C : Q),QeqT ( A + C - B + X ) ( X + A + C - B).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

Lemma q_ring_reorder3 : forall (X B C : Q),QeqT ( X - B + C ) ( X + C - B).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* c1 逐列配对（段 1a：j ≤ 1——min 都 = m−1）：第一列 == 第二列 + brk2 (2m+1) (S j) − brk2 (m+1) (S j) *)
Lemma c1_col_lo_shift : forall (m j : nat) (a : Q), (j <= 1)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)
  ) ( sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)
     + brk2 (2 * m + 1) (Datatypes.S j) a - brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hj1 Hm.
  apply qeq_imp_qeqT.
  assert (Hmin1 : (Nat.min (m - 1) (m + 2 - Datatypes.S j) = m - 1)%nat) by (apply Nat.min_l; lia).
  assert (Hmin2 : (Nat.min (m - 1) (m + 1 - Datatypes.S j) = m - 1)%nat) by (apply Nat.min_l; lia).
  rewrite Hmin1. rewrite Hmin2.
  (* 第一列 = sum_upto m（m−1+1 == m）——拆尾项 brk2 (2m+1) *)
  assert (Hup1 : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hup1.
  (* sum_upto m == sum_upto (m−1) + 尾项（m == S(m−1)？——m ≥ 1——m = S(m−1) lia） *)
  assert (Hm1 : (m = Datatypes.S (m - 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) Hm1)).
  change (sum_upto (Datatypes.S (m - 1)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) with
    (sum_upto (m - 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) +
     brk2 (m + 2 + (m - 1)) (Datatypes.S j) a).
  assert (Hk : (m + 2 + (m - 1) = 2 * m + 1)%nat) by lia.
  rewrite Hk.
  (* col_shift_right 于 k=m+1、ub=m−1（先 ext_below 归约 brk2 参数 m+2+i == m+1+1+i） *)
  assert (Hpre1538_43 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) i ) ( (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hnat : (m + 2 + i = m + 1 + 1 + i)%nat) by lia. rewrite Hnat. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)           (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)           (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) Hpre1538_43)).
  setoid_rewrite (qeqT_imp_qeq _ _ (col_shift_right (m + 1) (Datatypes.S j) (m - 1) a)).
  (* 第二列参数归约：m−1+1 == m *)
  assert (Hup2 : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hup2.
  apply (qeqT_imp_qeq _ _ (q_ring_reorder3 (sum_upto m (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))           (brk2 (m + 1) (Datatypes.S j) a)           (brk2 (2 * m + 1) (Datatypes.S j) a))).
Qed.

(* c1 逐列配对（段 2：j = m+1——第一列 == 补充项列 brk2 (m+2) (m+2)） *)
Lemma c1_col_hi : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S (m + 1)) a)
  ) ( brk2 (m + 2) (m + 2) a).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  (* S(m+1) == m+2——lia 归约（sum_upto 参数） *)
  assert (Hsm : (Datatypes.S (m + 1) = m + 2)%nat) by lia.
  (* min(m−1, m+2−(m+2)) = 0 *)
  assert (Hmin : (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) = 0)%nat).
  { rewrite Hsm. lia. }
  (* rewrite Hmin 于 sum_upto 参数：min 子项 -> 0，参数成 0+1 *)
  rewrite Hmin.
  (* simpl 展开 sum_upto (0+1) = brk2 (m+2+0) (S(m+1)) *)
  simpl.
  (* brk2 第二参数 S(m+1) -> m+2 *)
  rewrite Hsm.
  (* brk2 第一参数 m+2+0 -> m+2 *)
  assert (Hz : (m + 2 + 0 = m + 2)%nat) by lia.
  rewrite Hz.
  ring.
Qed.

(* c1 逐列配对（段 1b：2 ≤ j ≤ m）：第一列 == 第二列 + 补充项列 − brk2 (m+1) (S j)
   ——min 归约 + col_shift_right（尾项 == 补充项列） *)
Lemma c1_col_mid : forall (m j : nat) (a : Q), (2 <= j)%nat -> (j <= m)%nat -> (1 <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)
  ) ( sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)
     + brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a
     + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a
     - brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hj2 Hjm Hm.
  apply qeq_imp_qeqT.
  assert (Hmin1 : (Nat.min (m - 1) (m + 2 - Datatypes.S j) = m + 2 - Datatypes.S j)%nat) by (apply Nat.min_r; lia).
  assert (Hmin2 : (Nat.min (m - 1) (m + 1 - Datatypes.S j) = m + 1 - Datatypes.S j)%nat) by (apply Nat.min_r; lia).
  rewrite Hmin1. rewrite Hmin2.
  (* 第一列 = sum_upto (m+2−S j+1)——拆尾项 brk2 (2m+4−S j) *)
  (* m+2−S j+1 与 S(m+2−S j)——lia 归约 *)
  assert (Hsucc : (m + 2 - Datatypes.S j + 1 = Datatypes.S (m + 2 - Datatypes.S j))%nat) by lia.
  rewrite Hsucc.
  change (sum_upto (Datatypes.S (m + 2 - Datatypes.S j)) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) with
    (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) +
     brk2 (m + 2 + (m + 2 - Datatypes.S j)) (Datatypes.S j) a).
  (* 尾项 k = m+2+m+2−S j = 2m+4−S j——lia 归约 *)
  assert (Hk : (m + 2 + (m + 2 - Datatypes.S j) = 2 * m + 4 - Datatypes.S j)%nat) by lia.
  rewrite Hk.
  (* col_shift_right 于 k=m+1、ub=m+2−S j *)
  assert (Hpre1538_42 : (forall i : nat, NatLe (Datatypes.S i) (m + 2 - Datatypes.S j) ->QeqT ( (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) i ) ( (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) i))).
  {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. assert (Hnat : (m + 2 + i = m + 1 + 1 + i)%nat) by lia. rewrite Hnat. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m + 2 - Datatypes.S j)           (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)           (fun i => brk2 (m + 1 + 1 + i) (Datatypes.S j) a) Hpre1538_42)).
  setoid_rewrite (qeqT_imp_qeq _ _ (col_shift_right (m + 1) (Datatypes.S j) (m + 2 - Datatypes.S j) a)).
  (* sum_upto (m+3−S j) (fun i => brk2 (m+1+i)) == 第二列 + brk2 (2m+3−S j)——拆尾项 *)
  setoid_replace (sum_upto (m + 2 - Datatypes.S j + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
    with (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
          brk2 (m + 1 + (m + 2 - Datatypes.S j)) (Datatypes.S j) a).
  2: { assert (Hsucc2 : (m + 2 - Datatypes.S j + 1 = Datatypes.S (m + 2 - Datatypes.S j))%nat) by lia.
       rewrite Hsucc2. reflexivity. }
  assert (Hk2 : (m + 1 + (m + 2 - Datatypes.S j) = 2 * m + 3 - Datatypes.S j)%nat) by lia.
  rewrite Hk2.
  (* 第二列：sum_upto (m+1−S j+1)——m+1−S j+1 == m+2−S j（lia 归约） *)
  assert (Hup : (m + 1 - Datatypes.S j + 1 = m + 2 - Datatypes.S j)%nat) by lia.
  rewrite Hup.
  setoid_replace (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
                  brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a - brk2 (m + 1) (Datatypes.S j) a +
                  brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)
    with (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a -
          brk2 (m + 1) (Datatypes.S j) a + sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
    by (apply (qeqT_imp_qeq _ _ (q_ring_reorder (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))                (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a)
                (brk2 (m + 1) (Datatypes.S j) a)
                (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)))).
  apply qeqT_imp_qeq.
  apply (q_ring_reorder2 (sum_upto (m + 2 - Datatypes.S j) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)) (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a) (brk2 (m + 1) (Datatypes.S j) a) (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)).
Qed.

(* 补充行 → 列（supp_col）：Σ_{i=0}^{m−1} [brk2 (m+2+i)(m+1−i) + brk2 (m+2+i)(m+2−i)]
   == Σ_{S=2}^{m+1} brk2 (2m+3−S)(S) + Σ_{S=3}^{m+2} brk2 (2m+4−S)(S)
   ——i 反转换元（sum_upto_rev）：i' = m−1−i，S = i'+2（第一族）/ i'+3（第二族） *)
Lemma supp_col : forall (m : nat) (a : Q),QeqT (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a) ) (
  sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a) +
  sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) (fun i => brk2 (m + 2 + i) (m + 2 - i) a))).
  (* 第一族：Σ_i brk2 (m+2+i)(m+1−i) == Σ_i brk2 (2m+1−i)(i+2)
     ——sum_upto_rev m h 的 h(m−1−i) = brk2 (2m+1−(m−1−i))((m−1−i)+2) == brk2 (m+2+i)(m+1−i) *)
  (* 第一族等式：Σ_i brk2 (m+2+i)(m+1−i) == Σ_i brk2 (2m+1−i)(i+2)
     ——ext_below 换到 rev 形式（i<m 时 2m+1−(m−1−i) == m+2+i）+ sum_upto_rev 归位 *)
  assert (Htmp1 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) ==
                  sum_upto m (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 2) a)).
  { apply qeqT_imp_qeq.
    apply (sum_upto_ext_below m
             (fun i => brk2 (m + 2 + i) (m + 1 - i) a)
             (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 2) a)).
    intros i Hi. apply NatLe_drop in Hi.
    apply qeq_imp_qeqT.
    assert (Ha : (2 * m + 1 - (m - 1 - i) = m + 2 + i)%nat) by lia.
    assert (Hb : ((m - 1 - i) + 2 = m + 1 - i)%nat) by lia.
    rewrite Ha, Hb. reflexivity. }
  assert (H1 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a) ==
               sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_rev m (fun i => brk2 (2 * m + 1 - i) (i + 2) a))) in Htmp1.
    exact Htmp1. }
  (* 第二族等式：Σ_i brk2 (m+2+i)(m+2−i) == Σ_i brk2 (2m+1−i)(i+3) *)
  assert (Htmp2 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 2 - i) a) ==
                  sum_upto m (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 3) a)).
  { apply qeqT_imp_qeq.
  apply (sum_upto_ext_below m             (fun i => brk2 (m + 2 + i) (m + 2 - i) a)             (fun i => brk2 (2 * m + 1 - (m - 1 - i)) ((m - 1 - i) + 3) a)).
    intros i Hi. apply NatLe_drop in Hi.
    apply qeq_imp_qeqT.
    assert (Ha : (2 * m + 1 - (m - 1 - i) = m + 2 + i)%nat) by lia.
    assert (Hb : ((m - 1 - i) + 3 = m + 2 - i)%nat) by lia.
    rewrite Ha, Hb. reflexivity. }
  assert (H2 : sum_upto m (fun i => brk2 (m + 2 + i) (m + 2 - i) a) ==
               sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_rev m (fun i => brk2 (2 * m + 1 - i) (i + 3) a))) in Htmp2.
    exact Htmp2. }
  (* 合并：LHS 已是 sum_upto_plus 拆分形式——直接 rewrite H1 H2 *)
  rewrite H1. rewrite H2.
  reflexivity.
Qed.

(* c1 统一配对：第一列（j 下标，S j 列）== 第二列 + C(j) − brk2 (m+1) (S j)
   ——j ≤ 1 用 lo_shift（C = brk2 (2m+1) (S j)）；2 ≤ j ≤ m 用 mid（C = 两补充项） *)
Lemma c1_col_uni : forall (m j : nat) (a : Q), (1 <= m)%nat -> (j <= m)%nat ->QeqT (
  sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a) ) (
  sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
  (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
   else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -
  brk2 (m + 1) (Datatypes.S j) a).
Proof.
  intros m j a Hm Hjm.
  apply qeq_imp_qeqT.
  assert (Hle1 : (j <= 1)%nat \/ (2 <= j)%nat) by lia.
  destruct Hle1 as [Hj1 | Hj2].
  - (* j ≤ 1：lo_shift，if 分支 true（Nat.leb_le） *)
    assert (Hleb : Nat.leb j 1 = true) by (apply Nat.leb_le; exact Hj1).
    rewrite Hleb.
    apply qeqT_imp_qeq.
    apply (c1_col_lo_shift m j a Hj1 Hm).
  - (* 2 ≤ j：mid，if 分支 false（Nat.leb_gt）——目标 G + (b1+b2) − b3，mid 是 (G+b1)+b2−b3，
        Qplus_assoc 重排（Q 层 + 结合非定义性，需显式） *)
    assert (Hleb : Nat.leb j 1 = false) by (apply Nat.leb_gt; lia).
    rewrite Hleb.
    setoid_rewrite (Qplus_assoc
             (sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                       (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
             (brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a)
             (brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a)).
    apply qeqT_imp_qeq.
    apply (c1_col_mid m j a Hj2 Hjm Hm).
Qed.

(* c1 补充部分组装：Σ_{j=2}^{m} 段1b 补充项 + brk2 (2m+1) 2 + brk2 (m+2) (m+2)（段2）== 补充行
   ——S = j+1 换元后 == supp_col 的 RHS（Σ_{S=2}^{m+1} + Σ_{S=3}^{m+2}） *)
Lemma c1_assembly : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a) +
  brk2 (2 * m + 1) 2 a + brk2 (m + 2) (m + 2) a ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a)).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (supp_col m a)).
  (* 目标：S0 + brk2(2m+1)2 + brk2(m+2)(m+2) == S1 + S2
     S1 拆头项 brk2(2m+1)2 + Σ_{i<m−1} brk2(2m−i)(i+3)（sum_upto_add 1 (m−1)）；
     S2 拆尾项 Σ_{i<m−1} brk2(2m+1−i)(i+3) + brk2(m+2)(m+2)（S(m−1) 定义） *)
  assert (H1 : sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 2) a) ==
               brk2 (2 * m + 1) 2 a +
               sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a)).
  { assert (Hup : (1 + (m - 1) = m)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (1 + (m - 1))                 (fun i => brk2 (2 * m + 1 - i) (i + 2) a) (eq_sym Hup))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 1 (m - 1)                 (fun i => brk2 (2 * m + 1 - i) (i + 2) a))).
    assert (Hpre1538_41 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun i => brk2 (2 * m + 1 - (1 + i)) (1 + i + 2) a) i ) ( (fun i => brk2 (2 * m - i) (i + 3) a) i))).
    {  intros i Hi. apply NatLe_drop in Hi.
         apply qeq_imp_qeqT.
         assert (Ha : (2 * m + 1 - (1 + i) = 2 * m - i)%nat) by lia.
         assert (Hb : (1 + i + 2 = i + 3)%nat) by lia.
         rewrite Ha, Hb. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)               (fun i => brk2 (2 * m + 1 - (1 + i)) (1 + i + 2) a)               (fun i => brk2 (2 * m - i) (i + 3) a) Hpre1538_41)).
    assert (Hsu : sum_upto 1 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a) ==
                 brk2 (2 * m + 1) 2 a).
    { change (sum_upto 1 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a)) with
        (sum_upto 0 (fun i : nat => brk2 (2 * m + 1 - i) (i + 2) a) +
         brk2 (2 * m + 1 - 0) (0 + 2) a).
      assert (Hnat1 : (2 * m + 1 - 0 = 2 * m + 1)%nat) by lia.
      assert (Hnat2 : (0 + 2 = 2)%nat) by lia.
      setoid_rewrite Hnat1. setoid_rewrite Hnat2.
      simpl. ring. }
    rewrite Hsu. reflexivity. }
  assert (H2 : sum_upto m (fun i => brk2 (2 * m + 1 - i) (i + 3) a) ==
               sum_upto (m - 1) (fun i => brk2 (2 * m + 1 - i) (i + 3) a) +
               brk2 (m + 2) (m + 2) a).
  { assert (Hsm : (m = Datatypes.S (m - 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))               (fun i => brk2 (2 * m + 1 - i) (i + 3) a) Hsm)).
    change (sum_upto (Datatypes.S (m - 1)) (fun i => brk2 (2 * m + 1 - i) (i + 3) a)) with
      (sum_upto (m - 1) (fun i => brk2 (2 * m + 1 - i) (i + 3) a) +
       brk2 (2 * m + 1 - (m - 1)) ((m - 1) + 3) a).
    assert (Hk : (2 * m + 1 - (m - 1) = m + 2)%nat) by lia.
    assert (Hj : ((m - 1) + 3 = m + 2)%nat) by lia.
    rewrite Hk, Hj.
    reflexivity. }
  rewrite H1. rewrite H2.
  (* 目标：S0 + brk2(2m+1)2 + brk2(m+2)(m+2) ==
           [brk2(2m+1)2 + S0a] + [S0b + brk2(m+2)(m+2)]——ring（S0 = S0a + S0b 用 sum_upto_plus） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                   (fun i => brk2 (2 * m - i) (i + 3) a)                   (fun i => brk2 (2 * m + 1 - i) (i + 3) a))).
  ring.
Qed.

(* c1 收尾重排：X + (B1+B2+S0) − Q + B3 − X == B1 + (B2 + (S0 + B3)) − Q（纯变量 ring） *)
Lemma c1_final : forall (X B1 B2 S0 B3 Q : Q),QeqT (
  X + (B1 + B2 + S0) - Q + B3 - X ) ( B1 + (B2 + (S0 + B3)) - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* c1 收尾重排简化版：X + A − Q + C − X == A + C − Q（A 为整体参数，X 两处相消） *)
Lemma c1_final2 : forall (X A Q C : Q),QeqT (
  X + A - Q + C - X ) ( A + C - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* c1 收尾重排全展开版：X + B1 + B2 + S0 − Q + C − X == B1 + B2 + S0 + C − Q
   ——目标 LHS 是左结合链（X + B1 + B2 + S0），非 X + (A) 形式，故需逐项展开 *)
Lemma c1_final3 : forall (X B1 B2 S0 Q C : Q),QeqT (
  X + B1 + B2 + S0 - Q + C - X ) ( B1 + B2 + S0 + C - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* c1 收尾结合重排：B1 + B2 + S0 + B3 − Q == B1 + (B2 + (S0 + B3)) − Q（供 c1_assembly2 匹配） *)
Lemma c1_assoc3 : forall (B1 B2 S0 B3 Q : Q),QeqT (
  B1 + B2 + S0 + B3 - Q ) ( B1 + (B2 + (S0 + B3)) - Q).
Proof. intros. apply qeq_imp_qeqT. ring. Qed.

(* c1_assembly 结合变体：B2 + (S0 + B3) == 补充行（供 setoid_rewrite 匹配） *)
Lemma c1_assembly2 : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  brk2 (2 * m + 1) 2 a +
  (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a) +
   brk2 (m + 2) (m + 2) a) ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a)).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  (* B2 + (S0 + B3) → (S0 + B2) + B3（Qplus_assoc + Qplus_comm）再 rewrite c1_assembly *)
  setoid_rewrite (Qplus_assoc (brk2 (2 * m + 1) 2 a)
                     (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a))
                     (brk2 (m + 2) (m + 2) a)).
  setoid_rewrite (Qplus_comm (brk2 (2 * m + 1) 2 a)
                     (sum_upto (m - 1) (fun i => brk2 (2 * m - i) (i + 3) a + brk2 (2 * m + 1 - i) (i + 3) a))).
  rewrite (qeqT_imp_qeq _ _ (c1_assembly m a Hm)).
  ring.
Qed.

(* c1：ksum_diff (S m) m == 补充项 − inner2 (m+1)(m+1) + inner2 (2m+1)1（ksum_diff_row 归纳步核心） *)
Lemma c1 : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff (Datatypes.S m) m a ) (
  sum_upto m (fun i => brk2 (m + 2 + i) (m + 1 - i) a + brk2 (m + 2 + i) (m + 2 - i) a) -
  inner2 (m + 1) (m + 1) a + inner2 (2 * m + 1) 1 a).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* LHS：ksum_diff_sum_upto——斜对角和有界和 *)
  rewrite (qeqT_imp_qeq _ _ (ksum_diff_sum_upto m m a)).
  (* inner2_sum_upto 展开内和（逐点 ext_below） *)
  assert (Hpre1538_40 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun k' => inner2 (m + 2 + k') (m + 2 - k') a - inner2 (m + 1 + k') (m + 1 - k') a) i ) ( (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a) -                      sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)) i))).
  {  intros k' Hk'. apply NatLe_drop in Hk'.
       apply qeq_imp_qeqT.
       setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 2 + k') (m + 2 - k') a)).
       setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 1 + k') (m + 1 - k') a)).
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m           (fun k' => inner2 (m + 2 + k') (m + 2 - k') a - inner2 (m + 1 + k') (m + 1 - k') a)
           (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a) -                      sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)) Hpre1538_40)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_minus m           (fun k' => sum_upto (m + 2 - k') (fun j => brk2 (m + 2 + k') (Datatypes.S j) a))           (fun k' => sum_upto (m + 1 - k') (fun j => brk2 (m + 1 + k') (Datatypes.S j) a)))).
  assert (Hle2 : (m <= m + 2)%nat) by lia.
  assert (Hle1 : (m <= m + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_min m (m + 2) (fun i j => brk2 (m + 2 + i) j a) Hm Hle2)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_tri_swap_min m (m + 1) (fun i j => brk2 (m + 1 + i) j a) Hm Hle1)).
  setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (m + 1) (m + 1) a)).
  setoid_rewrite (qeqT_imp_qeq _ _ (inner2_sum_upto (2 * m + 1) 1 a)).
  (* 目标（换序后）：
     Σ_{j=0}^{m+1} F1 j − Σ_{j=0}^{m} F2 j == 补充行 − Σ_{j=0}^{m} brk2 (m+1)(S j) + brk2 (2m+1) 1
     F1 j = sum_upto (min (m−1)(m+2−S j)+1) (brk2 (m+2+i)(S j))
     F2 j = sum_upto (min (m−1)(m+1−S j)+1) (brk2 (m+1+i)(S j)) *)
  (* 拆 sum_upto (m+2) F1 = sum_upto (m+1) F1 + F1 (m+1)（m+2 == S (m+1)） *)
  assert (Hsu : (m + 2 = Datatypes.S (m + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 2) (Datatypes.S (m + 1))            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) Hsu)).
  change (sum_upto (Datatypes.S (m + 1))
            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a))) with
    (sum_upto (m + 1)
       (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                         (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) +
     sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S (m + 1)) + 1)
              (fun i => brk2 (m + 2 + i) (Datatypes.S (m + 1)) a)).
  (* 尾项 j = m+1：c1_col_hi（第一列 == brk2 (m+2)(m+2)） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (c1_col_hi m a Hm)).
  (* Σ_{j<m+1} F1 j：逐点 c1_col_uni（j ≤ m ⇐ j < m+1）——ext_below *)
  assert (Hpre1538_39 : (forall i : nat, NatLe (Datatypes.S i) (m + 1) ->QeqT ( (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1) (fun i => brk2 (m + 2 + i) (Datatypes.S j) a)) i ) ( (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1) (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) + (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a + brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -               brk2 (m + 1) (Datatypes.S j) a) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (c1_col_uni m j a Hm). lia. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m + 1)            (fun j => sum_upto (Nat.min (m - 1) (m + 2 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 2 + i) (Datatypes.S j) a))
            (fun j =>
               sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                        (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
               (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                     brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) -               brk2 (m + 1) (Datatypes.S j) a) Hpre1538_39)).
  (* 拆 Σ (F2 + C − Q)：sum_upto_minus + sum_upto_plus *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_minus (m + 1)            (fun j =>
               sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                        (fun i => brk2 (m + 1 + i) (Datatypes.S j) a) +
               (if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                     brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))            (fun j => brk2 (m + 1) (Datatypes.S j) a))).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m + 1)            (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                              (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))
            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))).
  (* 目标：Σ F2 + Σ C − Σ Q + brk2 (m+2)(m+2) − Σ F2 == 补充行 − Σ Q + brk2 (2m+1) 1
     ——Σ C 拆 sum_upto 2 + sum_upto (m−1)（2+(m−1) = m+1） *)
  assert (HaddC : (2 + (m - 1) = m + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 1) (2 + (m - 1))            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) (eq_sym HaddC))).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_add 2 (m - 1)            (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                      else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +                           brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a))).
  (* sum_upto 2 C == brk2 (2m+1) 1 + brk2 (2m+1) 2 *)
  assert (Hc2 : sum_upto 2
                  (fun j => if Nat.leb j 1 then brk2 (2 * m + 1) (Datatypes.S j) a
                            else brk2 (2 * m + 3 - Datatypes.S j) (Datatypes.S j) a +
                                 brk2 (2 * m + 4 - Datatypes.S j) (Datatypes.S j) a) ==
               brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a).
  { simpl. ring. }
  rewrite Hc2.
  (* Σ_{j<m−1} C (2+j)：ext_below 归约（leb (2+j) 1 = false；S(2+j) = 3+j；2m+3−S(2+j) = 2m−j） *)
  assert (Hpre1538_100 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => if Nat.leb (2 + j) 1 then brk2 (2 * m + 1) (Datatypes.S (2 + j)) a else brk2 (2 * m + 3 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a + brk2 (2 * m + 4 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a) i ) ( (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a) i))).
  {  intros j Hj. apply NatLe_drop in Hj.
  apply qeq_imp_qeqT.
       assert (Hleb : Nat.leb (2 + j) 1 = false) by (apply Nat.leb_gt; lia).
       rewrite Hleb.
       assert (Hs1 : (Datatypes.S (2 + j) = 3 + j)%nat) by lia.
        rewrite Hs1.
        assert (Hsw : (3 + j = j + 3)%nat) by lia.
        rewrite Hsw.
        assert (Ha : (2 * m + 3 - (j + 3) = 2 * m - j)%nat) by lia.
       assert (Hb : (2 * m + 4 - (j + 3) = 2 * m + 1 - j)%nat) by lia.
       rewrite Ha, Hb. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1) (fun j => if Nat.leb (2 + j) 1 then brk2 (2 * m + 1) (Datatypes.S (2 + j)) a else brk2 (2 * m + 3 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a + brk2 (2 * m + 4 - Datatypes.S (2 + j)) (Datatypes.S (2 + j)) a) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a) Hpre1538_100)).
  (* 目标：Σ F2 + [brk2(2m+1)1 + brk2(2m+1)2 + S0] − Σ Q + brk2 (m+2)(m+2) − Σ F2 == 补充行 − Σ Q + Σ_1 brk2(2m+1)(S j)
     ——c1_final 重排相消（Σ F2、Σ Q 抵消）+ c1_assembly2（B2+(S0+B3) == 补充行）+ ring *)
  (* 先归约 RHS 的 sum_upto 1 (brk2 (2m+1)(S j)) == brk2 (2m+1) 1 *)
  assert (Hone : sum_upto 1 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a) ==
                 brk2 (2 * m + 1) 1 a).
  { change (sum_upto 1 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a)) with
      (sum_upto 0 (fun j => brk2 (2 * m + 1) (Datatypes.S j) a) +
       brk2 (2 * m + 1) (Datatypes.S 0) a).
    change (brk2 (2 * m + 1) (Datatypes.S 0) a) with (brk2 (2 * m + 1) 1 a).
    simpl. ring. }
  setoid_rewrite Hone.
  (* 目标：ΣF2 + (B1+B2+S0) − ΣQ + B3 − ΣF2 == 补充行 − ΣQ + B1
     ——assert 中间等式（c1_final2 相消 ΣF2），再 setoid_rewrite *)
  assert (Hx : (sum_upto (m + 1)
                  (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                    (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)) +
                (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
                 sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) -
                sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a) +
                brk2 (m + 2) (m + 2) a -
                sum_upto (m + 1)
                  (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                    (fun i => brk2 (m + 1 + i) (Datatypes.S j) a))) ==
              (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
               sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) +
              brk2 (m + 2) (m + 2) a -
              sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)).
  { apply (qeqT_imp_qeq _ _ (c1_final2             (sum_upto (m + 1)
                (fun j => sum_upto (Nat.min (m - 1) (m + 1 - Datatypes.S j) + 1)
                                  (fun i => brk2 (m + 1 + i) (Datatypes.S j) a)))
             (brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
              sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a))
             (sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a))             (brk2 (m + 2) (m + 2) a))). }
  (* transitivity 中间项：LHS == (B1+B2+S0) + B3 − ΣQ（Hx）== 补充行 − ΣQ + B1 *)
  transitivity ((brk2 (2 * m + 1) 1 a + brk2 (2 * m + 1) 2 a +
                 sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a)) +
                brk2 (m + 2) (m + 2) a -
                sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)).
  - (* LHS == 中间项：Hx 已证 *)
    exact Hx.
  - (* 中间项 == RHS：B1 + (B2+(S0+B3)) − ΣQ == 补充行 − ΣQ + B1
       ——c1_assoc3 反向重排 + c1_assembly2 + ring *)
    setoid_rewrite (qeqT_imp_qeq _ _ (c1_assoc3              (brk2 (2 * m + 1) 1 a)
              (brk2 (2 * m + 1) 2 a)
              (sum_upto (m - 1) (fun j => brk2 (2 * m - j) (j + 3) a + brk2 (2 * m + 1 - j) (j + 3) a))
              (brk2 (m + 2) (m + 2) a)              (sum_upto (m + 1) (fun j => brk2 (m + 1) (Datatypes.S j) a)))).
    setoid_rewrite (qeqT_imp_qeq _ _ (c1_assembly2 m a Hm)).
    ring.
Qed.

(* ============ 下轮目标：主恒等式 esq_eq_corr ============ *)
(*
   esq_eq_corr : forall (a : Q) (m : nat),
     e_sum m a * e_sum m a - o_sum m a * o_sum m a == 1 + corr m a.

   数学验证（数值，a=1）：m=2：E=37/24, O=7/6, E²−O²=65/64, corr=1/64 ✓
                         m=3：E²−O²=103721/103680 = 1+corr ✓（vm_compute 复核）

   等价形态（e_o_split_even/pos）：
     S_{2m}(−a)·S_{2m}(a) == 1 + corr m a   （因 E−O=S(−a)、E+O=S(a)）
   ⟹ corr ≥ 0（corr_nonneg 已证）⟹ S_{2m}(−a)·S_{2m}(a) ≥ 1 > 0
   ⟹ S_{2m}(−a) ≥ 0（exp_even_neg_nonneg，链到 exp_partial_tail_pos → cauchy_real_exp_pos）

   证明路线（两条，待择优）：
   【路线 A：对角线系数匹配（推荐）】
     1. E² == Σ_{i,j≤m} a^{2i+2j}/((2i)!(2j)!)；O² == Σ_{i,j≤m−1} a^{2i+2j+2}/((2i+1)!(2j+1)!)
        ——需 Fixpoint 双和（esq_sum/osq_sum）+ 展开引理（归纳 + ring）；
     2. a^{2n} 系数（n = i+j）：
        n ≤ m：E 侧 Σ_{i=0}^{n} 1/((2i)!(2n−2i)!) − O 侧 Σ_{i=0}^{n−1} 1/((2i+1)!(2n−2i−1)!) == 0
        ——正是 altf_zero (2n) 的偶奇拆分（altf (2n) == Σ_even − Σ_odd == 0 已证！）✓
        n ≥ m+1：截断系数 = 2Σ_{k=m}^{n−1}[1/((2k+1)!(2n−2k−1)!) − 1/((2k+2)!(2n−2k−2)!)]
        ——与 corr 的 brk2 结构逐项一致（kloop 的 k+j=n 重排）；
     3. corr 的 (k,j) → n=k+j 对角重排 == 同一条 Σ；两式相等 ⟹ 恒等式。
        【关键洞察】altf_zero（已 Qed）即 (1−1)^N==0 的展开，偶奇拆分直接给出
        Σ_even == Σ_odd——二项式恒等核心已备，无需新 binomial 定理。
   【路线 B：corr_succ 递推（增量匹配）】
     1. corr_succ：corr (S m) == corr m + Δ'，Δ' = 2E_m·T_e + T_e² − 2O_m·T_o − T_o²
        （T_e = a^{2m+2}/(2m+2)!，T_o = a^{2m+1}/(2m+1)!）——与 esq_succ 增量一致；
     2. corr (S m) − corr m = Σ_{k=m+1}^{2m+1} inner2 k (2m+2−k) − Σ_{k=m}^{2m−1} inner2 k (2m−k)
        逐项差分（inner2_succ）+ brk2 展开，匹配 Δ' 需展开 e_sum/o_sum——较繁琐；
     3. esq_succ 归纳 + corr_succ 归纳 ⟹ esq_eq_corr。
   推荐 A（altf_zero 已备、结构清晰），B 作后备。预计 2–4 小时。
*)

(* 本检验当前进度：基础设施 + corr 结构 + 非负性 + altf_zero + esq_succ 全部 Qed；
   下轮：esq_eq_corr 主恒等式（路线 A 对角线系数匹配）。 *)

(* ===== 配对论证 vander 系支撑引理（检验 _dbg_kdr.v 690-775 行，随 vander 块并入） ===== *)
(* Q 层 2·(1/x) == 2/x（Qdiv 展开 ring）——E_0/O_0 抵消用 *)
Lemma q_div_scale2 : forall (x : Q),QeqT ( 2 * (1 / x) ) ( 2 / x).
Proof.
  intro x. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

(* Qeq 移项通用引理：SE + Em - SO - Om == 0 ⟹ SO - SE == Em - Om
   （Qopp_comp 取反 + transitivity + ring——免 Hz 句法匹配之判例模式） *)
Lemma qeq_moved : forall (SE SO Em Om : Q),QeqT (
  SE + Em - SO - Om ) ( 0 )->QeqT ( SO - SE ) ( Em - Om).
Proof.
  intros SE SO Em Om H.
  apply qeq_imp_qeqT.
  assert (Hdiff : (SO - SE) - (Em - Om) == 0).
  { transitivity (- (SE + Em - SO - Om)).
    - ring.
    - assert (Hopp : - (SE + Em - SO - Om) == - 0).
      { apply (Qopp_comp (SE + Em - SO - Om) 0 (qeqT_imp_qeq _ _ H)). }
      rewrite <- Hopp.
      ring. }
  transitivity ((SO - SE) - (Em - Om) + (Em - Om)).
  - ring.
  - rewrite Hdiff. ring.
Qed.

(* Qeq 移项变体：A + B + (-C) == 0 ⟹ C - A == B（Hz 的 2ΣE + Em + 2·(-ΣO) == 0 形态） *)
Lemma qeq_moved_neg : forall (A B C : Q),QeqT (
  A + B + (- C) ) ( 0 )->QeqT ( C - A ) ( B).
Proof.
  intros A B C H.
  apply qeq_imp_qeqT.
  (* H : A + B + (-C) == 0 ⟹ -(A + B + (-C)) == 0（Qopp_comp）
     C - A - B == -(A + B + (-C))（ring 恒等） *)
  assert (Hdiff : (C - A) - B == 0).
  { transitivity (- (A + B + (- C))).
    - ring.
    - assert (Hopp : - (A + B + (- C)) == - 0).
      { apply (Qopp_comp (A + B + (- C)) 0 (qeqT_imp_qeq _ _ H)). }
      rewrite <- Hopp.
      ring. }
  (* (C-A) - B == 0 ⟹ C - A == B（两边加 B） *)
  transitivity ((C - A) - B + B).
  - ring.
  - rewrite Hdiff. ring.
Qed.

(* Qeq 移项变体2：A + B + 2*(-C) == 0 ⟹ 2C - A == B（Hz 的 `2ΣE + Em + 2·(-ΣO) == 0` 形态）
   用 qeq_moved_neg 于 (A, B, 2C)：A + B + (-(2C)) == 0 由前提经 ring（2·(-C) == -(2·C)） *)
Lemma qeq_moved_neg2 : forall (A B C : Q),QeqT (
  A + B + 2 * (- C) ) ( 0 )->QeqT ( 2 * C - A ) ( B).
Proof.
  intros A B C H.
  apply (qeq_moved_neg A B (2 * C)).
  apply qeq_imp_qeqT.
  (* 需证 A + B + (-(2*C)) == 0——由 H（A + B + 2*(-C) == 0）经 ring *)
  rewrite <- (qeqT_imp_qeq _ _ H).
  ring.
Qed.

(* sum_upto 移位：Σ_{j=0}^{n-1} f (j+1) == Σ_{j=0}^{n} f j - f 0（首项移出，rot 反向）
   sum_upto (S n) f == f 0 + sum_upto n (fun j => f (S j))（rot）⟹ 移项 *)
Lemma sum_upto_shift : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => f (j + 1)%nat) ) ( sum_upto (n + 1) f - f 0%nat).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  assert (Hn : (n + 1 = Datatypes.S n)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (n + 1)%nat (Datatypes.S n) f Hn)).
  rewrite (qeqT_imp_qeq _ _ (sum_upto_rot n f)).
  assert (Hpre1538_38 : (forall i,QeqT ( (fun j => f (j + 1)%nat) i ) ( (fun j => f (Datatypes.S j)) i))).
  {  intro j. apply qeq_imp_qeqT. assert (Hj : (j + 1 = Datatypes.S j)%nat) by lia. rewrite Hj. reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext n (fun j => f (j + 1)%nat) (fun j => f (Datatypes.S j)) Hpre1538_38)).
  unfold Qminus. ring.
Qed.

(* sum_upto 数乘线性：Σ(c·f) == c·Σf（归纳，simpl + ring） *)
Lemma sum_upto_scale : forall (n : nat) (c : Q) (f : nat -> Q),QeqT (
  sum_upto n (fun j => c * f j) ) ( c * sum_upto n f).
Proof.
  intros n. induction n as [| n' IH]; intros c f; simpl.
  - apply qeq_imp_qeqT. ring.
  - apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (IH c f)). ring.
Qed.

(* sum_upto 数乘线性（-2 系数）：Σ(-2·f) == -2·Σf *)
Lemma sum_upto_scale_neg2 : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => - 2 * f j) ) ( - 2 * sum_upto n f).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_scale n (- 2) f)).
  reflexivity.
Qed.

(* ============ 配对论证第三步：Vandermonde 恒等（vander_4m2 / vander_4m4，检验 _dbg_kdr.v 67 Qed 并入） ============ *)
(* q_pow 1 任意幂 == 1 *)
Lemma q_pow_one : forall n,QeqT ( q_pow 1 n ) ( 1).
Proof.
  intro n. apply qeq_imp_qeqT. induction n as [| n' IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(* (−1)^{2n} == 1 *)
Lemma q_pow_neg1_even : forall n,QeqT ( q_pow (-1) (2 * n) ) ( 1).
Proof.
  intro n. apply qeq_imp_qeqT.
  exact (Qeq_trans _ _ _ (qeqT_imp_qeq _ _ (q_pow_neg_even 1 n)) (qeqT_imp_qeq _ _ (q_pow_one (2 * n)))).
Qed.

(* (−1)^{2n+1} == −1 *)
Lemma q_pow_neg1_odd : forall n,QeqT ( q_pow (-1) (2 * n + 1) ) ( -1).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  assert (Hidx : (2 * n + 1 = Datatypes.S (2 * n))%nat) by lia.
  setoid_replace (q_pow (-1) (2 * n + 1)) with (q_pow (-1) (Datatypes.S (2 * n))).
  2: { apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) (2 * n + 1)%nat (Datatypes.S (2 * n))%nat Hidx). }
  setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd 1 n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_one (Datatypes.S (2 * n)))).
  ring.
Qed.

(* altf 转 sum_upto：altf N == Σ_{u=0}^{N} q_pow (−1) u / (u!(N−u)!) *)
Lemma altf_as_sum_upto : forall N,QeqT ( altf N ) (
  sum_upto (N + 1) (fun u => q_pow (-1) u / (q_fact u * q_fact (N - u)))).
Proof.
  intro N.
  apply qeq_imp_qeqT.
  (* 先证通用：altf_aux N u == sum_upto (u+1) (fun t => q_pow (−1) t / (t!(N−t)!))，归纳于 u *)
  assert (Haux : forall u, altf_aux N u ==
                 sum_upto (u + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))).
  { intro u. induction u as [| u' IH]; simpl.
    - (* u=0：altf_aux N 0 == Qinv(q_fact N)；sum_upto 1 f == f 0 == 1/(0!(N−0)!) *)
      assert (Hs : sum_upto (0 + 1) (fun t : nat => q_pow (-1) t / (q_fact t * q_fact (N - t))) ==
                   q_pow (-1) 0 / (q_fact 0 * q_fact (N - 0))).
      { simpl. ring. }
      rewrite Hs.
      assert (H0 : (N - 0 = N)%nat) by lia.
      rewrite H0.
      simpl.
      unfold Qdiv.
      setoid_rewrite (Qmult_1_l (q_fact N)).
      ring.
    - (* u = S u'：altf_aux N (S u') == altf_aux N u' + q_pow (−1) (S u')/((S u')!(N−S u')!) *)
      change (altf_aux N u' + q_pow (-1) (Datatypes.S u') / (q_fact (Datatypes.S u') * q_fact (N - Datatypes.S u')) ==
              sum_upto (Datatypes.S u' + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))).
      assert (Hsu : (Datatypes.S u' + 1 = Datatypes.S (u' + 1))%nat) by lia.
      rewrite Hsu.
      change (sum_upto (Datatypes.S (u' + 1)) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t)))) with
        (sum_upto (u' + 1) (fun t => q_pow (-1) t / (q_fact t * q_fact (N - t))) +
         q_pow (-1) (u' + 1) / (q_fact (u' + 1) * q_fact (N - (u' + 1)))).
      setoid_rewrite IH.
      (* 尾项：q_pow (−1) (S u') vs q_pow (−1) (u'+1)——S u' == u'+1 定义性？u'+1 == S u' 需 lia *)
      assert (Hp : (u' + 1 = Datatypes.S u')%nat) by lia.
      setoid_replace (q_pow (-1) (u' + 1)) with (q_pow (-1) (Datatypes.S u')).
      2: { apply (q_pow_comp_proper (-1) (-1) (Qeq_refl (-1)) (u' + 1)%nat (Datatypes.S u')%nat Hp). }
      assert (Hf : (N - (u' + 1) = N - Datatypes.S u')%nat) by lia.
      setoid_replace (q_fact (N - (u' + 1))) with (q_fact (N - Datatypes.S u')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
      assert (Hq : (u' + 1 = Datatypes.S u')%nat) by lia.
      setoid_replace (q_fact (u' + 1)) with (q_fact (Datatypes.S u')).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hq. }
      ring. }
  (* altf N == altf_aux N N；sum_upto (N+1) 与 u=N 形态一致 *)
  unfold altf.
  setoid_rewrite (Haux N).
  assert (Hn : (N + 1 = N + 1)%nat) by lia.
  reflexivity.
Qed.

(* sum_upto 偶奇拆分（偶数项数）：Σ_{i=0}^{2n−1} f i == Σ_{j=0}^{n−1} f (2j) + Σ_{j=0}^{n−1} f (2j+1) *)
Lemma sum_upto_even_split : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto (2 * n)%nat f ) (
  sum_upto n (fun j => f (2 * j)%nat) + sum_upto n (fun j => f (2 * j + 1)%nat)).
Proof.
  intros n. induction n as [| n' IH]; intros f.
  - (* n=0：sum_upto 0 f == 0 + 0 *)
    apply qeq_imp_qeqT.
    simpl. ring.
  - (* 2·S n' == S(S(2n'))——sum_upto_nat_eq 换形（simpl 不可，2·S n' 对变量 n' 不化简） *)
    apply qeq_imp_qeqT.
    assert (Hidx : (2 * Datatypes.S n' = Datatypes.S (Datatypes.S (2 * n')))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * Datatypes.S n')%nat (Datatypes.S (Datatypes.S (2 * n'))) f Hidx)).
    (* LHS 逐层拆：sum_upto (S(S(2n'))) f == sum_upto (2n') f + f (2n') + f (S(2n')) *)
    change (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f) with
      (sum_upto (Datatypes.S (2 * n')) f + f (Datatypes.S (2 * n'))).
    change (sum_upto (Datatypes.S (2 * n')) f) with
      (sum_upto (2 * n')%nat f + f (2 * n')%nat).
    setoid_rewrite (qeqT_imp_qeq _ _ (IH f)).
    (* RHS：sum_upto (S n') 拆尾项——逐项 change（大项 change 不可靠） *)
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j)%nat)) with
      (sum_upto n' (fun j => f (2 * j)%nat) + f (2 * n')%nat).
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j + 1)%nat)) with
      (sum_upto n' (fun j => f (2 * j + 1)%nat) + f (2 * n' + 1)%nat).
    (* 尾项换形：f (S(2n')) == f (2n'+1)（lia 非定义性，rewrite 显式） *)
    assert (Ht : (Datatypes.S (2 * n') = 2 * n' + 1)%nat) by lia.
    rewrite Ht.
    ring.
Qed.

(* sum_upto 偶奇拆分（奇数项数）：Σ_{i=0}^{2n} f i == Σ_{j=0}^{n} f (2j) + Σ_{j=0}^{n−1} f (2j+1) *)
Lemma sum_upto_even_split_odd : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto (2 * n + 1)%nat f ) (
  sum_upto (n + 1)%nat (fun j => f (2 * j)%nat) + sum_upto n (fun j => f (2 * j + 1)%nat)).
Proof.
  intros n. induction n as [| n' IH]; intros f.
  - (* n=0：sum_upto 1 f == f 0 == f 0 + 0 *)
    apply qeq_imp_qeqT.
    simpl. ring.
  - (* 2·S n'+1 == S(S(S(2n')))——sum_upto_nat_eq 换形 *)
    apply qeq_imp_qeqT.
    assert (Hidx : (2 * Datatypes.S n' + 1 = Datatypes.S (Datatypes.S (Datatypes.S (2 * n'))))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * Datatypes.S n' + 1)%nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * n')))) f Hidx)).
    (* LHS 逐层拆：sum_upto (2n'+3) f == sum_upto (2n'+1) f + f (2n'+1) + f (2n'+2) *)
    change (sum_upto (Datatypes.S (Datatypes.S (Datatypes.S (2 * n')))) f) with
      (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f + f (Datatypes.S (Datatypes.S (2 * n')))).
    change (sum_upto (Datatypes.S (Datatypes.S (2 * n'))) f) with
      (sum_upto (Datatypes.S (2 * n')) f + f (Datatypes.S (2 * n'))).
    (* sum_upto (S(2n')) f 与 IH 的 sum_upto (2n'+1) f 形态统一（lia 非定义性） *)
    assert (Hsn : (2 * n' + 1 = Datatypes.S (2 * n'))%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n' + 1)%nat (Datatypes.S (2 * n')) f Hsn)).
    (* 对 sum_upto (2n'+1) f 用 IH *)
    setoid_rewrite (qeqT_imp_qeq _ _ (IH f)).
    (* RHS 逐项拆尾项：先 nat_eq 统一 S n'+1 == S(n'+1)，再逐项 change *)
    assert (Hsr : (Datatypes.S n' + 1 = Datatypes.S (n' + 1))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S n' + 1)%nat (Datatypes.S (n' + 1)) (fun j => f (2 * j)%nat) Hsr)).
    change (sum_upto (Datatypes.S (n' + 1)) (fun j => f (2 * j)%nat)) with
      (sum_upto (n' + 1)%nat (fun j => f (2 * j)%nat) + f (2 * (n' + 1))%nat).
    change (sum_upto (Datatypes.S n') (fun j => f (2 * j + 1)%nat)) with
      (sum_upto n' (fun j => f (2 * j + 1)%nat) + f (2 * n' + 1)%nat).
    (* 尾项统一：f (2(n'+1)) == f (S(S(2n')))（H6）；f (S(2n')) == f (2n'+1)（Ht1） *)
    assert (H6 : (2 * (n' + 1) = Datatypes.S (Datatypes.S (2 * n')))%nat) by lia.
    rewrite H6.
    assert (Ht1 : (Datatypes.S (2 * n') = 2 * n' + 1)%nat) by lia.
    rewrite Ht1.
    ring.
Qed.

(* 和分割（通用版，无范围前提）：Σ_{i=0}^{a+b−1} f i == Σ_{i=0}^{a−1} f i + Σ_{i=0}^{b−1} f (a+i)
   证明：归纳于 a；归纳步两侧都 sum_upto_rot 移出首项 f 0，IH 于 g = f∘S（判例 g∘S 模式） *)
Lemma sum_upto_split_gen : forall (a b : nat) (f : nat -> Q),QeqT (
  sum_upto (a + b)%nat f ) ( sum_upto a f + sum_upto b (fun i => f (a + i)%nat)).
Proof.
  intros a. induction a as [| a' IH]; intros b f.
  - (* a=0：sum_upto b f == 0 + sum_upto b (fun i => f (0+i)) *)
    apply qeq_imp_qeqT.
    change (sum_upto (0 + b) f) with (sum_upto b f).
    change (sum_upto 0 f) with 0.
    assert (Hpre1538_37 : (forall i,QeqT ( (fun i => f (0 + i)%nat) i ) ( f i))).
    {  intro i. apply qeq_imp_qeqT. change (f (0 + i)%nat) with (f i). reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext b (fun i => f (0 + i)%nat) f Hpre1538_37)).
    ring.
  - (* a = S a'：LHS 与 RHS 都先 rot 移出首项 f 0，再 IH 于 g = f∘S *)
    apply qeq_imp_qeqT.
    assert (Hadd : (Datatypes.S a' + b = Datatypes.S (a' + b))%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (Datatypes.S a' + b) (Datatypes.S (a' + b)) f Hadd)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (a' + b) f)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_rot a' f)).
    setoid_rewrite (qeqT_imp_qeq _ _ (IH b (fun i => f (Datatypes.S i)))).
    assert (Hpre1538_36 : (forall i,QeqT ( (fun i => f (Datatypes.S (a' + i))%nat) i ) ( (fun i => f (Datatypes.S a' + i)%nat) i))).
    {  intro i. apply qeq_imp_qeqT. assert (Hnat : (Datatypes.S (a' + i) = Datatypes.S a' + i)%nat) by lia.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext b (fun i => f (Datatypes.S (a' + i))%nat) (fun i => f (Datatypes.S a' + i)%nat) Hpre1538_36)).
    ring.
Qed.

(* 副本对称（偶数项数）：f j == f (2n+1−j)（j ≤ n）⟹ Σ_{j=0}^{2n+1} f j == 2·Σ_{j=0}^{n} f j *)
Lemma sum_upto_mirror_even : forall (n : nat) (f : nat -> Q),
  (forall j, NatLe j n ->QeqT ( f j ) ( f (2 * n + 1 - j)%nat)) ->QeqT (
  sum_upto (2 * n + 2)%nat f ) ( 2 * sum_upto (n + 1) f).
Proof.
  intros n f Hmir.
  apply qeq_imp_qeqT.
  (* 2n+2 == (n+1)+(n+1)：split *)
  assert (Hadd : (2 * n + 2 = (n + 1) + (n + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n + 2)%nat ((n + 1) + (n + 1)) f Hadd)).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_split_gen (n + 1) (n + 1) f)).
  (* 第二和：Σ_{i=0}^{n} f (n+1+i) == Σ_{i=0}^{n} f i（副本 f (2n+1−i) == f i） *)
  assert (Hsec : sum_upto (n + 1) (fun i => f (n + 1 + i)%nat) == sum_upto (n + 1) f).
  { (* sum_upto_rev 反向：sum_upto (n+1) h == sum_upto (n+1) (fun i => h (n−i))，h i = f (n+1+i) *)
    setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev (n + 1) (fun i => f (n + 1 + i)%nat))).
    (* n+1+(n−i) == 2n+1−i 只对 i ≤ n 成立——ext_below（i < n+1） *)
    assert (Hpre1538_35 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (n + 1 + (n + 1 - 1 - i))%nat) i ) ( (fun i => f (2 * n + 1 - i)%nat) i))).
    {  intros i Hi. apply NatLe_drop in Hi. assert (Hnat : (n + 1 + (n + 1 - 1 - i) = 2 * n + 1 - i)%nat) by lia.
         apply qeq_imp_qeqT.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (n + 1 + (n + 1 - 1 - i))%nat) (fun i => f (2 * n + 1 - i)%nat) Hpre1538_35)).
    assert (Hpre1538_34 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (2 * n + 1 - i)%nat) i ) ( f i))).
    {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. apply (Hmir i). apply NatLe_lift. lia. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (2 * n + 1 - i)%nat) f Hpre1538_34)).
    reflexivity. }
  setoid_rewrite Hsec.
  ring.
Qed.

(* 副本对称（奇数项数）：f j == f (2n−j)（j ≤ n）⟹ Σ_{j=0}^{2n} f j == 2·Σ_{j=0}^{n−1} f j + f n *)
Lemma sum_upto_mirror_odd : forall (n : nat) (f : nat -> Q),
  (forall j, NatLe j n ->QeqT ( f j ) ( f (2 * n - j)%nat)) ->QeqT (
  sum_upto (2 * n + 1)%nat f ) ( 2 * sum_upto n f + f n).
Proof.
  intros n f Hmir.
  apply qeq_imp_qeqT.
  (* 2n+1 == n+(n+1)：split *)
  assert (Hadd : (2 * n + 1 = n + (n + 1))%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * n + 1)%nat (n + (n + 1)) f Hadd)).
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_split_gen n (n + 1) f)).
  (* 第二和：Σ_{i=0}^{n} f (n+i) == Σ_{i=0}^{n} f (2n−i) == Σ_{i=0}^{n} f i（副本） *)
  assert (Hsec : sum_upto (n + 1) (fun i => f (n + i)%nat) == sum_upto (n + 1) f).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev (n + 1) (fun i => f (n + i)%nat))).
    assert (Hpre1538_33 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (n + (n + 1 - 1 - i))%nat) i ) ( (fun i => f (2 * n - i)%nat) i))).
    {  intros i Hi. apply NatLe_drop in Hi. assert (Hnat : (n + (n + 1 - 1 - i) = 2 * n - i)%nat) by lia.
         apply qeq_imp_qeqT.
         rewrite Hnat. reflexivity. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (n + (n + 1 - 1 - i))%nat) (fun i => f (2 * n - i)%nat) Hpre1538_33)).
    assert (Hpre1538_32 : (forall i : nat, NatLe (Datatypes.S i) (n + 1) ->QeqT ( (fun i => f (2 * n - i)%nat) i ) ( f i))).
    {  intros i Hi. apply NatLe_drop in Hi. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. apply (Hmir i). apply NatLe_lift. lia. }
    rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (n + 1) (fun i => f (2 * n - i)%nat) f Hpre1538_32)).
    reflexivity. }
  setoid_rewrite Hsec.
  (* sum_upto (n+1) f == sum_upto n f + f n（n+1 非 S n 句法，nat_eq 桥接） *)
  assert (Hs : (n + 1 = Datatypes.S n)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (n + 1)%nat (Datatypes.S n) f Hs)).
  change (sum_upto (Datatypes.S n) f) with (sum_upto n f + f n).
  ring.
Qed.

(* ===== vander_4m2：a^{4m+2} 层 Vandermonde 恒等 =====
   Σ_{j=0}^{m−1} [−2/((4m+2−2j)!(2j)!) + 2/((4m+1−2j)!(2j+1)!)]
   == 2/((2m+2)!(2m)!) − 1/((2m+1)!(2m+1)!)
   证明路线：altf_zero (4m+2)（== 0）→ altf_as_sum_upto → 偶奇拆分
   → q_pow_neg1 奇偶归约 → 副本对称（偶部×2、奇部×2+中项）→ 代数变形。
   核心：0 == 2·Σ_{j=0}^{m} E_j − (2·Σ_{j=0}^{m−1} O_j + O_m)
        ⟹ 2·Σ_{j=0}^{m−1}(O_j−E_j) == 2·E_m − O_m == RHS（分母交换）。 *)
Lemma vander_4m2 : forall (m : nat),
  (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ) (
  2 / (q_fact (2 * m + 2) * q_fact (2 * m)) -
  1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  (* 1. altf_zero (4m+2)：altf (4m+2) == 0；altf_as_sum_upto 转换 *)
  assert (Hz : altf (4 * m + 2) == 0).
  { apply qeqT_imp_qeq. apply altf_zero. lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (altf_as_sum_upto (4 * m + 2))) in Hz.
  (* 2. 偶奇拆分：sum_upto (4m+3) g == Σ_{j=0}^{2m+1} g (2j) + Σ_{j=0}^{2m} g (2j+1)
     先 nat_eq 把 Hz 的 sum_upto (4m+2+1) 换成 sum_upto (2(2m+1)+1)（非定义性） *)
  assert (Hn1 : (4 * m + 2 + 1 = 2 * (2 * m + 1) + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (4 * m + 2 + 1)%nat (2 * (2 * m + 1) + 1)%nat            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 2 - u))) Hn1)) in Hz.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd (2 * m + 1)            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 2 - u))))) in Hz.
  (* RHS 的 sum_upto (2m+1+1) == sum_upto (2m+2)（非定义性，nat_eq） *)
  assert (Hn2 : (2 * m + 1 + 1 = 2 * m + 2)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * m + 1 + 1)%nat (2 * m + 2)%nat            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hn2)) in Hz.
  (* 3. 逐点归约：g (2j) == 1/((2j)!(4m+2−2j)!)；g (2j+1) == −1/((2j+1)!(4m+1−2j)!) *)
  assert (Hpre1538_31 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) i ) ( (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even j)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 2)            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))            (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hpre1538_31)) in Hz.
  assert (Hpre1538_30 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 2 - (2 * j + 1)))) i ) ( (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_odd j)).
       assert (Hn : (4 * m + 2 - (2 * j + 1) = 4 * m + 1 - 2 * j)%nat) by lia.
       setoid_replace (q_fact (4 * m + 2 - (2 * j + 1))) with (q_fact (4 * m + 1 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
       ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 1)            (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 2 - (2 * j + 1))))            (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) Hpre1538_30)) in Hz.
  (* 4. 副本对称：偶部 Σ_{j=0}^{2m+1} E_j == 2·Σ_{j=0}^{m} E_j *)
  assert (HmirE : sum_upto (2 * m + 2)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
  { apply qeqT_imp_qeq.
  apply (sum_upto_mirror_even m             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m + 1 - j) = 4 * m + 2 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 2 - 2 * (2 * m + 1 - j) = 2 * j)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1 - j))) with (q_fact (4 * m + 2 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 2 - 2 * (2 * m + 1 - j))) with (q_fact (2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: split; intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 5. 副本对称：奇部 Σ_{j=0}^{2m} O_j == 2·Σ_{j=0}^{m−1} O_j + O_m（O_m = −1/((2m+1)!(2m+1)!)） *)
  assert (HmirO : sum_upto (2 * m + 1)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) ==
           2 * sum_upto m
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) +
           (- 1) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { (* 用 mirror_odd 于 f（f j = -1/((2j+1)!(4m+1−2j)!)），产生 f m 项；
        先证 f m 的 q_fact 第二参数归约（4m+1−2m == 2m+1），替换后再用 mirror_odd *)
    assert (Hmid : (4 * m + 1 - 2 * m = 2 * m + 1)%nat) by lia.
    assert (Hfmid : - 1 / (q_fact (2 * m + 1) * q_fact (4 * m + 1 - 2 * m)) ==
                    - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
    { setoid_replace (q_fact (4 * m + 1 - 2 * m)) with (q_fact (2 * m + 1)).
      2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid. }
      reflexivity. }
    (* 目标 = 2·Σ f + (-1)/((2m+1)!(2m+1)!)；f m = (-1)/((2m+1)!(4m+1−2m)!) == 目标末项 *)
    setoid_rewrite <- Hfmid.
    apply qeqT_imp_qeq.
    apply (sum_upto_mirror_odd m             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m - j) + 1 = 4 * m + 1 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 1 - 2 * (2 * m - j) = 2 * j + 1)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m - j) + 1)) with (q_fact (4 * m + 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 1 - 2 * (2 * m - j))) with (q_fact (2 * j + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: split; intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 6. 代入副本：Hz == 2·Σ_{j=0}^{m} E_j − (2·Σ_{j=0}^{m−1} O_j + O_m) == 0 *)
  setoid_rewrite HmirE in Hz.
  setoid_rewrite HmirO in Hz.
  (* 7. 拆分 E 和：Σ_{j=0}^{m} E_j == Σ_{j=0}^{m−1} E_j + E_m，E_m = 1/((2m)!(2m+2)!) *)
  assert (HsplitE : sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
            sum_upto m
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
           1 / (q_fact (2 * m) * q_fact (2 * m + 2))).
  { assert (Hs : (m + 1 = Datatypes.S m)%nat) by lia.
    rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (m + 1)%nat (Datatypes.S m)              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) Hs)).
    change (sum_upto (Datatypes.S m)
              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) with
      (sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
       1 / (q_fact (2 * m) * q_fact (4 * m + 2 - 2 * m))).
    setoid_replace (q_fact (4 * m + 2 - 2 * m)) with (q_fact (2 * m + 2)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite HsplitE in Hz.
  (* 8. Hz 代数：Hz == 2·ΣE' + 2·Em − 2·ΣO'' − Om == 0（O'' = 1/((2j+1)!(4m+1−2j)!)）
        先用 HzO 把 Hz 里的 Σ(−1/X) 换成 −Σ(1/X)（sum_upto_neg + ext 逐点） *)
  assert (HzO : sum_upto m (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) ==
                - sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_neg m             (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext m             (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))             (fun j => - (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))).
    intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  rewrite HzO in Hz.
  (* 9. Hz 移项（qeq_moved 模式）：2·ΣO'' − 2·ΣE' == 2·Em − Om
        用 Qopp_comp 于 Hz 取反（免句法），transitivity + ring *)
  assert (Hmoved : 2 * sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                    2 * sum_upto m
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) ==
                   2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                   1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { (* Hdiff : LHS - RHS == 0；LHS - RHS == -(Hz LHS)（ring）；-(Hz LHS) == 0（Hz 取反） *)
    assert (Hdiff : (2 * sum_upto m
                       (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                      2 * sum_upto m
                        (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) -
                     (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                      1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) == 0).
    { (* Hdiff LHS == -A（ring）；-A == 0（Hz 取反）——A 用 set 从 Hz 提取（免句法） *)
      set (A := 2 * (sum_upto m
                       (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                      1 / (q_fact (2 * m) * q_fact (2 * m + 2))) +
                  (2 * (- sum_upto m
                          (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) +
                   (- 1) / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
      change (A == 0) in Hz.
      transitivity (- A).
      - unfold A. unfold Qdiv. ring.
      - (* -A == 0：Qopp_comp A 0 Hz 给 -A == -0；-0 == 0（ring） *)
        assert (Hopp : - A == - 0).
        { apply (Qopp_comp A 0 Hz). }
        rewrite <- Hopp. unfold Qdiv. ring. }
    (* Hdiff : LHS - RHS == 0 ⟹ LHS == RHS（两边加 RHS，Qeq 移项） *)
    transitivity ((2 * sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                    2 * sum_upto m
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) -
                   (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                    1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))) +
                   (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2))) -
                    1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
    - unfold Qdiv. ring.
    - rewrite Hdiff. ring. }
  (* 10. vander 目标 LHS == Σ(-2E + 2O)（原始）→ 需转成 -2ΣE' + 2ΣO''（sum_upto 线性）
        但当前目标是 vander 的原始陈述——先做线性转换 *)
  (* 目标：sum_upto m (fun j => -2/X_j + 2/Y_j) == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!)
     LHS 线性：Σ(-2E+2O) == -2ΣE' + 2ΣO''（sum_upto_ext 逐点 + 归纳线性） *)
  assert (Hlin : sum_upto m
                   (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                             2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) ==
                 - 2 * sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +
                 2 * sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m              (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))))              (fun j => 2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))))).
    assert (Hsc1 : sum_upto m (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))) ==
                  - 2 * sum_upto m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
    { exact (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))))). }
    assert (Hsc2 : sum_upto m (fun j => 2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) ==
                  2 * sum_upto m (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))).
    { exact (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))))). }
    setoid_rewrite Hsc1. setoid_rewrite Hsc2. reflexivity. }
  (* vander LHS 逐点归一到 -2*(1/X') + 2*(1/Y')（分母交换） *)
  assert (Hpre1538_29 : (forall i,QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)) + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) i ) ( (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +                      2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) i))).
  {  intro j. apply qeq_imp_qeqT. unfold Qdiv. field.
       all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
            intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)) +
                      2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1)))
            (fun j => - 2 * (1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j))) +                      2 * (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j)))) Hpre1538_29)).
  setoid_rewrite Hlin.
  (* 目标：-2ΣE' + 2ΣO'' == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!)
     Hmoved : 2ΣO'' - 2ΣE' == 2Em' - Om'
     RHS：2Em' - Om' == 2/((2m+2)!(2m)!) - 1/((2m+1)!(2m+1)!)（分母交换，ring） *)
  setoid_replace (2 / (q_fact (2 * m + 2) * q_fact (2 * m)))
    with (2 * (1 / (q_fact (2 * m) * q_fact (2 * m + 2)))).
  2: { unfold Qdiv. field.
       all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
            intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 目标：-2ΣE' + 2ΣO'' == 2Em' - Om'；用 Hmoved（LHS ring 等价） *)
  transitivity (2 * sum_upto m
                  (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 1 - 2 * j))) -
                2 * sum_upto m
                  (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 2 - 2 * j)))).
  - unfold Qdiv. ring.
  - exact Hmoved.
Qed.

(* ===== vander_4m4：a^{4m+4} 层 Vandermonde 恒等 =====
   Σ_{j=0}^{m−1} [−2/((4m+2−2j)!(2j+2)!) + 2/((4m+1−2j)!(2j+3)!)]
   + [−2/((4m+4)!(0)!) + 2/((4m+3)!(1)!)] == 1/((2m+2)!(2m+2)!)
   证明路线（同构 vander_4m2）：altf_zero (4m+4) → altf_as_sum_upto (4m+4)
   → 偶奇拆分（sum_upto (4m+5) = sum_upto (2(2m+2)+1)）→ q_pow_neg1 归约
   → 副本（偶部×2、奇部×2，无中项）→ Qeq 移项（Qopp_comp 模式）。
   尾项 [−2/((4m+4)!(0)!) + 2/((4m+3)!(1)!)] 与 j=0 项合并：j=0 时
   −2/((4m+2)!(2)!) + 2/((4m+1)!(3)!) + 尾项——需整体配对。 *)
Lemma vander_4m4 : forall (m : nat),
  (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))
       + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))
  - 2 / (q_fact (4 * m + 4) * q_fact 0)
  + 2 / (q_fact (4 * m + 3) * q_fact 1) ) (
  1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  (* 1. altf_zero (4m+4)：altf (4m+4) == 0；altf_as_sum_upto 转换 *)
  assert (Hz : altf (4 * m + 4) == 0).
  { apply qeqT_imp_qeq. apply altf_zero. lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (altf_as_sum_upto (4 * m + 4))) in Hz.
  (* 2. 偶奇拆分：sum_upto (4m+5) g == Σ_{j=0}^{2m+2} g (2j) + Σ_{j=0}^{2m+1} g (2j+1)
     先 nat_eq 把 Hz 的 sum_upto (4m+4+1) 换成 sum_upto (2(2m+2)+1) *)
  assert (Hn1 : (4 * m + 4 + 1 = 2 * (2 * m + 2) + 1)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (4 * m + 4 + 1)%nat (2 * (2 * m + 2) + 1)%nat            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 4 - u))) Hn1)) in Hz.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_even_split_odd (2 * m + 2)            (fun u => q_pow (-1) u / (q_fact u * q_fact (4 * m + 4 - u))))) in Hz.
  assert (Hn2 : (2 * m + 2 + 1 = 2 * m + 3)%nat) by lia.
  rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * m + 2 + 1)%nat (2 * m + 3)%nat            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hn2)) in Hz.
  (* 3. 逐点归约：g (2j) == 1/((2j)!(4m+4−2j)!)；g (2j+1) == −1/((2j+1)!(4m+3−2j)!) *)
  assert (Hpre1538_28 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) i ) ( (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_even j)). ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 3)            (fun j => q_pow (-1) (2 * j) / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j)))            (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hpre1538_28)) in Hz.
  assert (Hpre1538_27 : (forall i,QeqT ( (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 4 - (2 * j + 1)))) i ) ( (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) i))).
  {  intro j. apply qeq_imp_qeqT. setoid_rewrite (qeqT_imp_qeq _ _ (q_pow_neg1_odd j)).
       assert (Hn : (4 * m + 4 - (2 * j + 1) = 4 * m + 3 - 2 * j)%nat) by lia.
       setoid_replace (q_fact (4 * m + 4 - (2 * j + 1))) with (q_fact (4 * m + 3 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
       ring. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (2 * m + 2)            (fun j => q_pow (-1) (2 * j + 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 4 - (2 * j + 1))))            (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) Hpre1538_27)) in Hz.
  (* 4. 副本对称：
         偶部 sum_upto (2m+3) E（2m+3 项，j=0..2m+2）：mirror_odd n=m+1 ⟹ 2·Σ_{j=0}^{m} E_j + E_{m+1}
         奇部 sum_upto (2m+2) O（2m+2 项，j=0..2m+1）：mirror_even n=m ⟹ 2·Σ_{j=0}^{m} O_j *)
  assert (HmirE : sum_upto (2 * m + 3)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
           1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
  { (* mirror_odd (m+1) 结论：sum_upto (2(m+1)+1) f == 2·sum_upto (m+1) f + f (m+1)
         2(m+1)+1 == 2m+3 非句法同形——先 nat_eq 于目标 LHS 再 apply *)
    assert (Hidx : (2 * (m + 1) + 1 = 2 * m + 3)%nat) by lia.
    rewrite <- (qeqT_imp_qeq _ _ (sum_upto_nat_eq (2 * (m + 1) + 1)%nat (2 * m + 3)%nat              (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) Hidx)).
    apply qeqT_imp_qeq.
    apply (sum_upto_mirror_odd (m + 1)             (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * (m + 1) - j) = 4 * m + 4 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 4 - 2 * (2 * (m + 1) - j) = 2 * j)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * (m + 1) - j))) with (q_fact (4 * m + 4 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 4 - 2 * (2 * (m + 1) - j))) with (q_fact (2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
         intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  assert (HmirO : sum_upto (2 * m + 2)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) ==
           2 * sum_upto (m + 1)
             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
  { apply qeqT_imp_qeq.
  apply (sum_upto_mirror_even m             (fun j => - 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
    intros j Hj. apply NatLe_drop in Hj.
    apply qeq_imp_qeqT.
    assert (H1 : (2 * (2 * m + 1 - j) + 1 = 4 * m + 3 - 2 * j)%nat) by lia.
    assert (H2 : (4 * m + 3 - 2 * (2 * m + 1 - j) = 2 * j + 1)%nat) by lia.
    setoid_replace (q_fact (2 * (2 * m + 1 - j) + 1)) with (q_fact (4 * m + 3 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
    setoid_replace (q_fact (4 * m + 3 - 2 * (2 * m + 1 - j))) with (q_fact (2 * j + 1)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
    field.
    all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
         intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
  (* 5. 代入副本：Hz == 偶部 + 奇部 == 0（q_pow_neg1 后 even − odd == 0）
         even == 2·Σ_{j=0}^{m} E_j + E_{m+1}，odd == 2·Σ_{j=0}^{m} O_j
         ⟹ (2Σ_{j=0}^{m} E_j + E_{m+1}) − 2Σ_{j=0}^{m} O_j == 0
         ⟹ 2Σ_{j=0}^{m} O_j − 2Σ_{j=0}^{m} E_j == E_{m+1} == 1/((2m+2)!(2m+2)!) *)
  (* Hz 是 even + odd 形态（O 带负号）：(2ΣE + E_{m+1}) + (2ΣO') == 0，O' = -1/X *)
  setoid_rewrite HmirE in Hz.
  setoid_rewrite HmirO in Hz.
  (* Hz 里 O 部分是 2·Σ(-1/X)——先用 HzO 模式归约负号 *)
  assert (HzO : sum_upto (m + 1) (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) ==
                - sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))).
  { setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_neg (m + 1)             (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    apply qeqT_imp_qeq.
    apply (sum_upto_ext (m + 1)             (fun j => (- 1) / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))             (fun j => - (1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  rewrite HzO in Hz.
  (* Hz（E_{m+1} 归约）：2·Σ_{j=0}^{m} E_j + E_{m+1} − 2·Σ_{j=0}^{m} O_j == 0 *)
  (* E_{m+1} = 1/((2m+2)!(2m+2)!)——set 提取 + change 验证 + Qeq 移项 *)
  set (A := 2 * (sum_upto m
                    (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))) +
             (2 * (- sum_upto m
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j)))))).
  (* Hz 的 LHS 是否 == A：change 验证 *)
  (* 注意 Hz 的 O 部分经 HzO 后是 2·(-ΣO_j)，E 部分是 2·(ΣE_j + E_{m+1}) *)
  (* 由于 Hz 结构可能不同，先打印/用 change 尝试 *)
  (* 直接构造 Hmoved：2ΣO − 2ΣE == E_{m+1}（Qeq 移项模式） *)
  assert (Hmoved : 2 * sum_upto (m + 1)
                     (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))) -
                    2 * sum_upto (m + 1)
                      (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) ==
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
  { (* Hz : 2·ΣE + E_{m+1} + 2·(-ΣO) == 0（HzO 后）
         Hmoved : 2ΣO - 2ΣE == E_{m+1}
         用 qeq_moved_neg2 于 (A=2ΣE, B=E_{m+1}, C=ΣO)：
         A + B + 2*(-C) == 0 ⟹ 2C - A == B——前提恰是 Hz（ring 等价：Hz 是 2ΣE + E_{m+1} + 2*(-ΣO) == 0） *)
    apply qeqT_imp_qeq.
    apply (qeq_moved_neg2
             (2 * sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))))
             (1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1))))
             (sum_upto (m + 1) (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    apply qeq_imp_qeqT.
    (* 需证：2ΣE + E_{m+1} + 2*(-ΣO) == 0——Hz 的 ring 等价（transitivity 于 Hz LHS） *)
    transitivity (2 * sum_upto (m + 1)
                    (fun j => 1 / (q_fact (2 * j) * q_fact (4 * m + 4 - 2 * j))) +
                   1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1))) +
                   2 * (- sum_upto (m + 1)
                          (fun j => 1 / (q_fact (2 * j + 1) * q_fact (4 * m + 3 - 2 * j))))).
    - unfold Qdiv. ring.
    - exact Hz. }
  (* 6. vander LHS == −2·Σ_{k=0}^{m} E_k + 2·Σ_{k=0}^{m} O_k（E''_j=E_{j+1} 换元 + 尾项合并）
         目标 LHS：sum_upto m (fun j => -2/((4m+2−2j)!(2j+2)!) + 2/((4m+1−2j)!(2j+3)!))
         − 2/((4m+4)!(0)!) + 2/((4m+3)!(1)!)
         == -2·Σ_{k=1}^{m} E_k + 2·Σ_{k=1}^{m} O_k − 2·E_0 + 2·O_0
         == -2·Σ_{k=0}^{m} E_k + 2·Σ_{k=0}^{m} O_k
         而 Hmoved : 2Σ_{0}^{m}O − 2Σ_{0}^{m}E == E_{m+1}
         且 E_{m+1} == 1/((2m+2)!(2m+2)!)（分母交换） *)
  (* vander LHS 换元：sum_upto_ext 于 j，E''_j 换 E_{j+1} 形态（先写分母同形） *)
  assert (Hlin : sum_upto m
                   (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)) +
                             2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) ==
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) +
                 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m              (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hsc1 : sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) ==
                   - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))).
    assert (Hpre1538_26 : (forall i,QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))) i))).
      {  intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m                (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))                (fun j => - 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_26)).
      apply (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))))). }
    assert (Hsc2 : sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) ==
                   2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
    assert (Hpre1538_25 : (forall i,QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
      {  intro j. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m                (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))                (fun j => 2 * (1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_25)).
      apply (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))). }
    setoid_rewrite Hsc1. setoid_rewrite Hsc2.
    reflexivity. }
  (* Hlin 的 RHS 项换元到 E/O（k=j+1）：1/((2j+2)!(4m+2−2j)!) == E_{j+1} 等——需 sum_upto_ext *)
  (* 目标最终：-2Σ_{j=0}^{m}E_{j+1} + 2Σ_{j=0}^{m}O_{j+1} - 2E_0 + 2O_0 == 1/((2m+2)!(2m+2)!)
     而 Hmoved : 2Σ_{0}^{m}O_j - 2Σ_{0}^{m}E_j == E_{m+1}
     E_{j+1} vs E_j 差一索引——需换元 sum_upto_ext (fun j => E_{j+1}) 为 sum_upto m ... *)
  (* 这一步较繁：vander LHS 的 Σ_{j=0}^{m-1} 是 m 项（j=0..m-1），而 Hmoved 的 Σ_{j=0}^{m} 是 m+1 项
     vander LHS = -2Σ_{j=0}^{m-1}E''_j + 2Σ_{j=0}^{m-1}O''_j + tail
                = -2Σ_{k=1}^{m}E_k + 2Σ_{k=1}^{m}O_k - 2E_0 + 2O_0
                = -2Σ_{k=0}^{m}E_k + 2Σ_{k=0}^{m}O_k
     与 Hmoved 完全对齐 ✓ *)
  (* 收尾：vander LHS == -2Σ_{k=0}^{m}E_k + 2Σ_{k=0}^{m}O_k == Hmoved LHS == E_{m+1} == RHS *)
  setoid_rewrite Hlin.
  (* 目标：-2·Σ_{j=0}^{m-1}(1/E''_j) + 2·Σ_{j=0}^{m-1}(1/O''_j) - 2/((4m+4)!0!) + 2/((4m+3)!1!) == RHS
     E''_j = 1/((4m+2-2j)!(2j+2)!)，O''_j = 1/((4m+1-2j)!(2j+3)!) *)
  (* 换元：E''_j == E_{j+1}（E_k = 1/((4m+4-2k)!(2k)!)），sum_upto_shift 于 E 部分 *)
  assert (HshiftE : sum_upto m (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) ==
                    sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) -
                    1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0))).
  { apply (qeqT_imp_qeq _ _ (sum_upto_shift m (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))))). }
  (* 目标 LHS 的 E 部分：-2·Σ(1/E''_j)（负号在 sum 外）——对 sum 内部 ext 换元 E''_j → E_{j+1} *)
  assert (Hpre1538_24 : (forall i,QeqT ( (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) i))).
  {  intro j. apply qeq_imp_qeqT. assert (H1 : (4 * m + 4 - 2 * (j + 1) = 4 * m + 2 - 2 * j)%nat) by lia.
       assert (H2 : (2 * (j + 1) = 2 * j + 2)%nat) by lia.
       setoid_replace (q_fact (4 * m + 4 - 2 * (j + 1))) with (q_fact (4 * m + 2 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
       setoid_replace (q_fact (2 * (j + 1))) with (q_fact (2 * j + 2)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))            (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))) Hpre1538_24)).
  assert (Hpre1538_23 : (forall i,QeqT ( (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) i))).
  {  intro j. apply qeq_imp_qeqT. assert (H1 : (4 * m + 3 - 2 * (j + 1) = 4 * m + 1 - 2 * j)%nat) by lia.
       assert (H2 : (2 * (j + 1) + 1 = 2 * j + 3)%nat) by lia.
       setoid_replace (q_fact (4 * m + 3 - 2 * (j + 1))) with (q_fact (4 * m + 1 - 2 * j)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H1. }
       setoid_replace (q_fact (2 * (j + 1) + 1)) with (q_fact (2 * j + 3)).
       2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact H2. }
       reflexivity. }
  rewrite (qeqT_imp_qeq _ _ (sum_upto_ext m            (fun j => 1 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))            (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) Hpre1538_23)).
  (* 尾项并入：-2/((4m+4)!·0!) == -2·(1/((4m+4-2·0)!(2·0)!)) = -2·E_0 项；+2/((4m+3)!·1!) == +2·O_0 项
     目标：-2·Σ_{j=0}^{m-1}(1/E_{j+1}) + 2·Σ_{j=0}^{m-1}(1/O_{j+1}) - 2·E_0 + 2·O_0 == RHS
     用 HshiftE：Σ_{j=0}^{m-1}(1/E_{j+1}) == Σ_{k=0}^{m}(1/E_k) - E_0（E_0 = 1/((4m+4)!·0!)） *)
  setoid_replace (sum_upto m (fun j => 1 / (q_fact (4 * m + 4 - 2 * (j + 1)) * q_fact (2 * (j + 1)))))
    with (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) -
           1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0))).
  2: { exact HshiftE. }
  (* 目标：-2·(Σ_{k=0}^{m}(1/E_k) - E_0) + 2·Σ_{j=0}^{m-1}(1/O_{j+1}) - 2·E_0 + 2·O_0 == RHS
     O 部分同样 shift：Σ_{j=0}^{m-1}(1/O_{j+1}) == Σ_{k=0}^{m}(1/O_k) - O_0 *)
  assert (HshiftO : sum_upto m (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))) ==
                    sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                    1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1))).
  { apply (qeqT_imp_qeq _ _ (sum_upto_shift m (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))))). }
  setoid_replace (sum_upto m (fun j => 1 / (q_fact (4 * m + 3 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 1))))
    with (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
           1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1))).
  2: { exact HshiftO. }
  (* 目标：-2·(ΣE_k - E_0) + 2·(ΣO_k - O_0) - 2·E_0 + 2·O_0 == RHS
     ⟹ -2·ΣE_k + 2E_0 + 2·ΣO_k - 2O_0 - 2E_0 + 2O_0 == -2ΣE_k + 2ΣO_k == RHS（ring 消 E_0/O_0） *)
  (* 归约 E_0/O_0 字面：E_0 = 1/((4m+4)!·0!)、O_0 = 1/((4m+3)!·1!)——与尾项相同（ring） *)
  (* 目标现在是：-2·(Σ_{k=0}^{m}(1/E_k) - 1/E_0) + 2·(Σ_{k=0}^{m}(1/O_k) - 1/O_0) - 2/((4m+4)!·0!) + 2/((4m+3)!·1!) == RHS
     ring 展开：-2ΣE + 2/E_0 + 2ΣO - 2/O_0 - 2/E_0 + 2/O_0 == -2ΣE + 2ΣO（E_0/O_0 抵消） *)
  (* 用 Hmoved：2ΣO - 2ΣE == E_{m+1}；E_{m+1} == 1/((2m+2)!(2m+2)!)（分母交换） *)
  transitivity (2 * sum_upto (m + 1)
                  (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                2 * sum_upto (m + 1)
                  (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))).
  - (* 目标 LHS == 2ΣO - 2ΣE（E_0/O_0 抵消）——assert 独立检验目标后 exact（找差异） *)
    assert (Htmp : - 2 * (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) +
                          - (1 / (q_fact (4 * m + 4) * q_fact 0))) +
                   2 * (sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                          (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))) -
                   2 / (q_fact (4 * m + 4) * q_fact 0) +
                   2 / (q_fact (4 * m + 3) * q_fact 1) ==
                   2 * sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) -
                   2 * sum_upto (m + 1) (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))).
    { unfold Qminus. unfold Qdiv.
      (* O_0 字面归约：change 于整个 1/(...) 项（可转换：4m+3-2·0 == 4m+3、2·0+1 == 1） *)
      change (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
        with (1 / (q_fact (4 * m + 3) * q_fact 1)).
      (* ring_simplify 分配 -2*(Σ+...) 并归约 1*x，再 ring（E_0/O_0 抵消） *)
      ring_simplify.
      (* ring_simplify 后 O_0 是 2 * Qinv (q_fact (4m+3-2*0) * q_fact (2*0+1)) 未归约——change 归约 *)
      (* O_0 项：-2 * / (q_fact (4m+3-2*0) * q_fact (2*0+1))——setoid_replace 归约整体（Qinv Proper） *)
      setoid_replace (- 2 * / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
        with (- 2 * / (q_fact (4 * m + 3) * q_fact 1)).
      2: { setoid_replace (q_fact (4 * m + 3 - 2 * 0)) with (q_fact (4 * m + 3)).
           2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
           setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
           2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
           reflexivity. }
      ring. }
    (* vander 目标的 E_0/O_0 未归约（1/(q_fact (4m+4-2*0) * q_fact (2*0)) 等）——先归约再 exact Htmp *)
    setoid_replace (1 / (q_fact (4 * m + 4 - 2 * 0) * q_fact (2 * 0)))
      with (1 / (q_fact (4 * m + 4) * q_fact 0)).
    2: { setoid_replace (q_fact (4 * m + 4 - 2 * 0)) with (q_fact (4 * m + 4)).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         setoid_replace (q_fact (2 * 0)) with (q_fact 0).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         reflexivity. }
    setoid_replace (1 / (q_fact (4 * m + 3 - 2 * 0) * q_fact (2 * 0 + 1)))
      with (1 / (q_fact (4 * m + 3) * q_fact 1)).
    2: { setoid_replace (q_fact (4 * m + 3 - 2 * 0)) with (q_fact (4 * m + 3)).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         setoid_replace (q_fact (2 * 0 + 1)) with (q_fact 1).
         2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
         reflexivity. }
    unfold Qminus. unfold Qdiv.
    ring_simplify.
    ring.
  - (* 2ΣO - 2ΣE == E_{m+1}（Hmoved） *)
    transitivity (1 / (q_fact (2 * (m + 1)) * q_fact (4 * m + 4 - 2 * (m + 1)))).
    + (* 目标 LHS 的 O 部分换序（(4m+3-2k)!(2k+1)! -> (2k+1)!(4m+3-2k)!，匹配 Hmoved） *)
      assert (Hpre1538_22 : (forall i,QeqT ( (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1))) i ) ( (fun k => 1 / (q_fact (2 * k + 1) * q_fact (4 * m + 3 - 2 * k))) i))).
        {  intro k. apply qeq_imp_qeqT. field.
             all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
                  intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
      { rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m + 1)                  (fun k => 1 / (q_fact (4 * m + 3 - 2 * k) * q_fact (2 * k + 1)))                  (fun k => 1 / (q_fact (2 * k + 1) * q_fact (4 * m + 3 - 2 * k))) Hpre1538_22)).
        assert (Hpre1538_21 : (forall i,QeqT ( (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k))) i ) ( (fun k => 1 / (q_fact (2 * k) * q_fact (4 * m + 4 - 2 * k))) i))).
        {  intro k. apply qeq_imp_qeqT. field.
             all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
                  intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)). }
        rewrite (qeqT_imp_qeq _ _ (sum_upto_ext (m + 1)                  (fun k => 1 / (q_fact (4 * m + 4 - 2 * k) * q_fact (2 * k)))                  (fun k => 1 / (q_fact (2 * k) * q_fact (4 * m + 4 - 2 * k))) Hpre1538_21)).
        exact Hmoved. }
    + (* E_{m+1} == RHS：分母交换 1/((2m+2)!(2m+2)!) == 1/((2(m+1))!(4m+4−2(m+1))!) *)
      { assert (Hmid : (2 * (m + 1) = 2 * m + 2)%nat) by lia.
        assert (Hmid2 : (4 * m + 4 - 2 * (m + 1) = 2 * m + 2)%nat) by lia.
        setoid_replace (q_fact (2 * (m + 1))) with (q_fact (2 * m + 2)).
        2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid. }
        setoid_replace (q_fact (4 * m + 4 - 2 * (m + 1))) with (q_fact (2 * m + 2)).
        2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hmid2. }
        reflexivity. }
Qed.

End QExpEOSplit.
(* ============ 配对论证（备份 92 并入，来自 _dbg_kdr.v 检验全部通过） ============
   row_pair_main：行差分闭合（分层组装：a^{4m+6} 抵消 + vander_4m2/4m4 + 低层 refl）
   ksum_diff_row：corr 差分 == RHS（corr_diff_expand + 换元 + row_pair_main）——配对论证完结 *)
Lemma esq_row_nat_eq2 : forall (N i1 i2 : nat) (a : Q),
  i1 = i2 ->QeqT ( esq_row N i1 a ) ( esq_row N i2 a).
Proof. intros. subst. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma sum_upto_opp2 : forall (n : nat) (f : nat -> Q),QeqT (
  sum_upto n (fun j => - (2 * f j)) ) ( - (2 * sum_upto n f)).
Proof.
  intros n f.
  apply qeq_imp_qeqT.
  induction n as [| n' IH]; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.

Lemma esq_pair : forall (m j : nat) (a : Q), (j < m)%nat ->QeqT (
  - 2 * esq_row (2 * m + 1 - (j + 1)) (j + 1 + 2) a
  + 2 * esq_row (2 * m - j) (j + 1) a ) (
  - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
  - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
Proof.
  intros m j a Hj.
  apply qeq_imp_qeqT.
  assert (Ha : (2 * m + 1 - (j + 1) = 2 * m - j)%nat) by lia.
  assert (Hb : (j + 1 + 2 = j + 3)%nat) by lia.
  rewrite Ha. rewrite Hb.
  (* esq_row (2m−j) (j+3) == esq_row (2m−j) (j+1) + T_{j+2} + T_{j+3}（esq_row_succ 两次） *)
  assert (Hexp : esq_row (2 * m - j) (j + 3) a ==
          esq_row (2 * m - j) (j + 1) a +
          q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 1))) +
          q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 2)))).
  { assert (Hn : (j + 3 = Datatypes.S (j + 2))%nat) by lia.
    rewrite Hn.
    rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m - j) (j + 2) a)).
    setoid_replace (esq_row (2 * m - j) (j + 2) a) with (esq_row (2 * m - j) (Datatypes.S (j + 1)) a).
    2: { apply qeqT_imp_qeq. apply esq_row_nat_eq2. lia. }
    rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m - j) (j + 1) a)).
    reflexivity. }
  rewrite Hexp.
  (* T_{j+2} == q_pow a (4m+4)/((4m−2j)!(2j+4)!)：q_pow/q_fact 参数归约 *)
  assert (Ht2 : q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 1))) ==
                q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))).
  { setoid_replace (q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 1))) with (q_pow a (4 * m + 4)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - j) + 2 * Datatypes.S (j + 1))%nat (4 * m + 4)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - j))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 1))) with (q_fact (2 * j + 4)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  (* T_{j+3} == q_pow a (4m+6)/((4m−2j)!(2j+6)!) *)
  assert (Ht3 : q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2)) / (q_fact (2 * (2 * m - j)) * q_fact (2 * Datatypes.S (j + 2))) ==
                q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
  { setoid_replace (q_pow a (2 * (2 * m - j) + 2 * Datatypes.S (j + 2))) with (q_pow a (4 * m + 6)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - j) + 2 * Datatypes.S (j + 2))%nat (4 * m + 6)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - j))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 2))) with (q_fact (2 * j + 6)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite Ht2.
  setoid_rewrite Ht3.
  unfold Qdiv in *. ring.
Qed.

Lemma osq_pair : forall (m j : nat) (a : Q), (j < m)%nat ->QeqT (
  2 * osq_row (2 * m - (j + 1)) (j + 1 + 1) a
  - 2 * osq_row (2 * m - 1 - j) j a ) (
  2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
  + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
Proof.
  intros m j a Hj.
  apply qeq_imp_qeqT.
  assert (Ha : (2 * m - (j + 1) = 2 * m - 1 - j)%nat) by lia.
  assert (Hb : (j + 1 + 1 = j + 2)%nat) by lia.
  rewrite Ha. rewrite Hb.
  (* osq_row (2m−1−j) (j+2) == osq_row (2m−1−j) j + T'_{j+1} + T'_{j+2}（osq_row_succ 两次） *)
  assert (Hexp : osq_row (2 * m - 1 - j) (j + 2) a ==
          osq_row (2 * m - 1 - j) j a +
          q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S j + 1)) +
          q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S (j + 1) + 1))).
  { assert (Hn : (j + 2 = Datatypes.S (j + 1))%nat) by lia.
    rewrite Hn.
    rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m - 1 - j) (j + 1) a)).
    setoid_replace (osq_row (2 * m - 1 - j) (j + 1) a) with (osq_row (2 * m - 1 - j) (Datatypes.S j) a).
    2: { apply qeqT_imp_qeq. apply osq_row_nat_eq2. lia. }
    rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m - 1 - j) j a)).
    reflexivity. }
  rewrite Hexp.
  (* T'_{j+1} == q_pow a (4m+2)/((4m−1−2j)!(2j+3)!) *)
  assert (Ht2 : q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S j + 1)) ==
                q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))).
  { setoid_replace (q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2)) with (q_pow a (4 * m + 2)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - 1 - j) + 2 * Datatypes.S j + 2)%nat (4 * m + 2)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - 1 - j) + 1)) with (q_fact (4 * m - 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S j + 1)) with (q_fact (2 * j + 3)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  (* T'_{j+2} == q_pow a (4m+4)/((4m−1−2j)!(2j+5)!) *)
  assert (Ht3 : q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2) / (q_fact (2 * (2 * m - 1 - j) + 1) * q_fact (2 * Datatypes.S (j + 1) + 1)) ==
                q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
  { setoid_replace (q_pow a (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2)) with (q_pow a (4 * m + 4)).
    2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m - 1 - j) + 2 * Datatypes.S (j + 1) + 2)%nat (4 * m + 4)%nat). lia. }
    setoid_replace (q_fact (2 * (2 * m - 1 - j) + 1)) with (q_fact (4 * m - 1 - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    setoid_replace (q_fact (2 * Datatypes.S (j + 1) + 1)) with (q_fact (2 * j + 5)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. lia. }
    reflexivity. }
  setoid_rewrite Ht2.
  setoid_rewrite Ht3.
  unfold Qdiv in *. ring.
Qed.

Lemma esq_row_diff_closed : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto m (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a
                      + 2 * esq_row (2 * m - j) (j + 1) a) ) (
  2 * esq_row (m + 1) m a - 2 * esq_row (2 * m + 1) 2 a
  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* ① 拆分 f = esq- + esq+ *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m            (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a)            (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  (* ② Σ esq- == esq-@0 + Σ_{j<m−1} esq-@(j+1)（sum_upto_shift 移首项） *)
  assert (Hsh : sum_upto m (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a) ==
                (- 2 * esq_row (2 * m + 1) 2 a) +
                sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1)              (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a) (eq_sym Hm1))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1)                      (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a))).
    assert (Hf0 : (fun k : nat => - 2 * esq_row (2 * m + 1 - k) (k + 2) a) 0%nat ==
                  - 2 * esq_row (2 * m + 1) 2 a).
    { change ((fun k : nat => - 2 * esq_row (2 * m + 1 - k) (k + 2) a) 0%nat) with
        (- 2 * esq_row (2 * m + 1 - 0) (0 + 2) a).
      assert (Hn1 : (2 * m + 1 - 0 = 2 * m + 1)%nat) by lia.
      assert (Hn2 : (0 + 2 = 2)%nat) by lia.
      rewrite Hn1. rewrite Hn2.
      reflexivity. }
    setoid_rewrite Hf0.
    unfold Qminus. ring. }
  (* ③ Σ esq+ == Σ_{j<m−1} esq+@j + esq+@(m−1)（拆末项） *)
  assert (Hsl : sum_upto m (fun j => 2 * esq_row (2 * m - j) (j + 1) a) ==
                sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a) +
                2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 * esq_row (2 * m - j) (j + 1) a) Hms)).
    reflexivity. }
  (* ④ 替换 + 重组（ring 证 Hre，把 ΣA' 与 ΣB 并拢） *)
  setoid_rewrite Hsh.
  setoid_rewrite Hsl.
  assert (Hre : ((- 2 * esq_row (2 * m + 1) 2 a) +
                 sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)) +
                (sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a) +
                 2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a) ==
                (- 2 * esq_row (2 * m + 1) 2 a) +
                (2 * esq_row (2 * m - (m - 1)) (m - 1 + 1) a) +
                (sum_upto (m - 1) (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a) +
                 sum_upto (m - 1) (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  { ring. }
  setoid_rewrite Hre.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a)                      (fun j => 2 * esq_row (2 * m - j) (j + 1) a))).
  (* ⑤ 逐点 esq_pair（配对和 → −2·T4 − 2·T6） *)
  assert (Hpre1538_20 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) i ) ( (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))                            - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (esq_pair m j a). lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                    (fun j => - 2 * esq_row (2 * m + 1 - (j + 1)) ((j + 1) + 2) a
                            + 2 * esq_row (2 * m - j) (j + 1) a)
                    (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))                            - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) Hpre1538_20)).
  (* ⑥ 提出 −2（逐点 (-2·a)/D == -2·(a/D)，再 sum_upto_plus/scale） *)
  assert (Hstep4 : forall j, - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)) ==
                            - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hstep6 : forall j, - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)) ==
                            - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hsum : sum_upto (m - 1) (fun j =>
                    - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
                    - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) ==
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))).
  assert (Hpre1538_19 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)) - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i ) ( (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))                              - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                      (fun j => - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))
                              - 2 * q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                      (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))                              - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) Hpre1538_19)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))                      (fun j => - (2 * (q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_opp2 (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
    ring. }
  setoid_rewrite Hsum.
  (* ⑦ 末项归约：esq+@(m−1) == 2·esq_row (m+1) m *)
  assert (Hma : (2 * m - (m - 1) = m + 1)%nat) by lia.
  assert (Hmb : (m - 1 + 1 = m)%nat) by lia.
  rewrite Hma. rewrite Hmb.
  (* ⑧ ring 组装 *)
  unfold Qdiv in *. ring.
Qed.

Lemma osq_row_diff_closed : forall (m : nat) (a : Q), (1 <= m)%nat ->QeqT (
  sum_upto m (fun j => 2 * osq_row (2 * m - j) (j + 1) a
                      - 2 * osq_row (2 * m - 1 - j) j a) ) (
  - 2 * osq_row m (m - 1) a + 2 * osq_row (2 * m) 1 a
  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
Proof.
  intros m a Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* ① 拆分 f = osq+ + osq-（目标 LHS 是 A - B 记法 == A + Qopp B，g 用 Qopp 形态） *)
  rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m            (fun j => 2 * osq_row (2 * m - j) (j + 1) a)            (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  (* ② Σ osq+ == osq+@0 + Σ_{j<m−1} osq+@(j+1)（sum_upto_shift 移首项） *)
  assert (Hsh : sum_upto m (fun j => 2 * osq_row (2 * m - j) (j + 1) a) ==
                (2 * osq_row (2 * m) 1 a) +
                sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1)              (fun j => 2 * osq_row (2 * m - j) (j + 1) a) (eq_sym Hm1))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1)                      (fun j => 2 * osq_row (2 * m - j) (j + 1) a))).
    assert (Hf0 : (fun k : nat => 2 * osq_row (2 * m - k) (k + 1) a) 0%nat ==
                  2 * osq_row (2 * m) 1 a).
    { change ((fun k : nat => 2 * osq_row (2 * m - k) (k + 1) a) 0%nat) with
        (2 * osq_row (2 * m - 0) (0 + 1) a).
      assert (Hn1 : (2 * m - 0 = 2 * m)%nat) by lia.
      assert (Hn2 : (0 + 1 = 1)%nat) by lia.
      rewrite Hn1. rewrite Hn2.
      reflexivity. }
    setoid_rewrite Hf0.
    unfold Qminus. ring. }
  (* ③ Σ osq- == Σ_{j<m−1} osq-@j + osq-@(m−1)（拆末项） *)
  assert (Hsl : sum_upto m (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) ==
                sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) +
                (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) Hms)).
    reflexivity. }
  (* ④ 替换 + 重组 *)
  setoid_rewrite Hsh.
  setoid_rewrite Hsl.
  assert (Hre : ((2 * osq_row (2 * m) 1 a) +
                 sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)) +
                (sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)) +
                 (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a))) ==
                (2 * osq_row (2 * m) 1 a) +
                (- (2 * osq_row (2 * m - 1 - (m - 1)) (m - 1) a)) +
                (sum_upto (m - 1) (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a) +
                 sum_upto (m - 1) (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  { ring. }
  setoid_rewrite Hre.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a)                      (fun j => - (2 * osq_row (2 * m - 1 - j) j a)))).
  (* ⑤ 逐点 osq_pair（配对和 → 2·T'_{4m+2} + 2·T'_{4m+4}） *)
  assert (Hpre1538_18 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a - 2 * osq_row (2 * m - 1 - j) j a) i ) ( (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))                            + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply qeqT_imp_qeq. apply (osq_pair m j a). lia. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                    (fun j => 2 * osq_row (2 * m - (j + 1)) ((j + 1) + 1) a
                            - 2 * osq_row (2 * m - 1 - j) j a)
                    (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))                            + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) Hpre1538_18)).
  (* ⑥ 提出 2（逐点 (2·a)/D == 2·(a/D)，再 sum_upto_plus/scale） *)
  assert (Hstep2 : forall j, 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)) ==
                            2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hstep4 : forall j, 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)) ==
                            2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
  { intro j. unfold Qdiv. ring. }
  assert (Hsum : sum_upto (m - 1) (fun j =>
                    2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
                    + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) ==
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))).
  assert (Hpre1538_17 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)) + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))                              + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
  { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)                      (fun j => 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))
                              + 2 * q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                      (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))                              + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_17)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus (m - 1)                      (fun j => 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))                      (fun j => 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    ring. }
  setoid_rewrite Hsum.
  (* ⑦ 末项归约：osq-@(m−1) == −2·osq_row m (m−1) *)
  assert (Hma : (2 * m - 1 - (m - 1) = m)%nat) by lia.
  rewrite Hma.
  (* ⑧ ring 组装 *)
  unfold Qdiv in *. ring.
Qed.

Lemma row_pair_esq2_expand : forall (m : nat) (a : Q),QeqT (
  esq_row (2 * m + 1) 2 a ) (
  q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0) +
  q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2) +
  q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 1) 1 a)).
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 1) 0 a)).
  change (esq_row (2 * m + 1) 0 a) with
    (q_pow a (2 * (2 * m + 1)) / (q_fact (2 * (2 * m + 1)) * q_fact 0)).
  assert (Hn0 : (2 * (2 * m + 1) = 4 * m + 2)%nat) by lia.
  assert (Hn1 : (2 * (2 * m + 1) + 2 * Datatypes.S 0 = 4 * m + 4)%nat) by lia.
  assert (Hn2 : (2 * (2 * m + 1) + 2 * Datatypes.S 1 = 4 * m + 6)%nat) by lia.
  assert (Hf1 : (2 * Datatypes.S 0 = 2)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 1 = 4)%nat) by lia.
  setoid_replace (q_pow a (2 * (2 * m + 1))) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1))%nat (4 * m + 2)%nat). exact Hn0. }
  setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * Datatypes.S 0)) with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1) + 2 * Datatypes.S 0)%nat (4 * m + 4)%nat). exact Hn1. }
  setoid_replace (q_pow a (2 * (2 * m + 1) + 2 * Datatypes.S 1)) with (q_pow a (4 * m + 6)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m + 1) + 2 * Datatypes.S 1)%nat (4 * m + 6)%nat). exact Hn2. }
  setoid_replace (q_fact (2 * (2 * m + 1))) with (q_fact (4 * m + 2)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hn0. }
  setoid_replace (q_fact (2 * Datatypes.S 0)) with (q_fact 2).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf1. }
  setoid_replace (q_fact (2 * Datatypes.S 1)) with (q_fact 4).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf2. }
  reflexivity.
Qed.

Lemma row_pair_osq1_expand : forall (m : nat) (a : Q),QeqT (
  osq_row (2 * m) 1 a ) (
  q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1) +
  q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (osq_row_succ (2 * m) 0 a)).
  change (osq_row (2 * m) 0 a) with
    (q_pow a (2 * (2 * m) + 2) / (q_fact (2 * (2 * m) + 1) * q_fact 1)).
  assert (Hn0 : (2 * (2 * m) + 2 = 4 * m + 2)%nat) by lia.
  assert (Hn1 : (2 * (2 * m) + 2 * Datatypes.S 0 + 2 = 4 * m + 4)%nat) by lia.
  assert (Hf1 : (2 * (2 * m) + 1 = 4 * m + 1)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 0 + 1 = 3)%nat) by lia.
  setoid_replace (q_pow a (2 * (2 * m) + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m) + 2)%nat (4 * m + 2)%nat). exact Hn0. }
  setoid_replace (q_pow a (2 * (2 * m) + 2 * Datatypes.S 0 + 2)) with (q_pow a (4 * m + 4)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * (2 * m) + 2 * Datatypes.S 0 + 2)%nat (4 * m + 4)%nat). exact Hn1. }
  setoid_replace (q_fact (2 * (2 * m) + 1)) with (q_fact (4 * m + 1)).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf1. }
  setoid_replace (q_fact (2 * Datatypes.S 0 + 1)) with (q_fact 3).
  2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hf2. }
  reflexivity.
Qed.

Lemma row_pair_tail_expand : forall (m : nat) (a : Q),QeqT (
  - 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
  2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ) (
  - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1)).
Proof.
  intros m a.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (esq_row_succ (2 * m + 2) 0 a)).
  change (esq_row (2 * m + 2) 0 a) with
    (q_pow a (2 * (2 * m + 2)) / (q_fact (2 * (2 * m + 2)) * q_fact 0)).
  change (osq_row (2 * m + 1) 0 a) with
    (q_pow a (2 * (2 * m + 1) + 2) / (q_fact (2 * (2 * m + 1) + 1) * q_fact 1)).
  assert (Hn1 : (2 * (2 * m + 2) = 4 * m + 4)%nat) by lia.
  assert (Hn2 : (2 * (2 * m + 2) + 2 * Datatypes.S 0 = 4 * m + 6)%nat) by lia.
  assert (Hn3 : (2 * (2 * m + 1) + 2 = 4 * m + 4)%nat) by lia.
  assert (Hf2 : (2 * Datatypes.S 0 = 2)%nat) by lia.
  assert (Hf3 : (2 * (2 * m + 1) + 1 = 4 * m + 3)%nat) by lia.
  (* 参数替换用 Leibniz rewrite（setoid_replace 的转换匹配会误伤 Q 数字 2 ≡ q_fact 2） *)
  rewrite Hn2. rewrite Hf2. rewrite Hn1. rewrite Hn3. rewrite Hf3.
  unfold Qdiv in *. ring.
Qed.

Lemma row_pair_high6 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 4)
  - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
  + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))
  ) ( 0).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hm1 : ((m - 1) + 1 = m)%nat) by lia.
  set (f' := fun j : nat => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))).
  assert (Hf0 : f' 0%nat == 1 / (q_fact (4 * m + 2) * q_fact 4)).
  { unfold f'. change (1 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0 + 4)) ==
                       1 / (q_fact (4 * m + 2) * q_fact 4)).
    assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
    assert (Hb : (2 * 0 + 4 = 4)%nat) by lia.
    setoid_replace (q_fact (4 * m + 2 - 2 * 0)) with (q_fact (4 * m + 2)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Ha. }
    setoid_replace (q_fact (2 * 0 + 4)) with (q_fact 4).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hb. }
    reflexivity. }
  assert (Hfs : forall j, f' (j + 1)%nat ==
                          1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
  { intro j. unfold f'.
    change (1 / (q_fact (4 * m + 2 - 2 * (j + 1)) * q_fact (2 * (j + 1) + 4)) ==
            1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))).
    assert (Ha : (4 * m + 2 - 2 * (j + 1) = 4 * m - 2 * j)%nat) by lia.
    assert (Hb : (2 * (j + 1) + 4 = 2 * j + 6)%nat) by lia.
    setoid_replace (q_fact (4 * m + 2 - 2 * (j + 1))) with (q_fact (4 * m - 2 * j)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Ha. }
    setoid_replace (q_fact (2 * (j + 1) + 4)) with (q_fact (2 * j + 6)).
    2: { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hb. }
    reflexivity. }
  assert (Hsplit : sum_upto m f' == f' 0%nat + sum_upto (m - 1) (fun j => f' (j + 1)%nat)).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m ((m - 1) + 1) f' (eq_sym Hm1))).
    assert (Hshift : sum_upto (m - 1) (fun j => f' (j + 1)%nat) ==
                     sum_upto ((m - 1) + 1) f' - f' 0%nat).
    { apply (qeqT_imp_qeq _ _ (sum_upto_shift (m - 1) f')). }
    setoid_rewrite Hshift.
    unfold Qminus. ring. }
  setoid_rewrite Hsplit.
  assert (Hpre1538_16 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => f' (j + 1)%nat) i ) ( (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i))).
  {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hfs j). }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1) (fun j => f' (j + 1)%nat)                   (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) Hpre1538_16)).
  setoid_rewrite Hf0.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma row_pair_mid4 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 2)
  - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
  + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
  + 2 / (q_fact (4 * m + 1) * q_fact 3)
  - 2 / (q_fact (4 * m + 4) * q_fact 0)
  + 2 / (q_fact (4 * m + 3) * q_fact 1)
  ) ( 1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* H1：前两项 → Σ_{j<m} −2/((4m+2−2j)!(2j+2)!) *)
  assert (H1 : - 2 / (q_fact (4 * m + 2) * q_fact 2)
               - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) ==
               sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2))))).
    assert (Hg0 : - 2 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0 + 2)) ==
                  - 2 / (q_fact (4 * m + 2) * q_fact 2)).
    { assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
      assert (Hb : (2 * 0 + 2 = 2)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2)) ==
                           - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))).
    { intro j. assert (Ha : (4 * m + 2 - 2 * Datatypes.S j = 4 * m - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 2 = 2 * j + 4)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_15 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2))) i ) ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 2)))       (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) Hpre1538_15)).
    setoid_rewrite Hg0.
    assert (Hpre1538_14 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))       (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) Hpre1538_14)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* H2：2·Σ_{j<m−1} 1/((4m−1−2j)!(2j+5)!) + 2/((4m+1)!(3)!) → Σ_{j<m} 2/((4m+1−2j)!(2j+3)!) *)
  assert (H2 : 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
               + 2 / (q_fact (4 * m + 1) * q_fact 3) ==
               sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hg0 : 2 / (q_fact (4 * m + 1 - 2 * 0) * q_fact (2 * 0 + 3)) ==
                  2 / (q_fact (4 * m + 1) * q_fact 3)).
    { assert (Ha : (4 * m + 1 - 2 * 0 = 4 * m + 1)%nat) by lia.
      assert (Hb : (2 * 0 + 3 = 3)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3)) ==
                           2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))).
    { intro j. assert (Ha : (4 * m + 1 - 2 * Datatypes.S j = 4 * m - 1 - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 3 = 2 * j + 5)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_13 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3))) i ) ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 3)))       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) Hpre1538_13)).
    setoid_rewrite Hg0.
    assert (Hpre1538_12 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))       (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_12)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* 组装：先重组（ring 证 Hre，把 H1/H2 的 LHS 并拢为连续子项），再替换 + vander_4m4 *)
  assert (Hre : - 2 / (q_fact (4 * m + 2) * q_fact 2)
                - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                + 2 / (q_fact (4 * m + 1) * q_fact 3)
                - 2 / (q_fact (4 * m + 4) * q_fact 0)
                + 2 / (q_fact (4 * m + 3) * q_fact 1) ==
                (- 2 / (q_fact (4 * m + 2) * q_fact 2)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))
                + (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                   + 2 / (q_fact (4 * m + 1) * q_fact 3))
                - 2 / (q_fact (4 * m + 4) * q_fact 0)
                + 2 / (q_fact (4 * m + 3) * q_fact 1)).
  { unfold Qminus. ring. }
  setoid_rewrite Hre.
  setoid_rewrite H1.
  setoid_rewrite H2.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus m                      (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 2)))                      (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 3))))).
  apply qeqT_imp_qeq.
  apply (vander_4m4 m Hm).
Qed.

Lemma row_pair_mid2 : forall (m : nat), (1 <= m)%nat ->QeqT (
  - 2 / (q_fact (4 * m + 2) * q_fact 0)
  + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
  + 2 / (q_fact (4 * m + 1) * q_fact 1)
  - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
  ) ( - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
Proof.
  intros m Hm.
  apply qeq_imp_qeqT.
  assert (Hms : (m = Datatypes.S (m - 1))%nat) by lia.
  (* H1：中间两项 → Σ_{j<m} 2/((4m+1−2j)!(2j+1)!) *)
  assert (H1 : 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
               + 2 / (q_fact (4 * m + 1) * q_fact 1) ==
               sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1)))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) Hms)).
    rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))).
    assert (Hg0 : 2 / (q_fact (4 * m + 1 - 2 * 0) * q_fact (2 * 0 + 1)) ==
                  2 / (q_fact (4 * m + 1) * q_fact 1)).
    { assert (Ha : (4 * m + 1 - 2 * 0 = 4 * m + 1)%nat) by lia.
      assert (Hb : (2 * 0 + 1 = 1)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hgs : forall j, 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1)) ==
                           2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))).
    { intro j. assert (Ha : (4 * m + 1 - 2 * Datatypes.S j = 4 * m - 1 - 2 * j)%nat) by lia.
      assert (Hb : (2 * Datatypes.S j + 1 = 2 * j + 3)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    assert (Hpre1538_11 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1))) i ) ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m + 1 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j + 1)))       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) Hpre1538_11)).
    setoid_rewrite Hg0.
    assert (Hpre1538_10 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
    {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)       (fun j => 2 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))       (fun j => 2 * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_10)).
    setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) 2 (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    unfold Qdiv in *. unfold Qminus. ring. }
  (* H2：首项 + T 和的 −2·Σ → Σ_{j<m} −2/((4m+2−2j)!(2j)!) − 2/((2m+2)!(2m)!) *)
  assert (Htail : sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                  sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
                  1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))              (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) Hms)).
    change (sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
            1 / (q_fact (4 * m - 2 * (m - 1)) * q_fact (2 * (m - 1) + 2)) ==
            sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
            1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    assert (Htm : 1 / (q_fact (4 * m - 2 * (m - 1)) * q_fact (2 * (m - 1) + 2)) ==
                  1 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    { assert (Ha : (4 * m - 2 * (m - 1) = 2 * m + 2)%nat) by lia.
      assert (Hb : (2 * (m - 1) + 2 = 2 * m)%nat) by lia.
      rewrite Ha. rewrite Hb. reflexivity. }
    setoid_rewrite Htm. reflexivity. }
  assert (H2 : - 2 / (q_fact (4 * m + 2) * q_fact 0)
               - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
               sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) -
               2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { setoid_rewrite Htail.
    assert (Hpre : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                   - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                   sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)))).
    { rewrite (qeqT_imp_qeq _ _ (sum_upto_nat_eq m (Datatypes.S (m - 1))                (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) Hms)).
      rewrite (qeqT_imp_qeq _ _ (sum_upto_rot (m - 1) (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))))).
      assert (Hg0 : - 2 / (q_fact (4 * m + 2 - 2 * 0) * q_fact (2 * 0)) ==
                    - 2 / (q_fact (4 * m + 2) * q_fact 0)).
      { assert (Ha : (4 * m + 2 - 2 * 0 = 4 * m + 2)%nat) by lia.
        assert (Hb : (2 * 0 = 0)%nat) by lia.
        rewrite Ha. rewrite Hb. reflexivity. }
      assert (Hgs : forall j, - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j)) ==
                             - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))).
      { intro j. assert (Ha : (4 * m + 2 - 2 * Datatypes.S j = 4 * m - 2 * j)%nat) by lia.
        assert (Hb : (2 * Datatypes.S j = 2 * j + 2)%nat) by lia.
        rewrite Ha. rewrite Hb. reflexivity. }
      assert (Hpre1538_9 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j))) i ) ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. apply (Hgs j). }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)         (fun j => - 2 / (q_fact (4 * m + 2 - 2 * Datatypes.S j) * q_fact (2 * Datatypes.S j)))         (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) Hpre1538_9)).
      setoid_rewrite Hg0.
      assert (Hpre1538_8 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)         (fun j => - 2 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))         (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_8)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (Hdist : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                    - 2 * (sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) +
                           1 / (q_fact (2 * m + 2) * q_fact (2 * m))) ==
                    (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                     - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))
                    - 2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
    { unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite Hdist.
    setoid_rewrite Hpre.
    unfold Qdiv in *. unfold Qminus. ring. }
  (* 组装：H1/H2 替换后 == vander_4m2 LHS − 2/((2m+2)!(2m)!) == −1/((2m+1)!(2m+1)!) *)
  assert (Hre : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                + 2 / (q_fact (4 * m + 1) * q_fact 1)
                - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))
                + (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                   + 2 / (q_fact (4 * m + 1) * q_fact 1))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hre.
  setoid_rewrite H2.
  setoid_rewrite H1.
  assert (Hre2 : (sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) -
                  2 / (q_fact (2 * m + 2) * q_fact (2 * m))) +
                 sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ==
                 (sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))) +
                  sum_upto m (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))
                 - 2 / (q_fact (2 * m + 2) * q_fact (2 * m))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hre2.
  setoid_rewrite <- (qeqT_imp_qeq _ _ (sum_upto_plus m                      (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j)))                      (fun j => 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))))).
  assert (Hv : sum_upto m (fun j => - 2 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j))
                               + 2 / (q_fact (4 * m + 1 - 2 * j) * q_fact (2 * j + 1))) ==
               2 / (q_fact (2 * m + 2) * q_fact (2 * m)) -
               1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  apply qeqT_imp_qeq.
  { apply (vander_4m2 m Hm). }
  setoid_rewrite Hv.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma row_pair_main : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  sum_upto m
    (fun j =>
       - 2 * esq_row (2 * m + 1 - j) (j + 2) a
       + 2 * esq_row (2 * m - j) (j + 1) a
       + 2 * osq_row (2 * m - j) (j + 1) a
       - 2 * osq_row (2 * m - 1 - j) j a
       + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
       - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
  - 2 * esq_row (2 * m + 2) 1 a
  + 2 * osq_row (2 * m + 1) 0 a
  + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ) (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* ① 行差(j) 逐点重排为 esq(j) + osq(j) + T(j)，再拆三份 *)
  assert (Hpre1538_7 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a + 2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)) - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) i ) ( (fun j => (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) + (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a) + (2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))        - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i))).
  { intros j Hlt. apply qeq_imp_qeqT. ring. }
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m    (fun j =>
       - 2 * esq_row (2 * m + 1 - j) (j + 2) a
       + 2 * esq_row (2 * m - j) (j + 1) a
       + 2 * osq_row (2 * m - j) (j + 1) a
       - 2 * osq_row (2 * m - 1 - j) j a
       + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
       - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))
    (fun j =>
       (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) +
       (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a) +
       (2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))        - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) Hpre1538_7)).
   setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m
     (fun j => (- 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a) +
     (2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a))
     (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
     - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
   setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m
     (fun j => - 2 * esq_row (2 * m + 1 - j) (j + 2) a + 2 * esq_row (2 * m - j) (j + 1) a)
     (fun j => 2 * osq_row (2 * m - j) (j + 1) a - 2 * osq_row (2 * m - 1 - j) j a))).
   setoid_rewrite (qeqT_imp_qeq _ _ (esq_row_diff_closed m a Hm)).
   setoid_rewrite (qeqT_imp_qeq _ _ (osq_row_diff_closed m a Hm)).
   assert (Hm1 : (m + 1 = Datatypes.S m)%nat) by lia.
   assert (Heq : esq_row (m + 1) m a == esq_row (Datatypes.S m) m a).
   { rewrite Hm1. reflexivity. }
   setoid_rewrite Heq.
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_esq2_expand m a)).
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_osq1_expand m a)).
  (* ④b' 拆 ΣT 为 Σ(2·q6/D6') + Σ(-(2·q2/D2'))（Hmov 分层需要分开的两个和） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_plus m    (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))    (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
  (* ⑤ Hmov：重组为 2·esqSm − 2·osqmm + R6 + R4 + R2（R6/R4/R2 按层分组，tail 原子在 R4 末尾） *)
  assert (Hmov : 2 * esq_row (Datatypes.S m) m a -
                 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0) +
                      q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2) +
                      q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)) -
                 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) -
                 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) +
                 (- 2 * osq_row m (m - 1) a +
                  2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1) +
                       q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)) +
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) +
                  2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) +
                 (sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) +
                  sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) -
                 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
                 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2) ==
                 2 * esq_row (Datatypes.S m) m a - 2 * osq_row m (m - 1) a +
                 (- 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                  + sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))) +
                 (- 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2))
                  - 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                  + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3))
                  + (- 2 * esq_row (2 * m + 2) 1 a + 2 * osq_row (2 * m + 1) 0 a +
                     2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 4) * q_fact 2))) +
                 (- 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0))
                  + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                  + 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1))
                  + sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
  { unfold Qdiv in *. unfold Qminus. ring. }
  setoid_rewrite Hmov.
  (* ⑥ 展开尾项（R4 内连续） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_tail_expand m a)).
  (* ⑦ 分层断言：R6 == 0、R4 == Te²、R2 == −To² *)
  assert (H6 : - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4))
               + (- (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))))
               + sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))
               == 0).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 4)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                 + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) == 0).
    { apply qeqT_imp_qeq. apply (row_pair_high6 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 6) / (q_fact (4 * m + 2) * q_fact 4)) ==
                  q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4))).
    { unfold Qdiv. ring. }
    assert (H2' : - (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) ==
                  q_pow a (4 * m + 6) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
    assert (Hpre1538_6 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))) i ) ( (fun j => q_pow a (4 * m + 6) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 6) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))        (fun j => q_pow a (4 * m + 6) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) Hpre1538_6)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 6)) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : sum_upto m (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) ==
                  q_pow a (4 * m + 6) * (2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
    assert (Hpre1538_5 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m        (fun j => 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))        (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) Hpre1538_5)).
      assert (Hpre1538_4 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i ) ( (fun j => q_pow a (4 * m + 6) * (2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m        (fun j => 2 * (q_pow a (4 * m + 6) * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))))        (fun j => q_pow a (4 * m + 6) * (2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))) Hpre1538_4)).
       setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m (q_pow a (4 * m + 6)) (fun j => 2 * (1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))))).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m 2 (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
      ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'.
    assert (Hfac : q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4)) +
                   q_pow a (4 * m + 6) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))) +
                   q_pow a (4 * m + 6) * (2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4)))) ==
                   q_pow a (4 * m + 6) * (- 2 / (q_fact (4 * m + 2) * q_fact 4)
                                          - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 6)))
                                          + 2 * sum_upto m (fun j => 1 / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))))).
    { ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  assert (H4 : - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2))
               + (- (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))))
               + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
               + 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3))
               + (- 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
                  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1)) ==
               q_pow a (4 * m + 4) / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 2)
                 - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                 + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                 + 2 / (q_fact (4 * m + 1) * q_fact 3)
                 - 2 / (q_fact (4 * m + 4) * q_fact 0)
                 + 2 / (q_fact (4 * m + 3) * q_fact 1) ==
                 1 / (q_fact (2 * m + 2) * q_fact (2 * m + 2))).
    { apply qeqT_imp_qeq. apply (row_pair_mid4 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 2) * q_fact 2)) ==
                  q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2))).
    { unfold Qdiv. ring. }
    assert (H2' : - (2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) ==
                  q_pow a (4 * m + 4) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
    assert (Hpre1538_3 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))) i ) ( (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))        (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) Hpre1538_3)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 4)) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) ==
                  q_pow a (4 * m + 4) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
    assert (Hpre1538_2 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))) i ) ( (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 4) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))        (fun j => q_pow a (4 * m + 4) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) Hpre1538_2)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 4)) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H4' : 2 * (q_pow a (4 * m + 4) / (q_fact (4 * m + 1) * q_fact 3)) ==
                  q_pow a (4 * m + 4) * (2 / (q_fact (4 * m + 1) * q_fact 3))).
    { unfold Qdiv. ring. }
    assert (H5' : - 2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 4) * q_fact 0) +
                  2 * q_pow a (4 * m + 4) / (q_fact (4 * m + 3) * q_fact 1) ==
                  q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 4) * q_fact 0) +
                                         2 / (q_fact (4 * m + 3) * q_fact 1))).
    { unfold Qdiv. ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'. setoid_rewrite H4'. setoid_rewrite H5'.
    assert (Hfac : q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2)) +
                   q_pow a (4 * m + 4) * (- 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))) +
                   q_pow a (4 * m + 4) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))) +
                   q_pow a (4 * m + 4) * (2 / (q_fact (4 * m + 1) * q_fact 3)) +
                   q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 4) * q_fact 0) + 2 / (q_fact (4 * m + 3) * q_fact 1)) ==
                   q_pow a (4 * m + 4) * (- 2 / (q_fact (4 * m + 2) * q_fact 2)
                                          - 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 4)))
                                          + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 5)))
                                          + 2 / (q_fact (4 * m + 1) * q_fact 3)
                                          - 2 / (q_fact (4 * m + 4) * q_fact 0)
                                          + 2 / (q_fact (4 * m + 3) * q_fact 1))).
    { unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  assert (H2 : - 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0))
               + 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
               + 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1))
               + sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
               - q_pow a (4 * m + 2) / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
  { assert (Hc : - 2 / (q_fact (4 * m + 2) * q_fact 0)
                 + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                 + 2 / (q_fact (4 * m + 1) * q_fact 1)
                 - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))) ==
                 - 1 / (q_fact (2 * m + 1) * q_fact (2 * m + 1))).
    { apply qeqT_imp_qeq. apply (row_pair_mid2 m Hm). }
    assert (H1' : - 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 2) * q_fact 0)) ==
                  q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0))).
    { unfold Qdiv. ring. }
    assert (H2' : 2 * sum_upto (m - 1) (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) ==
                  q_pow a (4 * m + 2) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
    assert (Hpre1538_1 : (forall i : nat, NatLe (Datatypes.S i) (m - 1) ->QeqT ( (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))) i ) ( (fun j => q_pow a (4 * m + 2) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
    { setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below (m - 1)        (fun j => q_pow a (4 * m + 2) / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))        (fun j => q_pow a (4 * m + 2) * (1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) Hpre1538_1)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale (m - 1) (q_pow a (4 * m + 2)) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    assert (H3' : 2 * (q_pow a (4 * m + 2) / (q_fact (4 * m + 1) * q_fact 1)) ==
                  q_pow a (4 * m + 2) * (2 / (q_fact (4 * m + 1) * q_fact 1))).
    { unfold Qdiv. ring. }
    assert (H4' : sum_upto m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
                  q_pow a (4 * m + 2) * (- 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      { assert (Hpre1538_200 : (forall i : nat, NatLe (Datatypes.S i) m ->QeqT ( (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) i ) ( (fun j => q_pow a (4 * m + 2) * (- 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) i))).
      {  intros j Hj. apply NatLe_drop in Hj. apply qeq_imp_qeqT. unfold Qdiv. ring. }
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_ext_below m (fun j => - (2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) (fun j => q_pow a (4 * m + 2) * (- 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))) Hpre1538_200)).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale m (q_pow a (4 * m + 2)) (fun j => - 2 * (1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))))).
      setoid_rewrite (qeqT_imp_qeq _ _ (sum_upto_scale_neg2 m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
      unfold Qdiv in *. unfold Qminus. ring. }
    setoid_rewrite H1'. setoid_rewrite H2'. setoid_rewrite H3'. setoid_rewrite H4'.
    assert (Hfac : q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0)) +
                   q_pow a (4 * m + 2) * (2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))) +
                   q_pow a (4 * m + 2) * (2 / (q_fact (4 * m + 1) * q_fact 1)) +
                   q_pow a (4 * m + 2) * (- 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))) ==
                   q_pow a (4 * m + 2) * (- 2 / (q_fact (4 * m + 2) * q_fact 0)
                                          + 2 * sum_upto (m - 1) (fun j => 1 / (q_fact (4 * m - 1 - 2 * j) * q_fact (2 * j + 3)))
                                          + 2 / (q_fact (4 * m + 1) * q_fact 1)
                                          - 2 * sum_upto m (fun j => 1 / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
    { ring. }
    setoid_rewrite Hfac.
    setoid_rewrite Hc.
    unfold Qdiv in *. unfold Qminus. ring. }
  (* ⑧ 组装：R6 + R4 + R2 == Te² − To² *)
  setoid_rewrite H6.
  setoid_rewrite H4.
  setoid_rewrite H2.
  unfold Qdiv in *. unfold Qminus. ring.
Qed.

Lemma ksum_diff_row : forall (a : Q) (m : nat),
  (1 <= m)%nat ->QeqT (
  ksum_diff m m a + inner2 (2 * m + 1) (2 * Datatypes.S m - (2 * m + 1)) a ) (
  2 * esq_row (Datatypes.S m) m a +
  (q_pow a (4 * m + 4) /
     (q_fact (2 * m + 2) * q_fact (2 * m + 2))) -
  2 * osq_row m (m - 1) a -
  (q_pow a (2 * m + 2 * m + 2) /
     (q_fact (2 * m + 1) * q_fact (2 * m + 1)))).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  (* ① LHS == corr 差分（corr_succ_decomp 反向） *)
  setoid_rewrite <- (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  (* ② corr 差分 == 行表达式 k' 形态（corr_diff_expand） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_diff_expand a m Hm)).
  (* ③ 行表达式 k' 形态 == j 形态（j = m−1−k'，sum_upto_rev + 逐点归约） *)
  assert (Hrel : sum_upto m
            (fun k' =>
               - 2 * esq_row (m + 2 + k') (m + 1 - k') a
               + 2 * esq_row (m + 1 + k') (m - k') a
               + 2 * osq_row (m + 1 + k') (m - k') a
               - 2 * osq_row (m + k') (m - k' - 1) a
               + 2 * q_pow a (4 * m + 6) / (q_fact (2 * m + 2 * k' + 4) * q_fact (2 * m + 2 - 2 * k'))
               - 2 * q_pow a (4 * m + 2) / (q_fact (2 * m + 2 * k' + 2) * q_fact (2 * m - 2 * k'))) ==
                 sum_upto m
            (fun j =>
               - 2 * esq_row (2 * m + 1 - j) (j + 2) a
               + 2 * esq_row (2 * m - j) (j + 1) a
               + 2 * osq_row (2 * m - j) (j + 1) a
               - 2 * osq_row (2 * m - 1 - j) j a
               + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))
               - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2)))).
  { rewrite <- (qeqT_imp_qeq _ _ (sum_upto_rev m      (fun j =>
         - 2 * esq_row (2 * m + 1 - j) (j + 2) a
         + 2 * esq_row (2 * m - j) (j + 1) a
         + 2 * osq_row (2 * m - j) (j + 1) a
         - 2 * osq_row (2 * m - 1 - j) j a
         + 2 * q_pow a (4 * m + 6) / (q_fact (4 * m + 2 - 2 * j) * q_fact (2 * j + 4))         - 2 * q_pow a (4 * m + 2) / (q_fact (4 * m - 2 * j) * q_fact (2 * j + 2))))).
    apply qeqT_imp_qeq. apply sum_upto_ext_below. intros k' Hk'. apply NatLe_drop in Hk'. apply qeq_imp_qeqT.
    (* 逐点：corr行差(k') == row行差(m−1−k')——参数归约（lia） *)
    assert (H1 : (2 * m + 1 - (m - 1 - k') = m + 2 + k')%nat) by lia.
    assert (H2 : ((m - 1 - k') + 2 = m + 1 - k')%nat) by lia.
    assert (H3 : (2 * m - (m - 1 - k') = m + 1 + k')%nat) by lia.
    assert (H4 : ((m - 1 - k') + 1 = m - k')%nat) by lia.
    assert (H5 : (2 * m - 1 - (m - 1 - k') = m + k')%nat) by lia.
    assert (H6 : ((m - 1 - k') = m - k' - 1)%nat) by lia.
    assert (H7 : (4 * m + 2 - 2 * (m - 1 - k') = 2 * m + 2 * k' + 4)%nat) by lia.
    assert (H8 : (2 * (m - 1 - k') + 4 = 2 * m + 2 - 2 * k')%nat) by lia.
    assert (H9 : (4 * m - 2 * (m - 1 - k') = 2 * m + 2 * k' + 2)%nat) by lia.
    assert (H10 : (2 * (m - 1 - k') + 2 = 2 * m - 2 * k')%nat) by lia.
    rewrite H1. rewrite H3. rewrite H5.
    rewrite H7. rewrite H8. rewrite H9. rewrite H10.
    rewrite H2. rewrite H4. rewrite H6.
    reflexivity. }
  setoid_rewrite Hrel.
  (* ④ 行表达式 j 形态 == RHS（row_pair_main） *)
  setoid_rewrite (qeqT_imp_qeq _ _ (row_pair_main a m Hm)).
  (* ⑤ To² 指数归约：2m+2m+2 == 4m+2 *)
  assert (He : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat). exact He. }
  reflexivity.
Qed.

(* ============ esq_eq_corr 论证（备份 93 并入，检验 _dbg_kdr.v 全部通过） ============
   corr_diff_eq_sq_diff：corr 差分 == E/O 平方差分差（corr_succ_decomp → ksum_diff_row → ksum_diff_row_rhs）
   esq_eq_corr：E_m²−O_m² == 1 + corr m（主恒等式，base 0/1 + 归纳 step）——注释目标 L10664 达成 *)
Lemma corr_diff_eq_sq_diff : forall (a : Q) (m : nat), (1 <= m)%nat ->QeqT (
  corr (Datatypes.S m) a - corr m a ) (
  (e_sum (Datatypes.S m) a * e_sum (Datatypes.S m) a -
   o_sum (Datatypes.S m) a * o_sum (Datatypes.S m) a) -
  (e_sum m a * e_sum m a - o_sum m a * o_sum m a)).
Proof.
  intros a m Hm.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (corr_succ_decomp a m Hm)).
  setoid_rewrite (qeqT_imp_qeq _ _ (ksum_diff_row a m Hm)).
  (* ksum_diff_row 的 To² 指数是 2m+2m+2，ksum_diff_row_rhs 是 4m+2——归约桥 *)
  assert (He : (2 * m + 2 * m + 2 = 4 * m + 2)%nat) by lia.
  setoid_replace (q_pow a (2 * m + 2 * m + 2)) with (q_pow a (4 * m + 2)).
  2: { apply (q_pow_comp_proper a a (Qeq_refl a) (2 * m + 2 * m + 2)%nat (4 * m + 2)%nat). exact He. }
  setoid_rewrite (qeqT_imp_qeq _ _ (ksum_diff_row_rhs a m Hm)).
  reflexivity.
Qed.

Lemma esq_eq_corr : forall (a : Q) (m : nat),QeqT (
  e_sum m a * e_sum m a - o_sum m a * o_sum m a ) ( 1 + corr m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  induction m as [| m' IH].
  - (* m=0：E_0=1、O_0=0、corr 0=0 *)
    simpl. reflexivity.
  - destruct m' as [| m''].
    + (* m=1：直接计算 *)
      unfold e_sum, o_sum, corr, kloop, inner2, brk2.
      simpl.
      field.
      all: repeat (split; [intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)) | idtac]);
           intro Hz1545; destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Hz1545)).
    + (* m = S(S m'')：step——corr 差分公式 + IH *)
      assert (Hstep : e_sum (Datatypes.S (Datatypes.S m'')) a * e_sum (Datatypes.S (Datatypes.S m'')) a -
                      o_sum (Datatypes.S (Datatypes.S m'')) a * o_sum (Datatypes.S (Datatypes.S m'')) a ==
                      (e_sum (Datatypes.S m'') a * e_sum (Datatypes.S m'') a -
                       o_sum (Datatypes.S m'') a * o_sum (Datatypes.S m'') a) +
                      (corr (Datatypes.S (Datatypes.S m'')) a - corr (Datatypes.S m'') a)).
      { assert (Hd : corr (Datatypes.S (Datatypes.S m'')) a - corr (Datatypes.S m'') a ==
                     (e_sum (Datatypes.S (Datatypes.S m'')) a * e_sum (Datatypes.S (Datatypes.S m'')) a -
                      o_sum (Datatypes.S (Datatypes.S m'')) a * o_sum (Datatypes.S (Datatypes.S m'')) a) -
                     (e_sum (Datatypes.S m'') a * e_sum (Datatypes.S m'') a -
                      o_sum (Datatypes.S m'') a * o_sum (Datatypes.S m'') a)).
        { apply qeqT_imp_qeq. apply (corr_diff_eq_sq_diff a (Datatypes.S m'')). lia. }
        setoid_rewrite Hd.
        unfold Qminus. ring. }
      setoid_rewrite Hstep.
      setoid_rewrite IH.
      unfold Qminus. ring.
Qed.

(* ============ exp_even_neg_nonneg 论证（备份 94 并入，检验 _dbg_kdr.v 全部通过） ============
   q_div_nonneg / e_sum_ge_one / o_sum_nonneg（辅助：E≥1、O≥0）
   exp_even_mul_eq：S_{2m}(−a)·S_{2m}(a) == 1 + corr m a（(E−O)(E+O) = E²−O²）
   exp_even_neg_nonneg：0 ≤ a ⟹ 0 ≤ exp_partial (2·m) (−a)（corr_nonneg + S(a)>0 + field 恒等） *)
Lemma q_div_nonneg : forall (x d : Q), QleT' 0 x -> QltT 0 d -> QleT' 0 (x / d).
Proof.
  intros x d Hx Hd.
  assert (HxQ : Qle 0 x) by (apply QleT'_to_Qle; exact Hx).
  assert (HdQ : Qlt 0 d) by (apply QltT_to_Qlt; exact Hd).
  apply Qle_to_QleT'.
  unfold Qdiv.
  exact (Qmult_le_0_compat x (Qinv d) HxQ
  (Qlt_le_weak 0 (Qinv d) (Qinv_lt_0_compat d HdQ))).
Qed.
Lemma e_sum_ge_one : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 1 (e_sum m a).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  induction m as [| m' IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (e_sum m' a) _).
    + exact IH.
    + apply (Qle_trans _ (e_sum m' a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m' a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m' a) (e_sum m' a) 0 (q_pow a (2 * Datatypes.S m') / q_fact (2 * Datatypes.S m'))).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (q_div_nonneg (q_pow a (2 * Datatypes.S m')) (q_fact (2 * Datatypes.S m'))).
           ++ apply (q_pow_nonneg a (2 * Datatypes.S m')). exact Ha.
           ++ apply q_fact_pos.
Qed.
Lemma o_sum_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (o_sum m a).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  induction m as [| m' IH]; simpl.
  - exact (Qle_refl 0).
  - exact (Qplus_le_compat 0 (o_sum m' a) 0
  (q_pow a (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
  IH (QleT'_to_Qle _ _ (q_div_nonneg (q_pow a (Datatypes.S (2 * m')))
  (q_fact (Datatypes.S (2 * m')))
  (q_pow_nonneg a (Datatypes.S (2 * m')) Ha)        (q_fact_pos (Datatypes.S (2 * m')))))).
Qed.
Lemma exp_even_mul_eq : forall (a : Q) (m : nat),QeqT (
  exp_partial (2 * m) (- a) * exp_partial (2 * m) a ) ( 1 + corr m a).
Proof.
  intros a m.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_even a m)).
  setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
  assert (Hring : (e_sum m a - o_sum m a) * (e_sum m a + o_sum m a) ==
                  e_sum m a * e_sum m a - o_sum m a * o_sum m a) by ring.
  setoid_rewrite Hring.
  setoid_rewrite (qeqT_imp_qeq _ _ (esq_eq_corr a m)).
  reflexivity.
Qed.
Lemma exp_even_neg_nonneg : forall (a : Q) (m : nat), QleT' 0 a -> QleT' 0 (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha.
  apply Qle_to_QleT'.
  assert (H01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  (* ① 0 < S(−a)·S(a)：S(−a)·S(a) == 1 + corr ≥ 1 > 0 *)
  assert (Hmul_le : Qle 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq a m)).
    apply (Qle_trans _ (1 + 0) _).
    - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (corr_nonneg a m Ha). }
  assert (Hmul_pos : Qlt 0 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { apply (Qlt_le_trans 0 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
    - exact H01.
    - exact Hmul_le. }
  (* ② 0 < S(a)：S(a) == E+O，E ≥ 1 > 0、O ≥ 0 ⟹ E+O > 0 *)
  assert (Hspos : Qlt 0 (exp_partial (2 * m) a)).
  { setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
    apply (Qlt_le_trans 0 (e_sum m a) (e_sum m a + o_sum m a)).
    - apply (Qlt_le_trans 0 1 (e_sum m a)).
      + exact H01.
      + apply QleT'_to_Qle.
        apply (e_sum_ge_one a m Ha).
    - apply (Qle_trans _ (e_sum m a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m a) (e_sum m a) 0 (o_sum m a)).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (o_sum_nonneg a m Ha). }
  (* ③ S(−a) == (S(−a)·S(a))·inv(S(a))（field 恒等，S(a) ≠ 0） *)
  assert (Hinv : exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a) == 1).
  { apply Qmult_inv_r. intro Heq0. destruct (q_neq_of_lt (exp_partial (2 * m) a) (Qlt_to_QltT _ _ Hspos) (qeq_imp_qeqT _ _ Heq0)). }
  assert (Hfield : exp_partial (2 * m) (- a) ==
                   (exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a)).
  { transitivity (exp_partial (2 * m) (- a) *
                  (exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a))).
    - setoid_rewrite Hinv. ring.
    - ring. }
  (* ④ (S(−a)·S(a))·inv(S(a)) > 0（正×正）⟹ S(−a) > 0 ⟹ ≥ 0 *)
  assert (Hpos : Qlt 0 ((exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a))).
  { apply Qmult_lt_0_compat.
    - exact Hmul_pos.
    - apply Qinv_lt_0_compat. exact Hspos. }
  setoid_rewrite <- Hfield in Hpos.
  apply (Qlt_le_weak 0 (exp_partial (2 * m) (- a))). exact Hpos.
Qed.
(* ============ exp_partial_tail_pos 论证（备份 95 并入，检验 _dbg_kdr.v 全部通过） ============
   exp_even_neg_pos：0 ≤ a ⟹ 0 < exp_partial (2·m) (−a)（严格正版，S(−a)·S(a) ≥ 1 + S(a) > 0）
   exp_partial_tail_pos：0 ≤ a ⟹ 0 < exp_partial (2m+2) (−a)（尾截断正，exp_even_neg_pos 的 S m 版）
   下轮：cauchy_real_exp_pos（real_lt zero (cauchy_real_exp x)，exp_neg_pos 字段实例化材料） *)
Lemma exp_even_neg_pos : forall (a : Q) (m : nat), QleT' 0 a -> QltT 0 (exp_partial (2 * m) (- a)).
Proof.
  intros a m Ha.
  apply Qlt_to_QltT.
  assert (H01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  assert (Hmul_le : Qle 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq a m)).
    apply (Qle_trans _ (1 + 0) _).
    - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (corr_nonneg a m Ha). }
  assert (Hmul_pos : Qlt 0 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
  { apply (Qlt_le_trans 0 1 (exp_partial (2 * m) (- a) * exp_partial (2 * m) a)).
    - exact H01.
    - exact Hmul_le. }
  assert (Hspos : Qlt 0 (exp_partial (2 * m) a)).
  { setoid_rewrite (qeqT_imp_qeq _ _ (e_o_split_pos a m)).
    apply (Qlt_le_trans 0 (e_sum m a) (e_sum m a + o_sum m a)).
    - apply (Qlt_le_trans 0 1 (e_sum m a)).
      + exact H01.
      + apply QleT'_to_Qle.
        apply (e_sum_ge_one a m Ha).
    - apply (Qle_trans _ (e_sum m a + 0) _).
      * setoid_rewrite (Qplus_0_r (e_sum m a)). apply Qle_refl.
      * apply (Qplus_le_compat (e_sum m a) (e_sum m a) 0 (o_sum m a)).
        -- apply Qle_refl.
        -- apply QleT'_to_Qle.
           apply (o_sum_nonneg a m Ha). }
  assert (Hinv : exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a) == 1).
  { apply Qmult_inv_r. intro Heq0. destruct (q_neq_of_lt (exp_partial (2 * m) a) (Qlt_to_QltT _ _ Hspos) (qeq_imp_qeqT _ _ Heq0)). }
  assert (Hfield : exp_partial (2 * m) (- a) ==
                   (exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a)).
  { transitivity (exp_partial (2 * m) (- a) *
                  (exp_partial (2 * m) a * Qinv (exp_partial (2 * m) a))).
    - setoid_rewrite Hinv. ring.
    - ring. }
  assert (Hpos : Qlt 0 ((exp_partial (2 * m) (- a) * exp_partial (2 * m) a) * Qinv (exp_partial (2 * m) a))).
  { apply Qmult_lt_0_compat.
    - exact Hmul_pos.
    - apply Qinv_lt_0_compat. exact Hspos. }
  setoid_rewrite <- Hfield in Hpos.
  exact Hpos.
Qed.

Lemma exp_partial_tail_pos : forall (a : Q) (m : nat), QleT' 0 a -> QltT 0 (exp_partial (2 * m + 2) (- a)).
Proof.
  intros a m Ha.
  apply Qlt_to_QltT.
  assert (Hn : (2 * Datatypes.S m = 2 * m + 2)%nat) by lia.
  setoid_replace (exp_partial (2 * m + 2) (- a)) with (exp_partial (2 * Datatypes.S m) (- a)).
  2: { change (exp_partial (2 * m + 2) (- a) == exp_partial (2 * Datatypes.S m) (- a)).
       rewrite <- Hn. reflexivity. }
  apply QltT_to_Qlt. apply (exp_even_neg_pos a (Datatypes.S m)). exact Ha.
Qed.

(* 任意参数的偶截断正：∀y，0 < exp_partial (2·m) y（Qlt_le_dec 三分：
   0 < y ⟹ 正项和 ≥ 1 > 0；y ≤ 0 ⟹ exp_pair_alt m (−y) > 0（exp_even_neg_pos）） *)
Lemma exp_even_all_pos : forall (y : Q) (m : nat), QltT 0 (exp_partial (2 * m) y).
Proof.
  intros y m.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 y) as [Hy | Hy0].
  - (* 0 < y：ep (2m) y ≥ 1 > 0（正项和） *)
    assert (Hy0' : QleT' 0 y) by (apply Qle_to_QleT'; apply (Qlt_le_weak 0 y); exact Hy).
    assert (Hle : Qle 1 (exp_partial (2 * m) y)).
    { induction m as [| m' IH].
      + simpl. apply Qle_refl.
      + assert (Hidx : (2 * Datatypes.S m' = Datatypes.S (Datatypes.S (2 * m')))%nat) by lia.
        rewrite Hidx. simpl.
        assert (HT1 : Qle 0 (q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))).
        { apply QleT'_to_Qle.
          apply (q_div_nonneg (q_pow y (Datatypes.S (2 * m'))) (q_fact (Datatypes.S (2 * m')))).
          - apply (q_pow_nonneg y (Datatypes.S (2 * m'))). exact Hy0'.
          - apply q_fact_pos. }
        assert (HT2 : Qle 0 (q_pow y (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
        { apply QleT'_to_Qle.
          apply (q_div_nonneg (q_pow y (Datatypes.S (Datatypes.S (2 * m')))) (q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
          - apply (q_pow_nonneg y (Datatypes.S (Datatypes.S (2 * m')))). exact Hy0'.
          - apply q_fact_pos. }
        apply (Qle_trans _ (exp_partial (2 * m') y) _).
        * exact IH.
        * apply (Qle_trans _ (exp_partial (2 * m') y +
                              q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m'))) _).
          -- apply (Qle_trans _ (exp_partial (2 * m') y + 0) _).
             ++ setoid_rewrite (Qplus_0_r (exp_partial (2 * m') y)). apply Qle_refl.
             ++ apply (Qplus_le_compat (exp_partial (2 * m') y) (exp_partial (2 * m') y) 0
                        (q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))).
                ** apply Qle_refl.
                ** exact HT1.
          -- apply (Qle_trans _ (exp_partial (2 * m') y +
                                q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')) + 0) _).
             ++ setoid_rewrite (Qplus_0_r (exp_partial (2 * m') y +
                                         q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))). apply Qle_refl.
             ++ apply (Qplus_le_compat (exp_partial (2 * m') y +
                                       q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
                                     (exp_partial (2 * m') y +
                                      q_pow y (Datatypes.S (2 * m')) / q_fact (Datatypes.S (2 * m')))
                                     0 (q_pow y (Datatypes.S (Datatypes.S (2 * m'))) / q_fact (Datatypes.S (Datatypes.S (2 * m'))))).
                ** apply Qle_refl.
                ** exact HT2. }
    apply (Qlt_le_trans 0 1 (exp_partial (2 * m) y)).
    + unfold Qlt; simpl; lia.
    + exact Hle.
  - (* y ≤ 0：ep (2m) y = exp_pair_alt m (−y) > 0（exp_even_neg_pos 于 −y ≥ 0） *)
    assert (Hny : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hy0. }
    assert (Hp : Qlt 0 (exp_partial (2 * m) (- (- y)))).
    { apply QltT_to_Qlt. apply (exp_even_neg_pos (- y) m). apply Qle_to_QleT'. exact Hny. }
    destruct y as [n d].
    destruct n; exact Hp.
Qed.
(* ============================================================
   cauchy_real_exp_pos 论证（B3 最终步：exp_neg_pos 字段材料）
   目标：real_lt zero (cauchy_real_exp x)
   策略：偶数截断统一下界 1/C（exp_even_mul_eq + corr_nonneg +
   exp_series_arch：S_{2m}(-a)·S_{2m}(a) == 1+corr ≥ 1，且 S_{2m}(a) ≤ C，
   故 S_{2m}(-a) ≥ 1/C；y ≥ 0 时 S_{2m}(y) ≥ 1 ≥ 1/C）；
   奇数截断用尾项衰减补齐（2m+1 ≥ m0 时 |y|^{2m+1}/(2m+1)! < 1/(2C)）。
   ============================================================ *)

(* 0b. exp_partial 与 exp_series 定义性同构：exp_partial n x == exp_series n x *)
Lemma exp_partial_eq_series : forall (n : nat) (x : Q),QeqT ( exp_partial n x ) ( exp_series n x).
Proof.
  intros n x.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 0c. exp_partial 参数 wd：x == y ⟹ exp_partial n x == exp_partial n y *)
Lemma exp_partial_wd : forall (n : nat) (x y : Q),QeqT ( x ) ( y )->QeqT ( exp_partial n x ) ( exp_partial n y).
Proof.
  intros n x y Hxy.
  apply qeq_imp_qeqT.
  induction n as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (qeqT_imp_qeq _ _ (q_pow_wd x y (Datatypes.S m) Hxy)).
    reflexivity.
Qed.

(* 1. exp_series 对第二参数单调：0 ≤ B1 ≤ B2 ⟹ exp_series n B1 ≤ exp_series n B2 *)
Lemma exp_series_arg_mono : forall (B1 B2 : Q) (n : nat),
  QleT' 0 B1 -> QleT' B1 B2 -> QleT' (exp_series n B1) (exp_series n B2).
Proof.
  intros B1 B2 n HB1 HB12.
  apply Qle_to_QleT'.
  induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply Qplus_le_compat.
    + exact IH.
    + apply QleT'_to_Qle.
      apply (Qle_div_same_denom (q_pow B1 (Datatypes.S n)) (q_pow B2 (Datatypes.S n))
                               (q_fact (Datatypes.S n))).
      * apply q_fact_pos.
      * apply q_pow_mono; [exact HB1 | exact HB12].
Qed.

(* 2. 非负参数的任意截断 ≥ 1：0 ≤ y ⟹ 1 ≤ exp_partial n y（每步加非负项） *)
Lemma exp_partial_ge_one : forall (y : Q) (n : nat), QleT' 0 y -> QleT' 1 (exp_partial n y).
Proof.
  intros y n Hy.
  apply Qle_to_QleT'.
  induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (exp_partial n y) _).
    + exact IH.
    + apply (Qle_plus_nonneg_r (exp_partial n y) (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      apply QleT'_to_Qle.
      apply q_pow_fact_nonneg. exact Hy.
Qed.

(* 3. exp_partial (2m) a ≤ C：0 ≤ a ≤ M，(∀n, exp_series n M ≤ C) ⟹ exp_partial (2m) a ≤ C *)
Lemma exp_partial_even_upper : forall (a M C : Q) (m : nat),
  QleT' 0 M -> QleT' 0 a -> QleT' a M ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  QleT' (exp_partial (2 * m) a) C.
Proof.
  intros a M C m HM Ha Ham HC.
  apply Qle_to_QleT'.
  exact (Qle_trans (exp_partial (2 * m) a) (exp_series (2 * m) a) C
    (QleT'_to_Qle _ _ (qeq_le (exp_partial (2 * m) a) (exp_series (2 * m) a)
      (qeq_imp_qeqT (exp_partial (2 * m) a) (exp_series (2 * m) a)
      (qeqT_imp_qeq _ _ (exp_partial_eq_series (2 * m) a)))))
    (Qle_trans (exp_series (2 * m) a) (exp_series (2 * m) M) C
      (QleT'_to_Qle _ _ (exp_series_arg_mono a M (2 * m)%nat Ha Ham))
      (QleT'_to_Qle _ _ (HC (2 * m)%nat)))).
Qed.

(* 4. 偶数截断统一下界：|y| ≤ M ⟹ 1/C ≤ exp_partial (2m) y（y ≥ 0 用正项和 ≥ 1；
   y ≤ 0 用 S(-a)·S(a) == 1+corr ≥ 1 且 S(a) ≤ C ⟹ S(-a) ≥ 1/C） *)
Lemma exp_partial_even_lower : forall (M C : Q) (y : Q) (m : nat),
  QleT' 0 M -> QleT' 1 C ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  QleT' (Qabs y) M -> QleT' (1 / C) (exp_partial (2 * m) y).
Proof.
  intros M C y m HM HC HCser Hy.
  apply Qle_to_QleT'.
  destruct (Qlt_le_dec 0 y) as [Hypos | Hyneg].
  - (* 0 < y：正项和 ≥ 1 ≥ 1/C *)
    apply (Qle_trans _ 1 _).
    + (* 1/C ≤ 1：1/C == 1·Qinv C，Qinv C ≤ Qinv 1 == 1，且 1·x == x *)
      change (Qle (1 * Qinv C) 1).
      apply (Qle_trans _ (Qinv C) _).
      * apply QleT'_to_Qle.
        apply qeq_leT'.
        apply qeq_imp_qeqT.
        apply (Qmult_1_l (Qinv C)).
      * apply QleT'_to_Qle.
        apply (q_inv_le_contravar C 1).
        -- apply Qlt_to_QltT.
           apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
        -- apply Qlt_to_QltT.
           unfold Qlt; simpl; lia.
        -- exact HC.
    + apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. apply (Qlt_le_weak 0 y). exact Hypos.
  - (* y ≤ 0：a = -y ≥ 0，S_{2m}(-a) ≥ 1/S_{2m}(a) ≥ 1/C *)
    assert (Ha : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hyneg. }
    assert (Ham : Qle (- y) M).
    { assert (Habs : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
      rewrite <- Habs. exact (QleT'_to_Qle _ _ Hy). }
    (* S_{2m}(a) ≥ 1 > 0 且 S_{2m}(a) ≤ C（a = -y） *)
    assert (Hsa_pos : Qlt 0 (exp_partial (2 * m) (- y))).
    { apply (Qlt_le_trans _ 1 _).
      - unfold Qlt; simpl; lia.
      - apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. exact Ha. }
    assert (Hsa_le : Qle (exp_partial (2 * m) (- y)) C).
    { apply QleT'_to_Qle.
      apply (exp_partial_even_upper (- y) M C m).
      - exact HM.
      - apply Qle_to_QleT'. exact Ha.
      - apply Qle_to_QleT'. exact Ham.
      - exact HCser. }
    (* 1 ≤ S(-(-y))·S(-y)（exp_even_mul_eq + corr_nonneg） *)
    assert (Hmul : Qle 1 (exp_partial (2 * m) (- (- y)) * exp_partial (2 * m) (- y))).
    { rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq (- y) m)).
      apply (Qle_trans _ (1 + 0) _).
      - setoid_rewrite (Qplus_0_r 1). apply Qle_refl.
      - apply (Qplus_le_compat 1 1 0 (corr m (- y))).
        * apply Qle_refl.
        * apply QleT'_to_Qle.
          apply (corr_nonneg (- y) m).
          apply Qle_to_QleT'. exact Ha. }
    (* 目标 1/C ≤ S_{2m}(y)：y == -(-y)，1/C ≤ 1/S(-y) ≤ S(-(-y))，再用 wd 换回 y *)
    assert (Hyid : y == - (- y)) by ring.
    apply (Qle_trans _ (exp_partial (2 * m) (- (- y))) _).
    { (* 1/C ≤ S(-(-y))：链 1/C ≤ 1/S(-y) ≤ S(-(-y)) *)
      apply (Qle_trans _ (1 / exp_partial (2 * m) (- y)) _).
      { (* 1/C ≤ 1/S(-y)：先消 1·（Qdiv 1 x 与 Qinv x 形态不同），
         再 q_inv_le_contravar（Qinv C ≤ Qinv S），最后补回 1· *)
        apply (Qle_trans _ (Qinv C) _).
        - (* 1/C ≤ Qinv C：1·Qinv C == Qinv C *)
          apply QleT'_to_Qle.
          apply qeq_leT'.
          apply qeq_imp_qeqT.
          apply (Qmult_1_l (Qinv C)).
        - apply (Qle_trans _ (Qinv (exp_partial (2 * m) (- y))) _).
          + (* Qinv C ≤ Qinv S(-y)：q_inv_le_contravar（0 < S(-y) ≤ C） *)
            apply QleT'_to_Qle.
            apply (q_inv_le_contravar C (exp_partial (2 * m) (- y))).
            * apply Qlt_to_QltT.
              apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
            * apply Qlt_to_QltT. exact Hsa_pos.
            * exact (Qle_to_QleT' _ _ Hsa_le).
          + (* Qinv S(-y) ≤ 1·Qinv S(-y) == 1/S(-y)：补回 1· *)
            apply QleT'_to_Qle.
            apply qeq_leT'.
            apply qeq_imp_qeqT.
            apply Qeq_sym. apply (Qmult_1_l (Qinv (exp_partial (2 * m) (- y)))). }
      { (* 1/S(-y) ≤ S(-(-y))：Qle_shift_div_r 1 (S(-y)) (S(-(-y)))，需 1 ≤ S(-(-y))·S(-y) *)
        apply (Qle_shift_div_r 1 (exp_partial (2 * m) (- y))
                                (exp_partial (2 * m) (- (- y)))).
        - exact Hsa_pos.
        - exact Hmul. } }
    { (* S(-(-y)) ≤ S(y)：qeq_le（y == -(-y) 的 wd 版） *)
      apply QleT'_to_Qle.
      apply qeq_leT'.
      apply (exp_partial_wd (2 * m) (- (- y)) y).
      apply qeq_imp_qeqT.
      apply Qeq_sym.
      exact Hyid. }
Qed.

(* 5. 尾项衰减：∃m0, ∀m ≥ m0, M^{2m+1}/(2m+1)! < 1/(2C)
   （q_arch_geom 给几何前提 N0，arch_decay 给 (A^{N0}/N0!·2)·(1/2)^{S t} < 1/C，
    exp_tail_arch 收尾：b ≥ N0+S t ⟹ (A^b/b!)·2 < 1/C ⟹ A^b/b! < 1/(2C)） *)
Lemma exp_partial_tail_small : forall (M C : Q), QleT' 0 M -> QleT' 1 C ->
  sigT (fun m0 : nat => forall m : nat, NatLe m0 m ->
    QltT (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) (1 / (2 * C))).
Proof.
  intros M C HM HC.
  destruct (q_arch_geom M) as [N0 HN0].
  assert (HCpos : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)]).
  assert (Hinv : Qlt 0 (1 / C)).
  { apply (Qlt_le_trans _ (Qinv C) _).
    - apply Qinv_lt_0_compat. exact HCpos.
    - apply QleT'_to_Qle.
      apply qeq_leT'.
      apply qeq_imp_qeqT.
      apply Qeq_sym. apply (Qmult_1_l (Qinv C)). }
  destruct (arch_decay ((q_pow M N0 / q_fact N0) * (1 + 1)%Q) (1 / C)) as [t Ht].
  { apply q_pow_fact2_nonneg. exact HM. }
  { apply Qlt_to_QltT. exact Hinv. }
  exists (N0 + Datatypes.S t)%nat.
  intros m Hm.
  apply NatLe_drop in Hm.
  apply Qlt_to_QltT.
  assert (Hb : (N0 + Datatypes.S t <= 2 * m + 1)%nat) by lia.
  (* (M^{2m+1}/(2m+1)!)·2 < 1/C *)
  assert (Harch : Qlt ((q_pow M (2 * m + 1) / q_fact (2 * m + 1)) * (1 + 1)%Q) (1 / C)).
  { apply QltT_to_Qlt.
    apply (exp_tail_arch M N0 t (2 * m + 1) (1 / C) HM
             (fun u Hu => HN0 u Hu)
             (Qlt_to_QltT _ _ Hinv) Ht Hb). }
  (* x·(1+1) < 1/C ⟹ x < (1/C)/(1+1) == 1/(2C) *)
  apply (Qlt_le_trans _ ((1 / C) / (1 + 1)%Q) _).
  - apply (Qlt_shift_div_l (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) (1 / C) (1 + 1)%Q).
    + unfold Qlt; simpl; lia.
    + exact Harch.
  - apply QleT'_to_Qle.
    apply qeq_leT'.
    apply qeq_imp_qeqT.
    unfold Qdiv.
    field.
    intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ HCpos) (qeq_imp_qeqT _ _ Heq0)).
Qed.

(* 6. 奇数截断统一下界：|y| ≤ M、m ≥ m0 ⟹ 1/(2C) < exp_partial (2m+1) y
   （S_{2m+1}(y) == S_{2m}(y) + y^{2m+1}/(2m+1)!；y ≥ 0 时正项和 ≥ 1；
   y ≤ 0 时 S_{2m}(y) ≥ 1/C 且 |y|^{2m+1}/(2m+1)! < 1/(2C)） *)
Lemma exp_partial_odd_lower : forall (M C : Q) (m0 m : nat) (y : Q),
  QleT' 0 M -> QleT' 1 C ->
  (forall n : nat, QleT' (exp_series n M) C) ->
  (forall k : nat, NatLe m0 k ->
    QltT (q_pow M (2 * k + 1) / q_fact (2 * k + 1)) (1 / (2 * C))) ->
  (m0 <= m)%nat ->
  QleT' (Qabs y) M -> QltT (1 / (2 * C)) (exp_partial (2 * m + 1) y).
Proof.
  intros M C m0 m y HM HC HCser Htail Hm0 Hy.
  apply Qlt_to_QltT.
  assert (Hidx : (2 * m + 1 = Datatypes.S (2 * m))%nat) by lia.
  rewrite Hidx.
  destruct (Qlt_le_dec 0 y) as [Hypos | Hyneg].
  - (* 0 < y：正项和 ≥ 1 > 1/(2C) *)
    apply (Qlt_le_trans _ 1 _).
    + (* 1/(2C) < 1：1/(2C) ≤ 1/2 < 1 *)
      apply (Qle_lt_trans _ (1 / 2) _).
      * (* 1/(2C) ≤ 1/2 *)
        apply (Qle_shift_div_r 1 (2 * C) (1 / 2)).
        -- apply (Qmult_lt_0_compat 2 C).
           ++ unfold Qlt; simpl; lia.
           ++ apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)].
        -- (* 1 ≤ (1/2)·(2C)：桥 1 ≤ C == (1/2)·(2C) *)
           apply (Qle_trans _ C _).
           ++ exact (QleT'_to_Qle _ _ HC).  (* 1 ≤ C *)
      ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT.
         unfold Qdiv. field.
      * reflexivity.  (* 1/2 < 1 计算可判定 *)
    + apply QleT'_to_Qle. apply exp_partial_ge_one. apply Qle_to_QleT'. apply (Qlt_le_weak 0 y). exact Hypos.
  - (* y ≤ 0：S_{2m+1}(y) == S_{2m}(y) - |y|^{2m+1}/(2m+1)! ≥ 1/C - M^{...} > 1/(2C) *)
    assert (Ha : Qle 0 (- y)).
    { change (Qle 0 (- y)) with (Qle (- 0) (- y)).
      apply (Qopp_le_compat y 0). exact Hyneg. }
    assert (Ham : Qle (- y) M).
    { assert (Habs : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
      rewrite <- Habs. exact (QleT'_to_Qle _ _ Hy). }
    assert (Hsl : Qle (1 / C) (exp_partial (2 * m) y)).
    { apply QleT'_to_Qle. apply (exp_partial_even_lower M C y m HM HC HCser). exact Hy. }
    (* 尾项界：y^{2m+1} == -|y|^{2m+1}，|y|^{2m+1}/(2m+1)! ≤ M^{2m+1}/(2m+1)! < 1/(2C) *)
    assert (Htail_le : Qle (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))
                           (q_pow M (2 * m + 1) / q_fact (2 * m + 1))).
    { apply QleT'_to_Qle.
      apply (q_le_div_le (q_pow (Qabs y) (2 * m + 1)) (q_fact (2 * m + 1))
                         (q_pow M (2 * m + 1)) (q_fact (2 * m + 1))).
      - apply q_fact_pos.
      - apply q_fact_pos.
      - apply Qle_to_QleT'.
        apply (Qmult_le_compat_r (q_pow (Qabs y) (2 * m + 1)) (q_pow M (2 * m + 1))
                                 (q_fact (2 * m + 1))).
        + apply QleT'_to_Qle.
          apply q_pow_mono.
          * apply Qle_to_QleT'. apply Qabs_nonneg.
          * exact Hy.
        + apply QleT'_to_Qle.
          apply qltT_leT'. apply q_fact_pos. }
    assert (Htail_lt : Qlt (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))
                           (1 / (2 * C))).
    { apply (Qle_lt_trans _ (q_pow M (2 * m + 1) / q_fact (2 * m + 1)) _).
      - exact Htail_le.
      - exact (QltT_to_Qlt _ _ (Htail m (NatLe_lift _ _ Hm0))). }
    (* S_{2m+1}(y) == S_{2m}(y) - |y|^{2m+1}/(2m+1)! *)
    assert (Hstep : exp_partial (Datatypes.S (2 * m)) y ==
                    exp_partial (2 * m) y -
                    q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)).
    { assert (Hodd : q_pow y (Datatypes.S (2 * m)) == - q_pow (Qabs y) (Datatypes.S (2 * m))).
      { assert (Hm1 : Qabs y == - y) by (apply Qabs_neg; exact Hyneg).
        assert (Hy2 : y == - (Qabs y)).
        { transitivity (- (- y)).
          - apply Qeq_sym. apply Qopp_involutive.  (* y == -(-y) *)
          - apply (Qopp_comp (- y) (Qabs y)). exact (Qeq_sym _ _ Hm1). }
        (* y^{S(2m)} == (-|y|)^{S(2m)} == -|y|^{S(2m)}：q_pow_wd 桥 y == -|y|，
           q_pow_neg_odd 给 (-|y|)^{S(2m)} == -|y|^{S(2m)}（勿 setoid_rewrite 误伤 Qabs） *)
        transitivity (q_pow (- (Qabs y)) (Datatypes.S (2 * m))).
        - apply qeqT_imp_qeq.
          apply (q_pow_wd y (- (Qabs y)) (Datatypes.S (2 * m))).
          apply qeq_imp_qeqT. exact Hy2.
        - apply qeqT_imp_qeq. apply (q_pow_neg_odd (Qabs y) m). }
      (* 指数桥：S (2m) == 2m+1（q_pow_comp_proper 构造 Qeq 命题，lia 证 nat 相等） *)
      assert (Hidx_pow : q_pow (Qabs y) (Datatypes.S (2 * m)) == q_pow (Qabs y) (2 * m + 1)).
      { apply (q_pow_comp_proper (Qabs y) (Qabs y) (Qeq_refl (Qabs y))
                                (Datatypes.S (2 * m))%nat (2 * m + 1)%nat).
        lia. }
      assert (Hfn : (Datatypes.S (2 * m) = 2 * m + 1)%nat) by lia.
      assert (Hfq : q_fact (Datatypes.S (2 * m)) == q_fact (2 * m + 1)).
      { apply qeqT_imp_qeq. apply q_fact_nat_eq. exact Hfn. }
      (* 核心：y^{S(2m)}/q_fact(S(2m)) == -|y|^{2m+1}/(2m+1)! *)
      assert (Hsub : q_pow y (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)) ==
                     - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))).
      { unfold Qdiv.
        setoid_rewrite Hodd.
        setoid_rewrite Hidx_pow.
        setoid_rewrite Hfq.
        ring. }
      (* 组装：exp_partial (S(2m)) y == exp_partial (2m) y + 尾项 == 目标 RHS *)
      transitivity (exp_partial (2 * m) y + q_pow y (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))).
      - reflexivity.  (* exp_partial 定义展开：S(2m) = S (2*m) 且 2*m = 2*m *)
      - setoid_rewrite Hsub. ring. }
    rewrite Hstep.
    (* 1/C - |y|^{2m+1}/(2m+1)! > 1/(2C)：1/(2C) == 1/C - 1/(2C) < 1/C - t（t < 1/(2C)） *)
    apply (Qlt_le_trans _ (1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)) _).
    + (* 1/(2C) < 1/C - t：Qlt_minus_iff 双射 *)
      apply (Qlt_minus_iff (1 / (2 * C)) (1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))).
      assert (Htmp : 1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1) +
                     - (1 / (2 * C)) ==
                     1 / (2 * C) - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)).
      { field.
        split.
        - intro Heq0. destruct (q_neq_of_lt _ (q_fact_pos _) (qeq_imp_qeqT _ _ Heq0)).
        - assert (Hlt0C : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC)]). intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ Hlt0C) (qeq_imp_qeqT _ _ Heq0)). }
      setoid_rewrite Htmp.
      change (Qlt 0 (1 / (2 * C) + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))).
      apply (proj1 (Qlt_minus_iff (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)) (1 / (2 * C)))).
      exact Htail_lt.
    + (* 1/C - t ≤ S_{2m}(y) - t：Hsl 减法保序（先换形 -t == +(-t)） *)
      assert (Hrep : 1 / C - q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1) ==
                     1 / C + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) by ring.
      apply (Qle_trans _ (1 / C + - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) _).
{ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. exact Hrep. }
      { apply (Qle_trans _ (exp_partial (2 * m) y +
                            - (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1))) _).
        { apply (Qplus_le_compat (1 / C) (exp_partial (2 * m) y)
                               (- (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))
                               (- (q_pow (Qabs y) (2 * m + 1) / q_fact (2 * m + 1)))).
          - exact Hsl.
          - apply Qle_refl. }
{ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring. } }
Qed.

(* ============================================================
   cauchy_real_exp_pos 主定理：forall x : Real, real_lt zero (cauchy_real_exp x)
   （B3 最终步：exp_neg_pos 字段的实例化材料）
   策略：u 有界 |u n| ≤ M；exp_series_arch 给 C（exp_series n M ≤ C）；
   偶数截断 ≥ 1/C（exp_partial_even_lower），奇数截断 ≥ 1/(2C)
   （exp_partial_tail_small 选 m0 + exp_partial_odd_lower）；
   取 eps = 1/(2C)，对 n ≥ N（N 取 2·m0+1 保证奇偶都覆盖）。
   ============================================================ *)
Lemma cauchy_real_exp_pos : forall x : Real, real_lt real_zero (cauchy_real_exp x).
Proof.
  intros x. destruct x as [u Hu].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  destruct (exp_partial_tail_small M C (qltT_leT' 0 M HMpos) HC1) as [m0 Hm0].
  (* 构造 real_lt：eps = 1/(2C)（Set 正性链），N = 2·m0 + 1 *)
  exists (1 / (2 * C)).
  split.
  - apply (qltT_div_pos 1 (2 * C)).
    + exact qltT_0_1.
    + apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT.
  - exists (2 * m0 + 1)%nat.
    intros n Hn.
    assert (Hsub0 : exp_partial n (u n) - 0 == exp_partial n (u n)) by ring.
      change (QltT (1 / (2 * C)) (exp_partial n (u n) - 0)).
    apply (qltT_eq_compat_r (exp_partial n (u n) - 0) (exp_partial n (u n)) (1 / (2 * C))).
    + apply qeq_imp_qeqT. exact Hsub0.
    + (* 目标 QltT (1/(2C)) (exp_partial n (u n))：转 Prop 后分奇偶（ex 消去限制） *)
      apply Qlt_to_QltT.
      destruct (Nat.odd n) eqn:En.
      * (* n 奇：n = 2k+1，需 m0 ≤ k *)
        apply Nat.odd_spec in En. destruct En as [k Hk].
        subst n.
        apply NatLe_drop in Hn.
        assert (Hk0 : (m0 <= k)%nat) by lia.
        apply QltT_to_Qlt.
        apply (exp_partial_odd_lower M C m0 k (u (2 * k + 1)%nat) (qltT_leT' 0 M HMpos) HC1 HC Hm0 Hk0).
        exact (HM (2 * k + 1)%nat).
      * (* n 偶：n = 2k；1/(2C) < 1/C ≤ exp_partial (2k) (u (2k)) *)
        assert (Heven_true : Nat.even n = true).
        { rewrite <- (Nat.negb_odd n).
          rewrite En. reflexivity. }
        apply Nat.even_spec in Heven_true. destruct Heven_true as [k Hk].
        subst n.
        apply (Qlt_le_trans _ (1 / C) _).
        -- (* 1/(2C) < 1/C *)
           apply (Qlt_minus_iff (1 / (2 * C)) (1 / C)).
           unfold Qdiv.
           assert (Hf : 1 / C + - (1 / (2 * C)) == 1 / (2 * C)).
           { field.
             assert (Hlt0C : Qlt 0 C) by (apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]).
             intro Heq0. destruct (q_neq_of_lt C (Qlt_to_QltT _ _ Hlt0C) (qeq_imp_qeqT _ _ Heq0)). }
           setoid_rewrite Hf.
           apply (Qlt_le_trans _ (Qinv (2 * C)) _).
           { apply Qinv_lt_0_compat.
             apply (Qmult_lt_0_compat 2 C).
             - unfold Qlt; simpl; lia.
             - apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
        { apply QleT'_to_Qle. apply qeq_leT'.
          apply qeq_imp_qeqT.
          apply Qeq_sym. apply (Qmult_1_l (Qinv (2 * C))). }
        -- (* 1/C ≤ exp_partial (2k) (u (2k)) *)
           apply QleT'_to_Qle.
           apply (exp_partial_even_lower M C (u (2 * k)%nat) k (qltT_leT' 0 M HMpos) HC1 HC).
           exact (HM (2 * k)%nat).
Qed.

(* 反三角：| |a| − |b| | ≤ |a − b|（Prop 层 Qle 版，real_abs 柯西性核心）
   标准库已有 Qabs_triangle_reverse : Qabs x - Qabs y <= Qabs (x - y)，
   双向版 = 该引理 + 对称（Qabs_opp + Qabs_wd）*)
Lemma q_abs_abs_triangle : forall a b : Q,
  QleT' (Qabs (Qabs a - Qabs b)) (Qabs (a - b)).
Proof.
  intros a b.
  apply Qle_to_QleT'.
  apply Qabs_Qle_condition.
  split.
  - (* 左：-|a−b| ≤ |a|−|b| ⟸ |b|−|a| ≤ |a−b| 取负 *)
    apply (Qle_trans _ (Qopp (Qabs b - Qabs a)) _).
    + apply (Qopp_le_compat (Qabs b - Qabs a) (Qabs (a - b))).
      apply (Qle_trans _ (Qabs (b - a)) _).
      * apply Qabs_triangle_reverse.
      * (* |b−a| ≤ |a−b|：b−a == −(a−b)，Qabs_opp 对称 *)
        apply QleT'_to_Qle.
        apply qeq_leT'.
        apply qeq_imp_qeqT.
        transitivity (Qabs (- (a - b))).
        -- apply Qabs_wd. ring.
        -- apply Qabs_opp.
    + apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
  - (* 右：|a|−|b| ≤ |a−b|：标准库直接给 *)
    apply Qabs_triangle_reverse.
Qed.

(* 主文件 QltT 传递桥（若需）：QltT x y -> QltT y z -> QltT x z *)
Lemma qltT_trans : forall x y z : Q, QltT x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz.
  exact (Qlt_to_QltT x z
    (Qlt_trans x y z (QltT_to_Qlt x y Hxy) (QltT_to_Qlt y z Hyz))).
Qed.

(* real_abs：逐点 Qabs + 柯西性（反三角 + QltT 桥） *)
Definition real_abs (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n => Qabs (u n)).
  intros eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  (* 目标：QltT (Qabs (Qabs (u m) - Qabs (u n))) eps *)
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u m - u n)) _).
  - apply QleT'_to_Qle.
    apply (q_abs_abs_triangle (u m) (u n)).
  - apply QltT_to_Qlt. apply (HN m n Hm Hn).
Defined.

(* real_metric：|x − y| *)
Definition real_metric (x y : Real) : Real :=
  real_abs (real_plus x (real_opp y)).

(* |-x| == |x|：逐点 Qabs_opp（real_eq 版，逐 eps） *)
Lemma real_abs_opp : forall x : Real, real_eq (real_abs (real_opp x)) (real_abs x).
Proof.
  intros x. destruct x as [u Hu].
  unfold real_abs, real_opp, real_eq.
  intros eps Heps. exists 0%nat. intros n _.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ 0 _).
- apply QleT'_to_Qle. apply qeq_leT'.
    apply qeq_imp_qeqT.
    apply (Qabs_wd (Qabs (Qopp (u n)) - Qabs (u n)) 0).
    rewrite (Qabs_opp (u n)). ring.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* real_abs 的逐点投影：projT1 (real_abs x) n == Qabs (projT1 x n) *)
Lemma real_abs_proj : forall (x : Real) (n : nat),QeqT (
  projT1 (real_abs x) n ) ( Qabs (projT1 x n)).
Proof.
  intros x n. apply qeq_imp_qeqT. destruct x as [u Hu]. reflexivity.
Qed.

(* 三角不等式（逐 eps 形式，real_le 的 Or 编码无法表达"非严格且不趋近"，
   故用 Bishop 逐 eps 上界：∀eps>0 ∃N ∀n≥N，A_n ≤ B_n + eps） *)
Lemma real_abs_triangle_eps : forall (x y : Real) (eps : Q),
  QltT 0 eps -> sigT (fun N : nat => forall n : nat, NatLe N n ->
    QleT' (projT1 (real_abs (real_plus x y)) n)
        (projT1 (real_abs x) n + projT1 (real_abs y) n + eps)).
Proof.
  intros x y eps Heps.
  exists 0%nat. intros n _.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_plus x y) n)).
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj y n)).
  rewrite (qeqT_imp_qeq _ _ (real_plus_proj x y n)).
  destruct x as [u Hu]. destruct y as [v Hv].
  cbn [projT1].
  apply (Qle_trans _ (Qabs (u n) + Qabs (v n)) _).
  - exact (Qabs_triangle (u n) (v n)).
  - apply (Qle_trans _ (Qabs (u n) + Qabs (v n) + 0) _).
    + apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + apply (Qplus_le_compat (Qabs (u n) + Qabs (v n)) (Qabs (u n) + Qabs (v n)) 0 eps).
      * apply Qle_refl.
      * apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
Qed.

(* ============ 阶段 1 续：real_inv_pos（柯西倒数） ============ *)

(* 倒数差界（Qle 版）：0 < eps < a、0 < eps < b ⟹
   |1/a − 1/b| ≤ |a − b| · Qinv (eps·eps)
   证明：|1/a−1/b| == |a−b|/(|a||b|) ≤ |a−b|/eps²（q_le_div_le 扩分三明治） *)
Lemma q_inv_diff_bound :
  forall (a b eps : Q), QltT 0 eps -> QltT eps a -> QltT eps b ->
  QleT' (Qabs (Qinv a - Qinv b))
      (Qmult (Qabs (a - b)) (Qinv (Qmult eps eps))).
Proof.
  intros a b eps Heps Ha Hb.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (HaQ : Qlt eps a) by (apply QltT_to_Qlt; exact Ha).
  assert (HbQ : Qlt eps b) by (apply QltT_to_Qlt; exact Hb).
  apply Qle_to_QleT'.
  (* a,b > eps > 0 ⟹ 非零、正 *)
  assert (Ha0 : ~ a == 0) by (intro Heq0; destruct (q_neq_of_lt a (Qlt_to_QltT _ _ (Qlt_trans _ eps _ HepsQ HaQ)) (qeq_imp_qeqT _ _ Heq0))).
  assert (Hb0 : ~ b == 0) by (intro Heq0; destruct (q_neq_of_lt b (Qlt_to_QltT _ _ (Qlt_trans _ eps _ HepsQ HbQ)) (qeq_imp_qeqT _ _ Heq0))).
  assert (Hapos : Qlt 0 a) by (apply (Qlt_trans _ eps _); [exact HepsQ | exact HaQ]).
  assert (Hbpos : Qlt 0 b) by (apply (Qlt_trans _ eps _); [exact HepsQ | exact HbQ]).
  (* |1/a − 1/b| == |a − b| / (|a|·|b|) *)
  assert (Hmain : Qabs (Qinv a - Qinv b) ==
                  Qabs (a - b) / Qmult (Qabs a) (Qabs b)).
  { unfold Qdiv.
    transitivity (Qabs (Qmult (Qinv (Qmult a b)) (b - a))).
    - (* |1/a − 1/b| == |(b−a)/(ab)|：1/a − 1/b == (b−a)/(ab) *)
      apply Qabs_wd.
      field; split; assumption.
    - (* |(b−a)/(ab)| == |b−a|·|1/(ab)| == |a−b|/|ab| *)
      transitivity (Qmult (Qabs (Qinv (Qmult a b))) (Qabs (b - a))).
      + apply Qabs_Qmult.
      + transitivity (Qmult (Qabs (Qinv (Qmult a b))) (Qabs (a - b))).
        * apply Qmult_comp.
          -- apply Qeq_refl.
          -- (* Qabs (b−a) == Qabs (a−b)：b−a == −(a−b)，Qabs_wd + Qabs_opp *)
             apply (Qeq_trans _ (Qabs (- (a - b))) _).
             ++ apply Qabs_wd. ring.
             ++ apply Qabs_opp.
        * (* Qabs(|1/ab|)·|a−b| == |a−b|·Qinv(|ab|) == |a−b|·Qinv(|a||b|) *)
          transitivity (Qmult (Qabs (a - b)) (Qabs (Qinv (Qmult a b)))).
          -- apply Qeq_sym. apply Qmult_comm.
          -- transitivity (Qmult (Qabs (a - b)) (Qinv (Qabs (Qmult a b)))).
             ++ apply Qmult_comp.
                ** apply Qeq_refl.
                ** apply (Qabs_Qinv (Qmult a b)).
             ++ apply Qmult_comp.
                ** apply Qeq_refl.
                ** apply (Qinv_comp (Qabs (Qmult a b)) (Qmult (Qabs a) (Qabs b))).
                   apply Qabs_Qmult. }
  (* 用 q_le_div_le：a1=|a−b|、b1=|a||b|、c1=|a−b|、d1=eps·eps，需 |a−b|·eps² ≤ |a−b|·(|a||b|) *)
  rewrite Hmain.
  apply QleT'_to_Qle.
  apply (q_le_div_le (Qabs (a - b)) (Qmult (Qabs a) (Qabs b))
                      (Qabs (a - b)) (Qmult eps eps)).
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (Qabs a) (Qabs b)).
    + (* 0 < |a|：a > 0 ⟹ |a| == a *)
      apply (Qlt_le_trans _ a _).
      * exact Hapos.
      * apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos a). apply (Qlt_le_weak 0 a). exact Hapos.
    + apply (Qlt_le_trans _ b _).
      * exact Hbpos.
      * apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps eps); [exact HepsQ | exact HepsQ].
  - (* |a−b|·(eps·eps) ≤ |a−b|·(|a|·|b|)：|a−b| ≥ 0 且 eps·eps ≤ |a|·|b| *)
    (* 先换序：|a−b|·eps² == eps²·|a−b|，RHS 同理 *)
    apply Qle_to_QleT'.
    rewrite (Qmult_comm (Qabs (a - b)) (Qmult eps eps)).
    rewrite (Qmult_comm (Qabs (a - b)) (Qmult (Qabs a) (Qabs b))).
    apply (Qmult_le_compat_r (Qmult eps eps) (Qmult (Qabs a) (Qabs b)) (Qabs (a - b))).
    + (* eps·eps ≤ |a|·|b|：eps ≤ |a|、eps ≤ |b|（a,b > eps > 0） *)
      (* 分步：eps·eps ≤ eps·|b| ≤ |a|·|b|（Qmult_le_compat_r 两次） *)
      apply (Qle_trans _ (Qmult eps (Qabs b)) _).
      * (* eps·eps ≤ eps·|b|：右乘 eps，eps ≤ |b|（x·z ≤ y·z 给 eps·eps ≤ |b|·eps，换序） *)
        apply (Qle_trans _ (Qmult (Qabs b) eps) _).
        -- apply (Qmult_le_compat_r eps (Qabs b) eps).
           ++ apply (Qle_trans _ b _).
              ** apply (Qlt_le_weak _ _ HbQ).
              ** apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
           ++ apply (Qlt_le_weak 0 eps). exact HepsQ.
        -- apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qmult_comm.
      * (* eps·|b| ≤ |a|·|b|：右乘 |b|，eps ≤ |a| *)
        apply (Qmult_le_compat_r eps (Qabs a) (Qabs b)).
        -- apply (Qle_trans _ a _).
           ++ apply (Qlt_le_weak _ _ HaQ).
           ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos a). apply (Qlt_le_weak 0 a). exact Hapos.
        -- apply (Qlt_le_weak 0 (Qabs b)).
           apply (Qlt_le_trans _ b _).
           ++ exact Hbpos.
           ++ apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply (Qabs_pos b). apply (Qlt_le_weak 0 b). exact Hbpos.
    + apply Qabs_nonneg.
Qed.

(* real_inv_pos：柯西倒数（正下界 eps0 保护，m,n ≥ N0 时取 Qinv (u n)） *)
Definition real_inv_pos (x : Real) (Hx : real_lt real_zero x) : Real.
Proof.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  exists (fun n => if Nat.leb N0 n then Qinv (u n) else Qinv (u N0)).
  intros eps Heps.
  set (delta := Qmult eps (Qmult eps0 eps0)).
  assert (Hdlt : QltT 0 delta).
  { unfold delta. apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps (Qmult eps0 eps0)).
    - apply QltT_to_Qlt. exact Heps.
    - apply (Qmult_lt_0_compat eps0 eps0).
      + apply QltT_to_Qlt. exact Heps0.
      + apply QltT_to_Qlt. exact Heps0. }
  destruct (Hu delta Hdlt) as [N1 HN1].
  exists (Nat.max N0 N1).
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  assert (Hm0 : (N0 <= m)%nat) by lia.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  rewrite (leb_correct _ _ Hm0).
  rewrite (leb_correct _ _ Hn0).
  (* 目标：QltT (Qabs (Qinv (u m) - Qinv (u n))) eps *)
  apply Qlt_to_QltT.
  (* u m, u n > eps0：HN0 直接给 QltT eps0 (projT1 x m - 0)，x 已 destruct 为 existT u Hu *)
  assert (Hum : QltT eps0 (u m - 0)).
  { change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) m - projT1 real_zero m)).
    apply (HN0 m). apply NatLe_lift. exact Hm0. }
  assert (Hun : QltT eps0 (u n - 0)).
  { change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)).
    apply (HN0 n). apply NatLe_lift. exact Hn0. }
  apply (Qle_lt_trans _ (Qmult (Qabs (u m - u n)) (Qinv (Qmult eps0 eps0))) _).
  - apply QleT'_to_Qle.
    apply (q_inv_diff_bound (u m) (u n) eps0).
    + exact Heps0.
    + apply (qltT_eq_compat_r (u m) (u m - 0) eps0).
      * apply qeq_imp_qeqT. apply Qeq_sym. ring.
      * exact Hum.
    + apply (qltT_eq_compat_r (u n) (u n - 0) eps0).
      * apply qeq_imp_qeqT. apply Qeq_sym. ring.
      * exact Hun.
  - (* |u m − u n| · (1/eps0²) < eps：|u m − u n| < eps·eps0²（HN1 at delta） *)
    assert (Hdiff : QltT (Qabs (u m - u n)) delta).
    { apply (HN1 m n); apply NatLe_lift; lia. }
    unfold delta in Hdiff.
    (* (x·1/eps0²) < eps 由 x < eps·eps0²：乘 Qinv (eps0·eps0)（正） *)
    apply (Qlt_le_trans _ (Qmult (Qmult eps (Qmult eps0 eps0)) (Qinv (Qmult eps0 eps0))) _).
    { apply (Qmult_lt_compat_r (Qabs (u m - u n)) (Qmult eps (Qmult eps0 eps0))
                               (Qinv (Qmult eps0 eps0))).
      - apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat eps0 eps0).
        + apply QltT_to_Qlt. exact Heps0.
        + apply QltT_to_Qlt. exact Heps0.
      - exact (QltT_to_Qlt _ _ Hdiff). }
    { (* eps·(eps0·eps0)·(1/(eps0·eps0)) ≤ eps：约分 Qmult_inv_r *)
apply QleT'_to_Qle. apply qeq_leT'. apply qeq_imp_qeqT.
      transitivity (eps * ((eps0 * eps0) * Qinv (eps0 * eps0))).
      { apply Qeq_sym.
        apply (Qmult_assoc eps (Qmult eps0 eps0) (Qinv (Qmult eps0 eps0))). }
      { transitivity (eps * 1).
        + rewrite (Qmult_inv_r (Qmult eps0 eps0)).
          * reflexivity.
          * assert (Hltm : Qlt 0 (eps0 * eps0)) by (apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0).
            intro Heq0. destruct (q_neq_of_lt _ (Qlt_to_QltT _ _ Hltm) (qeq_imp_qeqT _ _ Heq0)).
        + ring. } }
Defined.

(* real_inv_pos 正确性：x · (1/x) == 1（n ≥ N0 时 u n·(1/u n) == 1，field） *)
Lemma real_inv_pos_correct :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x (real_inv_pos x Hx)) real_one.
Proof.
  intros x Hx.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  unfold real_mult, real_inv_pos, real_one, real_eq.
  intros eps Heps.
  exists N0.
  intros n Hn.
  (* 目标：QltT (Qabs (u n · (if N0≤n then 1/u n else 1/u N0) − 1)) eps *)
  (* 归约 projT1：real_mult 的序列 == fun n => u n · (if ...) *)
  cbn [projT1].
  destruct (Nat.leb N0 n) eqn:Eleb.
  - (* N0 ≤ n：用 1/u n；u n·(1/u n) == 1（Qmult_inv_r，u n ≠ 0） *)
    assert (Hun0 : ~ u n == 0).
    { assert (Hltun : Qlt 0 (u n)).
      { apply (Qlt_trans _ eps0 _); [apply QltT_to_Qlt; exact Heps0 | ].
      (* 目标：eps0 < u n；HN0 给 eps0 < u n - 0，桥 u n - 0 == u n *)
      apply (Qlt_le_trans _ (u n - 0) _).
      - apply QltT_to_Qlt.
        change (QltT eps0 (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n - projT1 real_zero n)).
        apply (HN0 n). apply NatLe_lift. apply Nat.leb_le. exact Eleb.
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      intro Heq0. destruct (q_neq_of_lt (u n) (Qlt_to_QltT _ _ Hltun) (qeq_imp_qeqT _ _ Heq0)). }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ 0 _).
    + (* |u n·(1/u n) − 1| == 0 ≤ 0：Hsub 后 Qabs_wd *)
      assert (Hsub : u n * / u n - 1 == 0).
      { rewrite (Qmult_inv_r (u n) Hun0). ring. }
      apply QleT'_to_Qle. apply qeq_le.
      apply qeq_imp_qeqT.
      (* 目标：Qabs (u n·(1/u n) − 1) == 0 *)
      transitivity (Qabs 0).
      * apply (Qabs_wd (u n * / u n - 1) 0). exact Hsub.
      * (* Qabs 0 == 0：Qabs_neg（0 ≤ 0） *)
        apply (Qeq_trans _ (- 0) _).
        -- apply Qabs_neg. apply Qle_refl.
        -- ring.
    + apply QltT_to_Qlt. exact Heps.
  - (* ¬N0 ≤ n：n < N0，用 1/u N0——但 real_eq 只需最终性质，n ≥ N0 已覆盖；
      此分支不可能（n ≥ N0 由 exists N0 保证）——排除 *)
    apply Nat.leb_gt in Eleb.
    apply NatLe_drop in Hn.
    exfalso. lia.
Qed.

(* real_inv_pos 正性：x > 0 ⟹ 1/x > 0
   策略：取 eps := Qinv (M+1)，n ≥ N0 时 u n ≤ M < M+1（Qinv_lt_contravar）
   得 Qinv (M+1) < Qinv (u n)，即 inv_n − 0 > eps *)
Lemma real_inv_pos_pos :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_lt real_zero (real_inv_pos x Hx).
Proof.
  intros x Hx.
  destruct x as [u Hu].
  destruct Hx as [eps0 [Heps0 [N0 HN0]]].
  (* 全局上界 M：|u k| ≤ M（real_norm_bounded） *)
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  (* 取 eps := Qinv (M + 1)，N := N0 *)
  unfold real_inv_pos, real_lt, real_zero.
  exists (Qinv (M + 1)).
  split.
  - (* 0 < Qinv (M+1) *)
    apply Qlt_to_QltT.
    apply Qinv_lt_0_compat.
    apply (Qlt_le_trans _ 1 _).
    + reflexivity.  (* 0 < 1 计算可判定 *)
    + (* 1 ≤ M+1：1 ≤ 1+M == M+1 *)
      apply (Qle_trans _ (1 + M) _).
      * apply (Qle_plus_nonneg_r 1 M). apply (Qlt_le_weak 0 M). apply QltT_to_Qlt. exact HMpos.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qplus_comm.
  - exists N0.
    intros n Hn.
    cbn [projT1].
    destruct (Nat.leb N0 n) eqn:Eleb.
    + (* n ≥ N0：inv_n == Qinv (u n)；需 Qinv (M+1) < Qinv (u n) *)
      apply Qlt_to_QltT.
      (* 前提：0 < u n、0 < M+1、u n < M+1 *)
      assert (Hu0 : Qlt 0 (u n)).
      { apply (Qlt_le_trans _ (u n - 0) _).
        - apply (Qlt_trans _ eps0 _).
          + apply QltT_to_Qlt. exact Heps0.
          + apply QltT_to_Qlt. apply (HN0 n). apply NatLe_lift. apply Nat.leb_le. exact Eleb.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      assert (HM1 : Qlt 0 (M + 1)).
      { apply (Qlt_le_trans _ 1 _); [reflexivity | ].
        apply (Qle_trans _ (1 + M) _).
        - apply (Qle_plus_nonneg_r 1 M). apply (Qlt_le_weak 0 M). apply QltT_to_Qlt. exact HMpos.
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qplus_comm. }
      assert (Hult : Qlt (u n) (M + 1)).
      { apply (Qle_lt_trans _ (Qabs (u n)) _).
        - apply Qle_Qabs.
        - apply (Qle_lt_trans _ M _).
          + apply QleT'_to_Qle. apply (HM n).
          + (* M < M+1：M == M+0，M+0 < M+1（Qplus_lt_r：0 < 1），再桥 M == M+0 *)
            apply (Qle_lt_trans _ (M + 0) _).
            * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.  (* M ≤ M+0：M == M+0 *)
            * apply (proj2 (Qplus_lt_r 0 1 M)). reflexivity.  (* M+0 < M+1 ⟸ 0 < 1 *) }
      (* 目标：QltT (Qinv (M+1)) (Qinv (u n) − 0)；RHS == Qinv (u n) *)
      apply (Qlt_le_trans _ (Qinv (u n)) _).
      { exact (proj1 (Qinv_lt_contravar (u n) (M + 1) Hu0 HM1) Hult). }
      { (* Qinv (u n) ≤ Qinv (u n) − 0：Qinv(u n) − 0 == Qinv(u n) 反向 *)
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
    + (* ¬N0 ≤ n：矛盾 *)
      apply Nat.leb_gt in Eleb.
      apply NatLe_drop in Hn.
      exfalso. lia.
Qed.

Print Assumptions Q2_nonneg.
Print Assumptions Qhalf_nonneg.
