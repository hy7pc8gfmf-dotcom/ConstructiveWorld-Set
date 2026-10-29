(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件：消融落件——原件全文逐字保留，仅将清单所列定理证明体         *)
(*   替换为玩具证（非平凡三口径），声明面/引用面零改动、零新增 Require；清单：     *)
(*   ln2i_p2_succ（原 L64，2 句；裸 reflexivity -> Qeq_refl 显式见证项 1 刀）。     *)
(* ============================================================ *)
(* UpReqLn2Irrational.v                                                          *)
(* 目的：母定理 lic_irrational_criterion 的 ln2 实例依赖模块：ln 2 = Σ_{k≥1}       *)
(*   1/(k·2^k) 的 Q 层部分和列 ln2i_x n = Σ_{k=1}^{n} 1/(k·2^k)（单调递增，          *)
(*   余项 0 < R_n < 2^{-n}，exact fractions 数值验真），误差窗 ln2i_e n = 2^{-n}     *)
(*   （Qinv(ln2i_p2 n) 形）。                                                      *)
(* 三件供给状态：① 尾控 ln2i_tail：绿（Defined，严格几何和界 2^{-n}−2^{-(n+K)}）；    *)
(*   ② 窗宽消失 ln2i_vanish：绿（Defined，N=den(eps)+1 配方，2^n ≥ n+1 桥）；         *)
(*   ③ 逃逸窗 ln2i_escape_witness：受阻（红线③申报）——e-级数逃逸靠 n!·s_n ∈ Z         *)
(*   的整递推给出窗位于尾控与间隙之间；ln2 级数公共母线为 2^n·(奇lcm)，有理间隙界     *)
(*   ≪ 2^{-n}，整递推 n!·2^n·(q−x_n) ∈ Z（n ≥ den q）只给                              *)
(*   |q−x_n| ≥ 2/(n!·2^n) ≪ 窗 2^{-n}，窗放不进「尾控上/间隙下」；本件以                *)
(*   ln2i_escape_spec 类型定义遗留，主装配走条件形 ln2i_irrational_criterion_cond，    *)
(*   证据 exact (lic_irrational_criterion …) 零旁路真走母定理。                        *)
(* 命名：ln2i_ 前缀（开工 grep 零撞名）。                                            *)
(* 公理面：本件纯构造性（零经典逻辑、零排中、零认授（未证断言））；语句面全 Set 层    *)
(*   （sigT/And/real_lt/QltT 形，无 Prop 泄露位）；证内 Prop（Qlt/Qle）仅作 Q 层推理   *)
(*   脚手架，不进结论面。                                                            *)
(* 依赖：UpReqIrrationalCriterion（母定理件，只读使用）；S01_BaseRing、                *)
(*   S02_CauchyComplete、S03_QExp、SumInvFactEscape、UpReqBanachNormOpp                *)
(*   （bno_mul_div_self 等）；Stdlib QArith、ZArith、Arith、Lia、Lra、Qfield。          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：Q 层通用小件                                                *)
(* ============================================================ *)

(* |u − v| == u − v（v ≤ u） *)
Lemma ln2i_abs_sub : forall u v : Q, Qle v u -> Qabs ((u - v)%Q) == (u - v)%Q.
Proof.
  intros u v H. apply Qabs_pos.
  unfold Qle in *. destruct u as [un ud]; destruct v as [vn vd].
  unfold Qminus, Qplus, Qopp. cbn [Qnum Qden] in *. lia.
Qed.

(* ============================================================ *)
(* S1：2 的幂（Q 层）与几何半恒等式                                   *)
(* ============================================================ *)

Fixpoint ln2i_p2 (n : nat) : Q :=
  match n with
  | O => (1 # 1)
  | Datatypes.S m => (2 # 1) * ln2i_p2 m
  end.

Lemma ln2i_p2_succ : forall m : nat, ln2i_p2 (Datatypes.S m) == ((2 # 1) * ln2i_p2 m)%Q.
Proof. intro m. exact (Qeq_refl ((2 # 1) * ln2i_p2 m)%Q). Qed.

Lemma ln2i_pow_ge : forall n : nat, (Datatypes.S n <= 2 ^ n)%nat.
Proof.
  induction n as [|n IH].
  - cbn. lia.
  - replace (2 ^ Datatypes.S n)%nat with (2 * 2 ^ n)%nat
      by (rewrite Nat.pow_succ_r'; reflexivity).
    lia.
Qed.

Lemma ln2i_powZ_pos : forall j : nat, (0 < Z.of_nat (2 ^ j))%Z.
Proof.
  intro j. pose proof (ln2i_pow_ge j) as Hp.
  apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
  rewrite Nat2Z.inj_succ in Hp. lia.
Qed.

(* p2 n 就是 2^n（显式指数形态，供 vanish 的 Z 层幂比较） *)
Lemma ln2i_p2_Z : forall n : nat, ln2i_p2 n == ((Z.of_nat (2 ^ n)) # 1)%Q.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite ln2i_p2_succ. rewrite IH.
    rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    cbn [Z.of_nat]. reflexivity.
Qed.

Lemma ln2i_p2_pos : forall n : nat, Qlt 0 (ln2i_p2 n).
Proof.
  intro n. rewrite ln2i_p2_Z.
  pose proof (ln2i_powZ_pos n) as Hp.
  unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma ln2i_p2_ne0 : forall n : nat, ~ (ln2i_p2 n == 0%Q).
Proof.
  intro n. intro Hc.
  exact (Qlt_not_eq 0%Q (ln2i_p2 n) (ln2i_p2_pos n) (eq_sym Hc)).
Qed.

(* 2^{-m} = 2^{-(m+1)} + 2^{-(m+1)}（Qinv 形几何半恒等式） *)
Lemma ln2i_inv_half : forall m : nat,
  (Qinv (ln2i_p2 (Datatypes.S m)) + Qinv (ln2i_p2 (Datatypes.S m)))%Q
  == Qinv (ln2i_p2 m).
Proof.
  intro m.
  assert (Hh : Qinv (2#1) == (1#2)) by reflexivity.
  rewrite (Qinv_mult_distr (2#1) (ln2i_p2 m)).
  rewrite Hh.
  ring.
Qed.

Lemma ln2i_inv_pos : forall m : nat, Qlt 0 (Qinv (ln2i_p2 m)).
Proof.
  intro m. rewrite ln2i_p2_Z.
  destruct (Z.of_nat (2 ^ m)) as [|pz|pz] eqn:E.
  - exfalso. pose proof (ln2i_powZ_pos m) as Hz. rewrite E in Hz. lia.
  - unfold Qinv, Qlt. cbn. lia.
  - unfold Qinv, Qlt. cbn. lia.
Qed.

(* ============================================================ *)
(* S2：级数项 1/(j·2^j) 与其对照界                                    *)
(* ============================================================ *)

Definition ln2i_t (j : nat) : Q := Qinv ((Z.of_nat j * Z.of_nat (2 ^ j)) # 1).

(* Qinv 非严格反序：0 < u ≤ v ⟹ v⁻¹ ≤ u⁻¹ *)
Lemma ln2i_inv_le : forall u v : Q, Qlt 0 u -> Qle u v -> Qle (Qinv v) (Qinv u).
Proof.
  intros [un ud] [vn vd]. unfold Qlt, Qle, Qinv in *.
  destruct un; destruct vn; cbn in *; try lia; nia.
Qed.

Lemma ln2i_t_pos : forall j : nat, (1 <= j)%nat -> Qlt 0 (ln2i_t j).
Proof.
  intros j Hj. unfold ln2i_t. apply Qinv_lt_0_compat.
  unfold Qlt. cbn [Qnum Qden].
  pose proof (ln2i_powZ_pos j) as Hp.
  assert (Hj1 : (0 < Z.of_nat j)%Z) by lia.
  nia.
Qed.

(* 项级界：1/(j·2^j) ≤ 2^{-j}（j ≥ 1；j=1 取等） *)
Lemma ln2i_t_le : forall j : nat, (1 <= j)%nat -> Qle (ln2i_t j) (Qinv (ln2i_p2 j)).
Proof.
  intros j Hj. rewrite ln2i_p2_Z. unfold ln2i_t.
  apply (ln2i_inv_le ((Z.of_nat (2 ^ j)) # 1)
           ((Z.of_nat j * Z.of_nat (2 ^ j)) # 1)).
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (ln2i_powZ_pos j) as Hp. lia.
  - unfold Qle. cbn [Qnum Qden].
    assert (Hj1 : (0 < Z.of_nat j)%Z) by lia.
    nia.
Qed.

(* ============================================================ *)
(* S3：部分和列、几何尾和、严格几何和界                                  *)
(* ============================================================ *)

(* 部分和：x_n = Σ_{k=1}^{n} 1/(k·2^k) *)
Fixpoint ln2i_x (n : nat) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S m => ln2i_x m + ln2i_t (Datatypes.S m)
  end.

(* 加权尾和 gsum n K = Σ_{i=1}^{K} 1/((n+i)·2^{n+i})（S 形指标） *)
Fixpoint ln2i_gsum (n K : nat) : Q :=
  match K with
  | O => 0%Q
  | Datatypes.S k => ln2i_gsum n k + ln2i_t (Datatypes.S (n + k))
  end.

(* 纯几何尾和 hsum n K = Σ_{i=1}^{K} 2^{-(n+i)}（S 形指标） *)
Fixpoint ln2i_hsum (n K : nat) : Q :=
  match K with
  | O => 0%Q
  | Datatypes.S k => ln2i_hsum n k + Qinv (ln2i_p2 (Datatypes.S (n + k)))
  end.

Lemma ln2i_gsum_ge0 : forall n K : nat, Qle 0%Q (ln2i_gsum n K).
Proof.
  intros n K. induction K as [|k IH].
  - cbn [ln2i_gsum]. apply Qle_refl.
  - cbn [ln2i_gsum].
    apply (Qplus_le_compat 0%Q (ln2i_gsum n k) 0%Q (ln2i_t (Datatypes.S (n + k))));
      [exact IH | apply Qlt_le_weak; apply ln2i_t_pos; lia].
Qed.

Lemma ln2i_gsum_le_hsum : forall n K : nat, Qle (ln2i_gsum n K) (ln2i_hsum n K).
Proof.
  intros n K. induction K as [|k IH].
  - cbn [ln2i_gsum ln2i_hsum]. apply Qle_refl.
  - cbn [ln2i_gsum ln2i_hsum].
    apply (Qplus_le_compat (ln2i_gsum n k) (ln2i_hsum n k)
             (ln2i_t (Datatypes.S (n + k)))
             (Qinv (ln2i_p2 (Datatypes.S (n + k))))).
    + exact IH.
    + apply ln2i_t_le. lia.
Qed.

(* 几何和界：hsum n K + 2^{-(n+K)} ≤ 2^{-n}（半恒等式归纳） *)
Lemma ln2i_hsum_le : forall n K : nat,
  Qle (ln2i_hsum n K + Qinv (ln2i_p2 (n + K)))%Q (Qinv (ln2i_p2 n)).
Proof.
  intros n K. induction K as [|k IH].
  - cbn [ln2i_hsum]. rewrite Nat.add_0_r. rewrite Qplus_0_l. apply Qle_refl.
  - cbn [ln2i_hsum].
    replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    rewrite <- Qplus_assoc.
    rewrite (ln2i_inv_half (n + k)).
    exact IH.
Qed.

Lemma ln2i_hsum_lt : forall n K : nat, Qlt (ln2i_hsum n K) (Qinv (ln2i_p2 n)).
Proof.
  intros n K. destruct K as [|k].
  - cbn [ln2i_hsum]. apply ln2i_inv_pos.
  - pose proof (ln2i_hsum_le n (Datatypes.S k)) as Hle.
    assert (HXp : Qlt 0 (Qinv (ln2i_p2 (n + Datatypes.S k))))
      by apply ln2i_inv_pos.
    assert (Hlt1 : Qlt (ln2i_hsum n (Datatypes.S k))
                     (ln2i_hsum n (Datatypes.S k)
                      + Qinv (ln2i_p2 (n + Datatypes.S k)))%Q)
      by (apply (lic_qlt_lt_add_r _ _); exact HXp).
    exact (Qlt_le_trans _ _ _ Hlt1 Hle).
Qed.

(* 核心界：gsum n K < 2^{-n} *)
Lemma ln2i_gsum_lt : forall n K : nat, Qlt (ln2i_gsum n K) (Qinv (ln2i_p2 n)).
Proof.
  intros n K.
  exact (Qle_lt_trans (ln2i_gsum n K) (ln2i_hsum n K) (Qinv (ln2i_p2 n))
           (ln2i_gsum_le_hsum n K) (ln2i_hsum_lt n K)).
Qed.

(* 部分和加法形：x_{n+K} == x_n + gsum n K *)
Lemma ln2i_x_add : forall n K : nat,
  ln2i_x (n + K) == (ln2i_x n + ln2i_gsum n K)%Q.
Proof.
  intros n K. induction K as [|k IH].
  - cbn [ln2i_gsum]. rewrite Nat.add_0_r. ring.
  - replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k))%nat by lia.
    cbn [ln2i_x ln2i_gsum]. rewrite IH. ring.
Qed.

Lemma ln2i_x_diff : forall n K : nat,
  (ln2i_x (n + K) - ln2i_x n)%Q == ln2i_gsum n K.
Proof.
  intros n K. rewrite ln2i_x_add. unfold Qminus. ring.
Qed.

(* 单调性：n ≤ k ⟹ x_n ≤ x_k *)
Lemma ln2i_mono : forall n k : nat, (n <= k)%nat -> Qle (ln2i_x n) (ln2i_x k).
Proof.
  intros n k Hnk.
  assert (Hk : k = (n + (k - n))%nat) by lia.
  rewrite Hk. rewrite ln2i_x_add.
  apply (Qle_trans (ln2i_x n) (ln2i_x n + 0%Q)
           (ln2i_x n + ln2i_gsum n (k - n))%Q).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qplus_0_r.
  - apply (Qplus_le_compat (ln2i_x n) (ln2i_x n) 0%Q
             (ln2i_gsum n (k - n)));
      [apply Qle_refl | apply ln2i_gsum_ge0].
Qed.

(* ============================================================ *)
(* S4：误差窗 e_n = 2^{-n}、尾控与消失两件供给                            *)
(* ============================================================ *)

Definition ln2i_e (n : nat) : Q := Qinv (ln2i_p2 n).

(* 尾控：n ≥ 1、k ≥ n ⟹ |x_k − x_n| < 2^{-n} *)
Definition ln2i_tail : lic_tail_bounded ln2i_x ln2i_e.
Proof.
  intros n k Hn1 Hnk.
  remember (k - n)%nat as K eqn:HK.
  assert (Hk : k = (n + K)%nat) by (rewrite HK; lia).
  rewrite Hk.
  pose proof (ln2i_gsum_lt n K) as Hlt0.
  pose proof (ln2i_x_diff n K) as Hsub.
  assert (Hge : Qle 0%Q ((ln2i_x (n + K) - ln2i_x n)%Q)).
  { rewrite ln2i_x_add.
    assert (Hr : ((ln2i_x n + ln2i_gsum n K) - ln2i_x n)%Q == ln2i_gsum n K)
      by (unfold Qminus; ring).
    rewrite Hr. apply ln2i_gsum_ge0. }
  apply Qlt_to_QltT.
  rewrite (Qabs_pos ((ln2i_x (n + K) - ln2i_x n)%Q) Hge).
  rewrite Hsub. exact Hlt0.
Defined.

(* 消失：2^{-n} → 0（N = den(eps)+1，2^n ≥ n+1 桥） *)
Definition ln2i_vanish : lic_vanish ln2i_e.
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  pose proof Heps0 as HepsZ.
  unfold Qlt in HepsZ. cbn [Qnum Qden] in HepsZ.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  assert (HpdQ : Qle (Qinv (pn # pd)) ((Z.pos pd) # 1)).
  { unfold Qinv, Qle. destruct pn as [|pp|pp]; cbn in *; try lia; nia. }
  exists (Datatypes.S (Z.to_nat (Z.pos pd))).
  intros n Hn. destruct n as [|n'].
  - lia.
  - assert (Hn1 : (1 <= Datatypes.S n')%nat) by lia.
    assert (Hid : Z.of_nat (Z.to_nat (Z.pos pd)) = Z.pos pd)
      by (apply Z2Nat.id; lia).
    assert (Hdn : (Z.pos pd < Z.of_nat (Datatypes.S n'))%Z).
    { pose proof (proj1 (Nat2Z.inj_le _ _) Hn) as Hz.
      rewrite Nat2Z.inj_succ in Hz. rewrite Hid in Hz. lia. }
    assert (Hpow : (Z.of_nat (Datatypes.S n') <= Z.of_nat (2 ^ Datatypes.S n'))%Z).
    { pose proof (ln2i_pow_ge (Datatypes.S n')) as Hp.
      apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
      rewrite Nat2Z.inj_succ in Hp. lia. }
    assert (HposA : Qlt 0 ((Z.of_nat (2 ^ Datatypes.S n')) # 1)).
    { pose proof (ln2i_powZ_pos (Datatypes.S n')) as Hp.
      unfold Qlt. cbn [Qnum Qden]. lia. }
    assert (HltB : Qlt ((Z.pos pd) # 1) ((Z.of_nat (Datatypes.S n')) # 1)).
    { unfold Qlt. cbn [Qnum Qden]. lia. }
    assert (HgeA : Qle ((Z.of_nat (Datatypes.S n')) # 1)
                       ((Z.of_nat (2 ^ Datatypes.S n')) # 1)).
    { unfold Qle. cbn [Qnum Qden]. lia. }
    assert (Hk : Qlt (Qinv (pn # pd)) ((Z.of_nat (2 ^ Datatypes.S n')) # 1))
      by (apply (Qlt_le_trans (Qinv (pn # pd)) ((Z.of_nat (Datatypes.S n')) # 1)
                   ((Z.of_nat (2 ^ Datatypes.S n')) # 1));
          [apply (Qle_lt_trans (Qinv (pn # pd)) ((Z.pos pd) # 1)
                    ((Z.of_nat (Datatypes.S n')) # 1)); assumption
          | exact HgeA]).
    apply Qlt_to_QltT.
    unfold ln2i_e. rewrite ln2i_p2_Z.
    rewrite <- (Qinv_involutive (pn # pd)).
    apply (proj1 (Qinv_lt_contravar (Qinv (pn # pd))
                    ((Z.of_nat (2 ^ Datatypes.S n')) # 1)
                    (Qinv_lt_0_compat _ Heps0) HposA)).
    exact Hk.
Defined.

(* ============================================================ *)
(* S5：逃逸窗遗留位 + 条件形主装配（真走母定理，零旁路）                     *)
(* ============================================================ *)

(* 逃逸窗类型定义（见证构造受阻，红线③申报；见交付报告 §逃逸窗） *)
Definition ln2i_escape_spec : Set := lic_escape_window ln2i_x ln2i_e.

(* 条件形主定理：逃逸窗见证一旦供给，即得「lim x_n 对每个有理数 q          *)
(* 存在 Q 层正分离常数 c 使 real_const c < |X − q|」——母定理 exact 装配。 *)
Theorem ln2i_irrational_criterion_cond : forall (Hesc : ln2i_escape_spec) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u) ln2i_x
                         (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish))
       (real_const q)))).
Proof.
  intros Hesc q.
  exact (lic_irrational_criterion ln2i_x ln2i_e ln2i_tail Hesc ln2i_vanish q).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction ln2i_irrational_criterion_cond ln2i_tail ln2i_vanish
  ln2i_x ln2i_e ln2i_t ln2i_p2 ln2i_gsum ln2i_hsum.

Print Assumptions ln2i_irrational_criterion_cond.
