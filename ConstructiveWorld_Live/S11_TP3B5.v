(* ============================================================ *)
(* S11_TP3B5.v —— 论文3 B5 模块：arctan 级数与 sin/cos 在单位域    *)
(*   的逐点连续性链（Q 层 + Real 层，构造性 Set 层）。              *)
(* ── 使命：arctan 在单位域内逐点连续；sin/cos 连续；               *)
(*   4·arctan(1) == π_L 值桥；同名非平凡替换件（消除逐句转发，       *)
(*   展开至定义层显式装配，替换定理 b3_one_minus_q_pos、             *)
(*   atan_odd_nonneg、atan_odd_neq、b3_abs_sq、b3_one_plus_sq_neq、  *)
(*   b3_inv_sq_r 语句与声明序不变）。                                *)
(* ── 依赖：S01–S10；Stdlib（QArith、Qabs、Qround、List、Bool、     *)
(*   Arith、Setoid、Morphisms、Lia、Qminmax、Lqa）。                 *)
(* ── 构造性注记：纯构造性；零承认语句；替换证明以真证明 Qed 闭合；   *)
(*   文件尾附假设面打印锚。                                          *)
(* ── 编译配方：全字面 COQLIB/ROCQLIB 双 export 后 coqc -Q           *)
(*   ../../Live_X "" -Q . "" S11_TP3B5.v。                           *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.


(* ============================================================ *)
(* SC-2 批（并入 203）：N9a arctan 级数（T-pi3 A1/B3-1）      *)
(* arctan_term/partial + 模量 + cauchy_real_arctan + x=1 桥   *)
(* ============================================================ *)

(* ================================================================== *)
(*  sT1_arctan / p_n9a_q1.v  N9a Q 层（一）：定义与基础恒等             *)
(*  基态：ConstructiveWorld.vo（迭代 200）                           *)
(*  内容：arctan_term/arctan_partial/atan_mag 定义；奇数分母正性；       *)
(*        平方-绝对值恒等；项模长非负；|arctan_term k x|==atan_mag      *)
(* ================================================================== *)

(* ---- 定义 ---- *)
(* arctan_term k x := (−1)^k · x^{2k+1} / (2k+1) *)
Definition arctan_term (k : nat) (x : Q) : Q :=
  q_pow (-1) k * (q_pow x (2 * k + 1) / (Z.of_nat (2 * k + 1) # 1)).

(* 部分和 arctan_partial n x = Σ_{k=0}^{n} arctan_term k x *)
Fixpoint arctan_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => arctan_term 0 x
  | Datatypes.S m => arctan_partial m x + arctan_term (Datatypes.S m) x
  end.

(* 项模长 atan_mag k x := |x|^{2k+1}/(2k+1)（|arctan_term k x| 的闭式） *)
Definition atan_mag (k : nat) (x : Q) : Q :=
  q_pow (Qabs x) (2 * k + 1) / (Z.of_nat (2 * k + 1) # 1).

(* ---- 奇数分母 (2k+1) 的正性 ---- *)
Lemma atan_odd_pos : forall k : nat, Qlt 0 (Z.of_nat (2 * k + 1) # 1).
Proof.
  intro k.
  unfold Qlt; simpl.
  lia.
Qed.

Lemma atan_odd_nonneg : forall k : nat, Qle 0 (Z.of_nat (2 * k + 1) # 1).
Proof.
  intro k.
  (* 三级提升链：nat 层非负见证（算术面）→ 整数域内嵌自然反映面提升 →
     Q 序定义体落实（展开＋显式换算落 Z 乘法面）——不经弱序桥单跳，
     不取用姊妹件（奇数分母严格正件保持独立）。 *)
  assert (Hn : (0 <= 2 * k + 1)%nat) by lia.
  assert (Hz : (0 <= Z.of_nat (2 * k + 1))%Z) by lia.
  unfold Qle.
  change (0 * 1 <= Z.of_nat (2 * k + 1) * 1)%Z.
  rewrite Z.mul_0_l, Z.mul_1_r.
  exact Hz.
Qed.

Lemma atan_odd_neq : forall k : nat, ~ (Z.of_nat (2 * k + 1) # 1) == 0.
Proof.
  intros k Heq.
  (* 提升链反向坍缩（与 atan_odd_nonneg 提升链同构）：商等式落定义体（分子/分母
     投影归约至整数层），自然层线性算术构造性排除——不经非等换形桥、
     不取用姊妹正性件。 *)
  unfold Qeq in Heq. simpl in Heq. lia.
Qed.

(* ---- x·x == |x|·|x|（Qcompare 三分，纯构造） ---- *)
Lemma atan_sq_abs : forall x : Q, x * x == Qabs x * Qabs x.
Proof.
  intro x.
  destruct (Qcompare x 0) eqn:E.
  - (* x == 0 *)
    assert (Hx : x == 0) by (apply (proj2 (Qeq_alt x 0)); exact E).
    setoid_rewrite Hx. reflexivity.
  - (* x < 0 *)
    assert (Hx : x < 0) by (apply (proj2 (Qlt_alt x 0)); exact E).
    assert (Hle : x <= 0) by (apply Qlt_le_weak; exact Hx).
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; exact Hle).
    setoid_rewrite Habs. ring.
  - (* 0 < x *)
    assert (Hx : 0 < x) by (apply (proj2 (Qgt_alt x 0)); exact E).
    assert (Hle : 0 <= x) by (apply Qlt_le_weak; exact Hx).
    assert (Habs : Qabs x == x) by (apply Qabs_pos; exact Hle).
    setoid_rewrite Habs. reflexivity.
Qed.

(* ---- 项模长非负 ---- *)
Lemma atan_mag_nonneg : forall (k : nat) (x : Q), Qle 0 (atan_mag k x).
Proof.
  intros k x.
  unfold atan_mag.
  (* 0 == 0/1 ≤ q_pow(|x|,2k+1)/d *)
  apply (q_le_div_le 0 1 (q_pow (Qabs x) (2 * k + 1)) (Z.of_nat (2 * k + 1) # 1)).
  - unfold Qlt; simpl; lia.
  - apply atan_odd_pos.
  - assert (Hz : 0 * (Z.of_nat (2 * k + 1) # 1) == 0) by ring.
    setoid_rewrite Hz.
    assert (Hone : q_pow (Qabs x) (2 * k + 1) * 1 == q_pow (Qabs x) (2 * k + 1)) by ring.
    setoid_rewrite Hone.
    apply q_pow_nonneg. apply Qabs_nonneg.
Qed.

(* ---- q_pow 加法：x^{a+b} == x^a · x^b ---- *)
Lemma atan_q_pow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b) == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction b as [| b IH].
  - replace (a + 0)%nat with a by lia.
    change (q_pow x a == q_pow x a * 1). ring.
  - replace (a + Datatypes.S b)%nat with (Datatypes.S (a + b)) by lia.
    setoid_rewrite (q_pow_succ x (a + b)).
    setoid_rewrite (q_pow_succ x b).
    setoid_rewrite IH. ring.
Qed.

(* x^{2k+3} == x^2 · x^{2k+1}（奇次幂一步） *)
Lemma atan_q_pow_odd3 : forall (x : Q) (k : nat),
  q_pow x (2 * k + 3) == (x * x) * q_pow x (2 * k + 1).
Proof.
  intros x k.
  replace (2 * k + 3)%nat with ((2 * k + 1) + 2)%nat by lia.
  setoid_rewrite (atan_q_pow_add x (2 * k + 1) 2). simpl. ring.
Qed.

(* c 序列一步：atan_mag (S k) x == |x|²·|x|^{2k+1}/(2k+3) *)
Lemma atan_mag_succ_geom : forall (x : Q) (k : nat),
  atan_mag (Datatypes.S k) x ==
  (Qabs x * Qabs x) * q_pow (Qabs x) (2 * k + 1) / (Z.of_nat (2 * k + 3) # 1).
Proof.
  intros x k.
  unfold atan_mag.
  replace (2 * Datatypes.S k + 1)%nat with (2 * k + 3)%nat by lia.
  unfold Qdiv.
  setoid_rewrite (atan_q_pow_odd3 (Qabs x) k).
  reflexivity.
Qed.

(* ---- |arctan_term k x| == atan_mag k x ---- *)
Lemma arctan_term_abs : forall (k : nat) (x : Q),
  Qabs (arctan_term k x) == atan_mag k x.
Proof.
  intros k x.
  unfold arctan_term, atan_mag, Qdiv.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite sc_abs_sign.
  setoid_rewrite q_pow_abs.
  setoid_rewrite Qabs_Qinv.
  assert (Hd : Qabs (Z.of_nat (2 * k + 1) # 1) == Z.of_nat (2 * k + 1) # 1).
  { apply Qabs_pos. apply atan_odd_nonneg. }
  setoid_rewrite Hd.
  ring.
Qed.
(* ================================================================== *)
(*  sT1_arctan / p_n9a_q2.v  N9a Q 层（二）：交错级数尾界               *)
(*  依赖：p_n9a_q1（定义/基础恒等）+ CW.ConstructiveWorld                *)
(*  内容：|x|≤1 ⟹ 成对项 |t_j+t_{j+1}|==c_j−c_{j+1}（c:=atan_mag）；    *)
(*        c 递减；Leibniz 余项界 |S_n−S_m| ≤ c_{m+1}（lt_wf 强归纳）     *)
(* ================================================================== *)

(* 括号因子：br j x := /(2j+1) − x²·/(2j+3)（成对项因子；|x|≤1 时 ≥ 0） *)
Definition atan_br (j : nat) (x : Q) : Q :=
  Qinv (Z.of_nat (2 * j + 1) # 1) -
  (x * x) * Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1).

(* ---- |x| ≤ 1 ⟹ x² ≤ 1 ---- *)
Lemma atan_sq_le_one : forall x : Q, QleT' (Qabs x) 1 -> Qle (x * x) 1.
Proof.
  intros x Hx.
  assert (Hle : Qle (Qabs x) 1) by (apply QleT'_to_Qle; exact Hx).
  apply (Qle_trans _ (Qabs x * Qabs x) _).
  - apply qeq_imp_qle. exact (atan_sq_abs x).
  - apply (Qle_trans _ (1 * (Qabs x)) _).
    + apply (Qmult_le_compat_r (Qabs x) 1 (Qabs x)); [exact Hle | apply Qabs_nonneg].
    + apply (Qle_trans _ (1 * 1) _).
      * apply sc_qmult_le_l; [exact Hle | exact Qle_0_1].
      * apply qeq_le. ring.
Qed.

(* ---- br j x ≥ 0（|x| ≤ 1） ---- *)
Lemma atan_br_nonneg : forall (j : nat) (x : Q), QleT' (Qabs x) 1 -> Qle 0 (atan_br j x).
Proof.
  intros j x Hx.
  unfold atan_br.
  apply (proj1 (Qle_minus_iff ((x * x) * Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1))
                              (Qinv (Z.of_nat (2 * j + 1) # 1)))).
  (* x²·/d2 ≤ /d1 *)
  apply (Qle_trans _ (1 * Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1)) _).
  - (* x²·/d2 ≤ 1·/d2 *)
    apply (Qle_trans _ (Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1) * (x * x)) _).
    + apply qeq_imp_qle. ring.
    + apply (Qle_trans _ (Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1) * 1) _).
      * apply (sc_qmult_le_l (x * x) 1 (Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1))).
        -- apply atan_sq_le_one. exact Hx.
        -- apply (Qlt_le_weak 0 (Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1))).
           apply Qinv_lt_0_compat. apply atan_odd_pos.
      * apply qeq_imp_qle. ring.
  - (* /d2 ≤ /d1（d1 < d2 ⟹ /d2 < /d1） *)
    apply (Qle_trans _ (Qinv (Z.of_nat (2 * Datatypes.S j + 1) # 1)) _).
    + apply qeq_imp_qle. ring.
    + apply Qlt_le_weak.
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * j + 1) # 1)
                                     (Z.of_nat (2 * Datatypes.S j + 1) # 1)
                                     (atan_odd_pos j) (atan_odd_pos (Datatypes.S j)))).
      unfold Qlt; simpl. lia.
Qed.

(* ---- 代数分解：t_j + t_{S j} == (−1)^j · x^{2j+1}·(br j x) ---- *)
Lemma atan_pair_factor : forall (j : nat) (x : Q),
  arctan_term j x + arctan_term (Datatypes.S j) x ==
  q_pow (-1) j * (q_pow x (2 * j + 1) * atan_br j x).
Proof.
  intros j x.
  unfold arctan_term, atan_br, Qdiv.
  assert (Hs : q_pow (-1) (Datatypes.S j) == - q_pow (-1) j).
  { rewrite (q_pow_succ (-1) j). ring. }
  assert (Hpow : q_pow x (2 * Datatypes.S j + 1) == (x * x) * q_pow x (2 * j + 1)).
  { replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
    apply atan_q_pow_odd3. }
  setoid_rewrite Hs.
  setoid_rewrite Hpow.
  ring.
Qed.

(* ---- 成对项界：|t_j + t_{S j}| == c_j − c_{S j}（|x| ≤ 1） ---- *)
Lemma atan_pair_abs : forall (j : nat) (x : Q), QleT' (Qabs x) 1 ->
  Qabs (arctan_term j x + arctan_term (Datatypes.S j) x) ==
  atan_mag j x - atan_mag (Datatypes.S j) x.
Proof.
  intros j x Hx.
  assert (Hal : arctan_term j x + arctan_term (Datatypes.S j) x ==
                q_pow (-1) j * (q_pow x (2 * j + 1) * atan_br j x)).
  { apply atan_pair_factor. }
  (* 2. LHS == |x|^{2j+1}·br *)
  assert (Hlhs : Qabs (arctan_term j x + arctan_term (Datatypes.S j) x) ==
                 q_pow (Qabs x) (2 * j + 1) * atan_br j x).
  { apply (Qeq_trans _ (Qabs (q_pow (-1) j * (q_pow x (2 * j + 1) * atan_br j x))) _).
    - apply (Qabs_wd (arctan_term j x + arctan_term (Datatypes.S j) x)
                     (q_pow (-1) j * (q_pow x (2 * j + 1) * atan_br j x))).
      exact Hal.
    - setoid_rewrite Qabs_Qmult.
      setoid_rewrite Qabs_Qmult.
      setoid_rewrite sc_abs_sign.
      setoid_rewrite q_pow_abs.
      assert (HB0 : Qle 0 (atan_br j x)) by (apply atan_br_nonneg; exact Hx).
      assert (HabsB : Qabs (atan_br j x) == atan_br j x) by (apply Qabs_pos; exact HB0).
      setoid_rewrite HabsB.
      ring. }
  (* 3. c_j − c_{S j} == |x|^{2j+1}·br *)
  assert (Hrhs : atan_mag j x - atan_mag (Datatypes.S j) x ==
                 q_pow (Qabs x) (2 * j + 1) * atan_br j x).
  { unfold atan_mag, atan_br, Qdiv.
    replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
    setoid_rewrite (atan_q_pow_odd3 (Qabs x) j).
    setoid_rewrite <- (atan_sq_abs x).
    ring. }
  apply (Qeq_trans _ (q_pow (Qabs x) (2 * j + 1) * atan_br j x) _).
  - exact Hlhs.
  - apply Qeq_sym. exact Hrhs.
Qed.

(* ---- c 递减：|x| ≤ 1 ⟹ c_{S j} ≤ c_j ---- *)
Lemma atan_mag_decr : forall (j : nat) (x : Q), QleT' (Qabs x) 1 ->
  Qle (atan_mag (Datatypes.S j) x) (atan_mag j x).
Proof.
  intros j x Hx.
  apply (proj2 (Qle_minus_iff (atan_mag (Datatypes.S j) x) (atan_mag j x))).
  apply (Qle_trans _ (Qabs (arctan_term j x + arctan_term (Datatypes.S j) x)) _).
  - apply Qabs_nonneg.
  - apply qeq_imp_qle. apply atan_pair_abs. exact Hx.
Qed.

(* ---- 尾界（Leibniz 余项）：m ≤ n ⟹ |S_n − S_m| ≤ c_{S m} ---- *)
Lemma atan_tail_bound : forall (x : Q) (m n : nat), QleT' (Qabs x) 1 -> (m <= n)%nat ->
  Qle (Qabs (arctan_partial n x - arctan_partial m x)) (atan_mag (Datatypes.S m) x).
Proof.
  intros x.
  assert (Hgen : forall (d m n : nat), QleT' (Qabs x) 1 -> (m <= n)%nat -> (n - m)%nat = d ->
     Qle (Qabs (arctan_partial n x - arctan_partial m x)) (atan_mag (Datatypes.S m) x)).
  { induction d as [d IH] using lt_wf_ind.
    intros m n Hx Hmn Hd.
    destruct (Nat.leb (Datatypes.S (Datatypes.S m)) n) eqn:E2.
    - (* m + 2 ≤ n：配对 (t_{S m} + t_{S(S m)}) + IH（下界 m+2） *)
      apply Nat.leb_le in E2.
      apply (Qle_trans _ (Qabs (arctan_partial n x - arctan_partial (Datatypes.S (Datatypes.S m)) x) +
                           Qabs (arctan_partial (Datatypes.S (Datatypes.S m)) x - arctan_partial m x)) _).
      + apply (Qle_trans _ (Qabs ((arctan_partial n x - arctan_partial (Datatypes.S (Datatypes.S m)) x) +
                                  (arctan_partial (Datatypes.S (Datatypes.S m)) x - arctan_partial m x))) _).
        * apply qeq_le.
          apply (Qabs_wd (arctan_partial n x - arctan_partial m x)
                         ((arctan_partial n x - arctan_partial (Datatypes.S (Datatypes.S m)) x) +
                          (arctan_partial (Datatypes.S (Datatypes.S m)) x - arctan_partial m x))).
          ring.
        * apply Qabs_triangle.
      + apply (Qle_trans _ (atan_mag (Datatypes.S (Datatypes.S (Datatypes.S m))) x +
                            (atan_mag (Datatypes.S m) x - atan_mag (Datatypes.S (Datatypes.S m)) x)) _).
        * apply Qplus_le_compat.
          -- apply (IH (n - Datatypes.S (Datatypes.S m))%nat).
             ++ lia.
             ++ exact Hx.
             ++ exact E2.
             ++ reflexivity.
          -- apply qeq_le.
             assert (Hpd : arctan_partial (Datatypes.S (Datatypes.S m)) x - arctan_partial m x ==
                            arctan_term (Datatypes.S m) x + arctan_term (Datatypes.S (Datatypes.S m)) x).
             { simpl. ring. }
             apply (Qeq_trans _ (Qabs (arctan_term (Datatypes.S m) x +
                                        arctan_term (Datatypes.S (Datatypes.S m)) x)) _).
             ++ apply (Qabs_wd (arctan_partial (Datatypes.S (Datatypes.S m)) x - arctan_partial m x)
                               (arctan_term (Datatypes.S m) x + arctan_term (Datatypes.S (Datatypes.S m)) x)).
                exact Hpd.
             ++ apply atan_pair_abs. exact Hx.
        * assert (Hdecr : Qle (atan_mag (Datatypes.S (Datatypes.S (Datatypes.S m))) x)
                              (atan_mag (Datatypes.S (Datatypes.S m)) x)).
          { apply atan_mag_decr. exact Hx. }
          apply (Qle_trans _ (atan_mag (Datatypes.S (Datatypes.S m)) x +
                               (atan_mag (Datatypes.S m) x - atan_mag (Datatypes.S (Datatypes.S m)) x)) _).
          -- apply Qplus_le_compat.
             ++ exact Hdecr.
             ++ apply Qle_refl.
          -- apply qeq_le. ring.
    - (* n ≤ S m：n = m 或 n = S m *)
      apply Nat.leb_gt in E2.
      assert (HnSm : (n <= Datatypes.S m)%nat) by lia.
      destruct (Nat.eq_dec m n) as [Heq | Hne].
      + (* n = m：差 0 *)
        subst n.
        assert (Hz : arctan_partial m x - arctan_partial m x == 0) by ring.
        apply (Qle_trans _ 0 _).
        * apply qeq_le.
          apply (Qabs_wd (arctan_partial m x - arctan_partial m x) 0). exact Hz.
        * apply atan_mag_nonneg.
      + (* n = S m：差 == t_{S m} *)
        assert (Hn : n = Datatypes.S m) by lia.
        subst n.
        apply qeq_le.
        assert (Ht : arctan_partial (Datatypes.S m) x - arctan_partial m x ==
                     arctan_term (Datatypes.S m) x).
        { simpl. ring. }
        apply (Qeq_trans _ (Qabs (arctan_term (Datatypes.S m) x)) _).
        * apply (Qabs_wd (arctan_partial (Datatypes.S m) x - arctan_partial m x)
                         (arctan_term (Datatypes.S m) x)). exact Ht.
        * apply arctan_term_abs.
  }
  intros m n Hx Hmn.
  apply (Hgen (n - m)%nat m n Hx Hmn). reflexivity.
Qed.
(* ================================================================== *)
(*  sT1_arctan / p_n9a_q3.v  N9a Q 层（三）：均匀尾界 + 柯西模量        *)
(*  依赖：p_n9a_q2 + CW.ConstructiveWorld                                *)
(*  内容：|x|≤1 ⟹ |S_n−S_m| ≤ 1/(2m+3)（m≤n 均匀化）；                  *)
(*        arctan_partial 的柯西模量（QltT/sigT 形，与 cauchy 谓词一致）  *)
(* ================================================================== *)

(* ---- 0 ≤ y ≤ 1 ⟹ y^p ≤ 1 ---- *)
Lemma atan_pow_le_one : forall (y : Q) (p : nat), Qle 0 y -> Qle y 1 -> Qle (q_pow y p) 1.
Proof.
  intros y p Hy0 Hy1. induction p as [| p IH]; simpl.
  - apply Qle_refl.
  - apply (Qle_trans _ (1 * q_pow y p) _).
    + apply (Qmult_le_compat_r y 1 (q_pow y p)); [exact Hy1 | apply q_pow_nonneg; exact Hy0].
    + apply (Qle_trans _ (1 * 1) _).
      * apply sc_qmult_le_l; [exact IH | exact Qle_0_1].
      * apply qeq_le. ring.
Qed.

(* ---- |x| ≤ 1 ⟹ c_{S m} ≤ 1/(2m+3)（均匀化：|x|^{2m+3} ≤ 1） ---- *)
Lemma atan_mag_le_denom : forall (x : Q) (m : nat), QleT' (Qabs x) 1 ->
  Qle (atan_mag (Datatypes.S m) x) (1 / (Z.of_nat (2 * m + 3) # 1)).
Proof.
  intros x m Hx.
  unfold atan_mag.
  replace (2 * Datatypes.S m + 1)%nat with (2 * m + 3)%nat by lia.
  apply (q_le_div_le (q_pow (Qabs x) (2 * m + 3)) (Z.of_nat (2 * m + 3) # 1)
                     1 (Z.of_nat (2 * m + 3) # 1)).
  - unfold Qlt; simpl; lia.
  - unfold Qlt; simpl; lia.
  - assert (Hp : Qle (q_pow (Qabs x) (2 * m + 3)) 1).
    { apply atan_pow_le_one; [apply Qabs_nonneg | apply QleT'_to_Qle; exact Hx]. }
    apply (Qmult_le_compat_r (q_pow (Qabs x) (2 * m + 3)) 1 (Z.of_nat (2 * m + 3) # 1)).
    + exact Hp.
    + unfold Qle; simpl; lia.
Qed.

(* ---- 均匀尾界：m ≤ n ⟹ |S_n − S_m| ≤ 1/(2m+3) ---- *)
Lemma atan_tail_bound_le : forall (x : Q) (m n : nat), QleT' (Qabs x) 1 -> (m <= n)%nat ->
  Qle (Qabs (arctan_partial n x - arctan_partial m x)) (1 / (Z.of_nat (2 * m + 3) # 1)).
Proof.
  intros x m n Hx Hmn.
  apply (Qle_trans _ (atan_mag (Datatypes.S m) x) _).
  - apply atan_tail_bound; assumption.
  - apply atan_mag_le_denom. exact Hx.
Qed.

(* ---- 1/(2m+3) ≤ 1/(N+2)（m ≥ N：分母更大 ⟹ 值更小） ---- *)
Lemma atan_inv_chain : forall (N m : nat), (N <= m)%nat ->
  Qle (1 / (Z.of_nat (2 * m + 3) # 1)) (1 / (Z.of_nat (N + 2) # 1)).
Proof.
  intros N m HNm.
  apply (Qle_trans _ (Qinv (Z.of_nat (2 * m + 3) # 1)) _).
  - apply qeq_imp_qle. unfold Qdiv. ring.
  - apply (Qle_trans _ (Qinv (Z.of_nat (N + 2) # 1)) _).
    + apply Qlt_le_weak.
      assert (Ha0 : Qlt 0 (Z.of_nat (N + 2) # 1)) by (unfold Qlt; simpl; lia).
      assert (Ha1 : Qlt 0 (Z.of_nat (2 * m + 3) # 1)) by (unfold Qlt; simpl; lia).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (N + 2) # 1) (Z.of_nat (2 * m + 3) # 1) Ha0 Ha1)).
      unfold Qlt; simpl. lia.
    + apply qeq_imp_qle. unfold Qdiv. ring.
Qed.

(* ---- 柯西模量：|x| ≤ 1 ⟹ ∀eps ∃N ∀m n ≥ N，|S_m − S_n| < eps ---- *)
Lemma arctan_partial_cauchy : forall (x : Q), QleT' (Qabs x) 1 -> forall (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall (m n : nat), NatLe N m -> NatLe N n ->
    QltT (Qabs (arctan_partial m x - arctan_partial n x)) eps).
Proof.
  intros x Hx eps Heps.
  destruct (q_arch_inv eps (QltT_to_Qlt 0 eps Heps)) as [N HN].
  exists N.
  intros m n HNm HNn.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n *)
    apply Nat.leb_le in E.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (1 / (Z.of_nat (2 * m + 3) # 1)) _).
    + apply (Qle_trans _ (Qabs (arctan_partial n x - arctan_partial m x)) _).
      * apply qeq_le. rewrite Qabs_Qminus. reflexivity.
      * apply atan_tail_bound_le. exact Hx. exact E.
    + apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1)) _).
      * apply atan_inv_chain. apply NatLe_drop in HNm. lia.
      * exact HN.
  - (* n < m *)
    apply Nat.leb_gt in E.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (1 / (Z.of_nat (2 * n + 3) # 1)) _).
    + (* |S_m − S_n| ≤ |S_n − S_m| == |S_m − S_n| ≤ 1/(2n+3)（n < m） *)
      apply (Qle_trans _ (Qabs (arctan_partial n x - arctan_partial m x)) _).
      * apply qeq_le. rewrite Qabs_Qminus. reflexivity.
      * apply (Qle_trans _ (Qabs (arctan_partial m x - arctan_partial n x)) _).
        -- apply qeq_le. rewrite Qabs_Qminus. reflexivity.
        -- apply atan_tail_bound_le. exact Hx. lia.
    + apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1)) _).
      * apply atan_inv_chain. apply NatLe_drop in HNn. lia.
      * exact HN.
Qed.
(* ================================================================== *)
(*  sT1_arctan / p_n9a_q4.v  N9a Q 层（四）：x=1 桥接 lp_odd + sanity   *)
(*  依赖：p_n9a_q2/q3 + CW.ConstructiveWorld                             *)
(*  内容：符号引理 (−1)^{2k}==1/(−1)^{2k+1}==−1；arctan_term k 1        *)
(*        == (−1)^k·lp_a k；奇数指标部分和 == lp_odd m（B3-3 锚）；     *)
(*        偶数指标版本；数值 sanity（76/105 等，纯计算核验方向）。       *)
(* ================================================================== *)

(* ---- 符号：(−1)^{2k} == 1；(−1)^{2k+1} == −1 ---- *)
Lemma atan_sign_even : forall k : nat, q_pow (-1) (2 * k) == 1.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - replace (2 * Datatypes.S k)%nat with ((2 * k) + 2)%nat by lia.
    rewrite (atan_q_pow_add (-1) (2 * k) 2).
    rewrite IH. simpl. ring.
Qed.

Lemma atan_sign_odd : forall k : nat, q_pow (-1) (2 * k + 1) == -1.
Proof.
  intro k.
  rewrite (atan_q_pow_add (-1) (2 * k) 1).
  rewrite (atan_sign_even k). simpl. ring.
Qed.

(* ---- arctan_term k 1 == (−1)^k·lp_a k ---- *)
Lemma arctan_term_one : forall k : nat, arctan_term k 1 == q_pow (-1) k * lp_a k.
Proof.
  intro k.
  unfold arctan_term, lp_a.
  setoid_rewrite (sc_q_pow_one (2 * k + 1)).
  ring.
Qed.

(* ---- 部分和两步步进：S_{S(S n)} == S_n + t_{S n} + t_{S(S n)} ---- *)
Lemma arctan_partial_step2 : forall (n : nat) (x : Q),
  arctan_partial (Datatypes.S (Datatypes.S n)) x ==
  arctan_partial n x + arctan_term (Datatypes.S n) x + arctan_term (Datatypes.S (Datatypes.S n)) x.
Proof. intros n x. simpl. ring. Qed.

(* ---- x=1 差分（奇指标 +2）：S_{2(S m)+1} − S_{2m+1} == t_{2m+2}+t_{2m+3} ---- *)
Lemma arctan_partial_diff22_one : forall (m : nat),
  arctan_partial (2 * Datatypes.S m + 1) 1 - arctan_partial (2 * m + 1) 1 ==
  arctan_term (2 * m + 2) 1 + arctan_term (2 * m + 3) 1.
Proof.
  intro m.
  replace (2 * Datatypes.S m + 1)%nat with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  rewrite (arctan_partial_step2 (2 * m + 1) 1).
  replace (2 * m + 2)%nat with (Datatypes.S (2 * m + 1)) by lia.
  replace (2 * m + 3)%nat with (Datatypes.S (Datatypes.S (2 * m + 1))) by lia.
  ring.
Qed.

(* ---- t_{2m+2} + t_{2m+3}（x=1）== lp_pair (S m) ---- *)
Lemma arctan_pair_step_one : forall (m : nat),
  arctan_term (2 * m + 2) 1 + arctan_term (2 * m + 3) 1 == lp_pair (Datatypes.S m).
Proof.
  intro m.
  rewrite (arctan_term_one (2 * m + 2)).
  rewrite (arctan_term_one (2 * m + 3)).
  replace (2 * m + 2)%nat with (2 * (m + 1))%nat by lia.
  replace (2 * m + 3)%nat with (2 * (m + 1) + 1)%nat by lia.
  rewrite (atan_sign_even (m + 1)).
  rewrite (atan_sign_odd (m + 1)).
  unfold lp_pair.
  replace (2 * Datatypes.S m)%nat with (2 * (m + 1))%nat by lia.
  replace (2 * Datatypes.S m + 1)%nat with (2 * (m + 1) + 1)%nat by lia.
  ring.
Qed.

(* ---- 奇数指标桥：S_{2m+1}(1) == lp_odd m（B3-3 锚点） ---- *)
Lemma arctan_partial_odd_one : forall (m : nat),
  arctan_partial (2 * m + 1) 1 == lp_odd m.
Proof.
  induction m as [| m IH].
  - (* m = 0：S_1 == lp_odd 0 —— 纯计算（构造性，零公理） *)
    change (arctan_term 0 1 + arctan_term 1 1 == lp_odd 0).
    vm_compute. reflexivity.
  - (* m → S m：A_{2(S m)+1} − A_{2m+1} == lp_pair (S m)，加回 A_{2m+1} *)
    assert (Hd : arctan_partial (2 * Datatypes.S m + 1) 1 - arctan_partial (2 * m + 1) 1 ==
                 lp_pair (Datatypes.S m)).
    { rewrite (arctan_partial_diff22_one m). apply arctan_pair_step_one. }
    apply (Qeq_trans _ (arctan_partial (2 * m + 1) 1 + lp_pair (Datatypes.S m)) _).
    + apply (Qeq_trans _ ((arctan_partial (2 * Datatypes.S m + 1) 1 - arctan_partial (2 * m + 1) 1) +
                          arctan_partial (2 * m + 1) 1) _).
      * ring.
      * setoid_rewrite Hd. ring.
    + rewrite IH. simpl lp_odd. reflexivity.
Qed.

(* ---- 偶数指标桥：S_{2m}(1) == lp_odd m + lp_a (2m+1) ---- *)
Lemma arctan_partial_even_one : forall (m : nat),
  arctan_partial (2 * m) 1 == lp_odd m + lp_a (2 * m + 1).
Proof.
  intro m.
  (* t_{2m+1}(1) == −lp_a(2m+1) *)
  assert (Ht : arctan_term (2 * m + 1) 1 == - lp_a (2 * m + 1)).
  { setoid_rewrite (arctan_term_one (2 * m + 1)). setoid_rewrite (atan_sign_odd m). ring. }
  (* S_{2m+1} == S_{2m} + t_{2m+1}（定义展开；不经 simpl 以免展开 ==） *)
  assert (Hdef : arctan_partial (2 * m + 1) 1 ==
                 arctan_partial (2 * m) 1 + arctan_term (2 * m + 1) 1).
  { replace (2 * m + 1)%nat with (Datatypes.S (2 * m)) by lia.
    reflexivity. }
  (* S_{2m+1} == lp_odd m ⟹ lp_odd m == S_{2m} + t_{2m+1} == S_{2m} − la *)
  assert (Hmain : lp_odd m == arctan_partial (2 * m) 1 - lp_a (2 * m + 1)).
  { apply (Qeq_trans _ (arctan_partial (2 * m + 1) 1) _).
    - apply Qeq_sym. apply arctan_partial_odd_one.
    - apply (Qeq_trans _ (arctan_partial (2 * m) 1 + arctan_term (2 * m + 1) 1) _).
      + exact Hdef.
      + apply (Qeq_trans _ (arctan_partial (2 * m) 1 + (- lp_a (2 * m + 1))) _).
        * setoid_rewrite Ht. reflexivity.
        * ring. }
  rewrite Hmain.
  ring.
Qed.

(* ==================== 数值 sanity（纯计算，构造性核验方向） ==================== *)
(* S_3(1) = 1 − 1/3 + 1/5 − 1/7 == 76/105（π/4 截断的下侧逼近 ≈ 0.724） *)
Example arctan_partial3_one_val : arctan_partial 3 1 == 76 / 105.
Proof. vm_compute. reflexivity. Qed.

(* S_4(1) = S_3 + 1/9 == 263/315（上侧 ≈ 0.835）；故 |S_4 − S_3| = 1/9 *)
Example arctan_partial4_one_val : arctan_partial 4 1 == 263 / 315.
Proof. vm_compute. reflexivity. Qed.

(* 尾界实例（x=1，m=0，n=3）：|S_3 − S_0| ≤ 1/3（纯计算核验） *)
Example atan_tail_inst1 : Qle (Qabs (arctan_partial 3 1 - arctan_partial 0 1)) (1 / 3).
Proof. vm_compute. congruence. Qed.

(* odd 桥实例：S_7(1) == lp_odd 3（1−1/3+1/5−1/7+1/9−1/11+1/13−1/15） *)
Example atan_odd_bridge_inst : arctan_partial 7 1 == lp_odd 3.
Proof.
  change (arctan_partial (2 * 3 + 1) 1 == lp_odd 3).
  apply arctan_partial_odd_one.
Qed.

(* 偶数桥实例：S_4(1) == lp_odd 2 + lp_a 5 *)
Example atan_even_bridge_inst : arctan_partial 4 1 == lp_odd 2 + lp_a 5.
Proof.
  change (arctan_partial (2 * 2) 1 == lp_odd 2 + lp_a (2 * 2 + 1)).
  apply arctan_partial_even_one.
Qed.
(* ================================================================== *)
(*  sT1_arctan / p_n9a_real.v  N9a Real 层：cauchy_real_arctan          *)
(*  依赖：p_n9a_q1..q4 + CW.ConstructiveWorld                            *)
(*  内容：                                                              *)
(*    - 三项三角 |a−c| ≤ |a−b|+|b−c|                                    *)
(*    - 幂差界 |a^{S k} − b^{S k}| ≤ (S k)·|a−b|（|a|,|b|≤1）            *)
(*    - 单项 + 固定索引 Lipschitz |ap_N a − ap_N b| ≤ (N+1)·|a−b|         *)
(*    - cauchy_real_arctan（点界 |x|≤1 前提；N0 固定索引 + eps/3）        *)
(*    - 投影恒等 arctan_real_proj                                        *)
(* ================================================================== *)

(* ---- 三项三角：|a − c| ≤ |a − b| + |b − c| ---- *)
Lemma atan_triangle3 : forall (a b c : Q),
  Qle (Qabs (a - c)) (Qabs (a - b) + Qabs (b - c)).
Proof.
  intros a b c.
  apply (Qle_trans _ (Qabs ((a - b) + (b - c))) _).
  - apply qeq_le.
    apply (Qabs_wd (a - c) ((a - b) + (b - c))). ring.
  - apply Qabs_triangle.
Qed.

(* ---- (Z.of_nat (S k) # 1) == (Z.of_nat k # 1) + 1 ---- *)
Lemma qn_succ : forall k : nat, (Z.of_nat (Datatypes.S k) # 1) == (Z.of_nat k # 1) + 1.
Proof.
  intro k. unfold Qeq. simpl. lia.
Qed.

(* ---- |a^{S k} − b^{S k}| ≤ (S k)·|a−b|（|a|,|b| ≤ 1） ---- *)
Lemma atan_pow_diff : forall (a b : Q) (k : nat),
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  Qle (Qabs (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k)))
      ((Z.of_nat (Datatypes.S k) # 1) * Qabs (a - b)).
Proof.
  intros a b k Ha Hb. induction k as [| k IH].
  - (* k = 0：|a − b| ≤ 1·|a−b| *)
    assert (Hpa : q_pow a 1 == a) by (change (a * q_pow a 0 == a); change (a * 1 == a); ring).
    assert (Hpb : q_pow b 1 == b) by (change (b * q_pow b 0 == b); change (b * 1 == b); ring).
    apply (Qle_trans _ (Qabs (a - b)) _).
    + apply qeq_le.
      apply (Qabs_wd (q_pow a 1 - q_pow b 1) (a - b)).
      setoid_rewrite Hpa. setoid_rewrite Hpb. reflexivity.
    + assert (Hone : (Z.of_nat 1 # 1) == 1) by (unfold Qeq; simpl; lia).
      replace (Z.of_nat (Datatypes.S 0) # 1) with (Z.of_nat 1 # 1) by reflexivity.
      rewrite Hone.
      apply qeq_imp_qle. ring.
  - (* k → S k *)
    assert (Hstep : q_pow a (Datatypes.S (Datatypes.S k)) - q_pow b (Datatypes.S (Datatypes.S k)) ==
                    (a * (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k))) +
                    ((a - b) * q_pow b (Datatypes.S k))).
    { rewrite (q_pow_succ a (Datatypes.S k)).
      rewrite (q_pow_succ b (Datatypes.S k)). ring. }
    apply (Qle_trans _ (Qabs (a * (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k))) +
                         Qabs ((a - b) * q_pow b (Datatypes.S k))) _).
    + apply (Qle_trans _ (Qabs ((a * (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k))) +
                                ((a - b) * q_pow b (Datatypes.S k)))) _).
      * apply qeq_le. apply (Qabs_wd _ _). exact Hstep.
      * apply Qabs_triangle.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * Qabs (a - b) +
                          Qabs (a - b)) _).
      * apply Qplus_le_compat.
        -- (* |a·(A−B)| ≤ 1·(Sk·|Δ|) *)
           apply (Qle_trans _ (Qabs a * Qabs (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k))) _).
           ++ apply qeq_le. apply Qabs_Qmult.
           ++ apply (Qle_trans _ (1 * ((Z.of_nat (Datatypes.S k) # 1) * Qabs (a - b))) _).
              ** apply (Qle_trans _ (1 * Qabs (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k))) _).
                 --- apply (Qmult_le_compat_r (Qabs a) 1 (Qabs (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k)))).
                     ---- apply QleT'_to_Qle. exact Ha.
                     ---- apply Qabs_nonneg.
                 --- apply (sc_qmult_le_l (Qabs (q_pow a (Datatypes.S k) - q_pow b (Datatypes.S k)))
                                          ((Z.of_nat (Datatypes.S k) # 1) * Qabs (a - b)) 1).
                     ---- exact IH.
                     ---- exact Qle_0_1.
              ** apply qeq_imp_qle. ring.
        -- (* |(a−b)·B| ≤ |a−b|（|B| ≤ 1） *)
           apply (Qle_trans _ (Qabs (a - b) * Qabs (q_pow b (Datatypes.S k))) _).
           ++ apply qeq_le. apply Qabs_Qmult.
           ++ apply (Qle_trans _ (Qabs (a - b) * 1) _).
              ** apply (sc_qmult_le_l (Qabs (q_pow b (Datatypes.S k))) 1 (Qabs (a - b))).
                 --- apply (Qle_trans _ (q_pow (Qabs b) (Datatypes.S k)) _).
                     ---- apply qeq_imp_qle. apply q_pow_abs.
                     ---- apply atan_pow_le_one; [apply Qabs_nonneg | apply QleT'_to_Qle; exact Hb].
                 --- apply Qabs_nonneg.
              ** apply qeq_imp_qle. ring.
      * apply qeq_imp_qle.
        assert (Hsucc : (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) ==
                        (Z.of_nat (Datatypes.S k) # 1) + 1).
        { apply qn_succ. }
        rewrite Hsucc. ring.
Qed.
(* ---- 单项 Lipschitz：|t_k a − t_k b| ≤ |a − b|（|a|,|b| ≤ 1） ---- *)
Lemma atan_term_lipschitz : forall (k : nat) (a b : Q),
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  Qle (Qabs (arctan_term k a - arctan_term k b)) (Qabs (a - b)).
Proof.
  intros k a b Ha Hb.
  unfold arctan_term, Qdiv.
  assert (Hal : q_pow (-1) k * (q_pow a (2 * k + 1) * Qinv (Z.of_nat (2 * k + 1) # 1)) -
                q_pow (-1) k * (q_pow b (2 * k + 1) * Qinv (Z.of_nat (2 * k + 1) # 1)) ==
                q_pow (-1) k * ((q_pow a (2 * k + 1) - q_pow b (2 * k + 1)) *
                                Qinv (Z.of_nat (2 * k + 1) # 1))).
  { ring. }
  apply (Qle_trans _ (Qabs (q_pow (-1) k * ((q_pow a (2 * k + 1) - q_pow b (2 * k + 1)) *
                                            Qinv (Z.of_nat (2 * k + 1) # 1)))) _).
  - apply qeq_le. apply (Qabs_wd _ _). exact Hal.
  - (* |s·X| == |X| ≤ |Δ|（|s| == 1） *)
    apply (Qle_trans _ (Qabs ((q_pow a (2 * k + 1) - q_pow b (2 * k + 1)) *
                              Qinv (Z.of_nat (2 * k + 1) # 1))) _).
    + apply qeq_imp_qle.
      apply (Qeq_trans _ (Qabs (q_pow (-1) k) *
                          Qabs ((q_pow a (2 * k + 1) - q_pow b (2 * k + 1)) *
                                Qinv (Z.of_nat (2 * k + 1) # 1))) _).
      * apply Qabs_Qmult.
      * setoid_rewrite (sc_abs_sign k). ring.
    + apply (Qle_trans _ (Qabs (q_pow a (2 * k + 1) - q_pow b (2 * k + 1)) *
                          Qabs (Qinv (Z.of_nat (2 * k + 1) # 1))) _).
      * apply qeq_le. apply Qabs_Qmult.
      * assert (Hpd := atan_pow_diff a b (2 * k) Ha Hb).
        apply (Qle_trans _ (((Z.of_nat (2 * k + 1) # 1) * Qabs (a - b)) *
                            Qabs (Qinv (Z.of_nat (2 * k + 1) # 1))) _).
        -- apply (Qmult_le_compat_r (Qabs (q_pow a (2 * k + 1) - q_pow b (2 * k + 1)))
                                   ((Z.of_nat (2 * k + 1) # 1) * Qabs (a - b))
                                   (Qabs (Qinv (Z.of_nat (2 * k + 1) # 1)))).
           ++ (* |A−B| ≤ (2k+1)#1·|Δ|（Hpd 索引形变） *)
              apply (Qle_trans _ (Qabs (q_pow a (Datatypes.S (2 * k)) - q_pow b (Datatypes.S (2 * k)))) _).
              ** apply qeq_imp_qle.
                 apply (Qabs_wd (q_pow a (2 * k + 1) - q_pow b (2 * k + 1))
                                (q_pow a (Datatypes.S (2 * k)) - q_pow b (Datatypes.S (2 * k)))).
                 replace (2 * k + 1)%nat with (Datatypes.S (2 * k)) by lia.
                 reflexivity.
              ** replace (Z.of_nat (2 * k + 1) # 1) with (Z.of_nat (Datatypes.S (2 * k)) # 1) by (f_equal; lia).
                 exact Hpd.
           ++ apply Qabs_nonneg.
        -- (* ((2k+1)#1·|Δ|)·|/d| == |Δ| *)
           apply qeq_imp_qle.
           assert (Habsd : Qabs (Qinv (Z.of_nat (2 * k + 1) # 1)) == Qinv (Z.of_nat (2 * k + 1) # 1)).
           { apply Qabs_pos.
             apply (Qlt_le_weak 0 (Qinv (Z.of_nat (2 * k + 1) # 1))).
             apply Qinv_lt_0_compat. apply atan_odd_pos. }
           rewrite Habsd.
           assert (Hinv : (Z.of_nat (2 * k + 1) # 1) * Qinv (Z.of_nat (2 * k + 1) # 1) == 1).
           { apply Qmult_inv_r. apply (q_neq_of_lt (Z.of_nat (2 * k + 1) # 1)). apply atan_odd_pos. }
           apply (Qeq_trans _ (Qabs (a - b) *
                               ((Z.of_nat (2 * k + 1) # 1) * Qinv (Z.of_nat (2 * k + 1) # 1))) _).
           ++ ring.
           ++ rewrite Hinv. ring.
Qed.

(* ---- 固定索引 Lipschitz：|ap_N a − ap_N b| ≤ (N+1)·|a−b| ---- *)
Lemma arctan_partial_lipschitz : forall (N : nat) (a b : Q),
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  Qle (Qabs (arctan_partial N a - arctan_partial N b))
      ((Z.of_nat (Datatypes.S N) # 1) * Qabs (a - b)).
Proof.
  intros N. induction N as [| N IH].
  - (* N = 0 *)
    intros a b Ha Hb.
    apply (Qle_trans _ (Qabs (a - b)) _).
    + apply (atan_term_lipschitz 0 a b Ha Hb).
    + assert (Hone : (Z.of_nat 1 # 1) == 1) by (unfold Qeq; simpl; lia).
      replace (Z.of_nat (Datatypes.S 0) # 1) with (Z.of_nat 1 # 1) by reflexivity.
      rewrite Hone.
      apply qeq_imp_qle. ring.
  - (* N → S N *)
    intros a b Ha Hb.
    assert (Hstep : arctan_partial (Datatypes.S N) a - arctan_partial (Datatypes.S N) b ==
                    (arctan_partial N a - arctan_partial N b) +
                    (arctan_term (Datatypes.S N) a - arctan_term (Datatypes.S N) b)).
    { change (arctan_partial N a + arctan_term (Datatypes.S N) a -
              (arctan_partial N b + arctan_term (Datatypes.S N) b) ==
              (arctan_partial N a - arctan_partial N b) +
              (arctan_term (Datatypes.S N) a - arctan_term (Datatypes.S N) b)).
      ring. }
    apply (Qle_trans _ (Qabs (arctan_partial N a - arctan_partial N b) +
                         Qabs (arctan_term (Datatypes.S N) a - arctan_term (Datatypes.S N) b)) _).
    + apply (Qle_trans _ (Qabs ((arctan_partial N a - arctan_partial N b) +
                                (arctan_term (Datatypes.S N) a - arctan_term (Datatypes.S N) b))) _).
      * apply qeq_le. apply (Qabs_wd _ _). exact Hstep.
      * apply Qabs_triangle.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S N) # 1) * Qabs (a - b) + Qabs (a - b)) _).
      * apply Qplus_le_compat.
        -- apply IH; assumption.
        -- apply (atan_term_lipschitz (Datatypes.S N) a b Ha Hb).
      * apply qeq_imp_qle.
        assert (Hsucc : (Z.of_nat (Datatypes.S (Datatypes.S N)) # 1) ==
                        (Z.of_nat (Datatypes.S N) # 1) + 1).
        { apply qn_succ. }
        rewrite Hsucc. ring.
Qed.

(* ---- eps/3 拆分恒等 ---- *)
Lemma atan_third_sum : forall eps : Q, eps / 3 + (eps / 3 + eps / 3) == eps.
Proof.
  intro eps. unfold Qdiv. field.
Qed.

(* ---- cauchy_real_arctan：|x| ≤ 1（逐点）上的 arctan 级数柯西实值 ---- *)
Definition cauchy_real_arctan (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real.
Proof.
  set (u := projT1 x).
  assert (Hu : cauchy u) by (unfold u; apply (projT2 x)).
  assert (Hxu : forall n : nat, QleT' (Qabs (u n)) 1) by (intro n; unfold u; apply Hx).
  exists (fun n : nat => arctan_partial n (u n)).
  intros eps Heps.
  (* 1. 尾阈值 N0：1/(N0+2) < eps/3 *)
  assert (Heps3 : Qlt 0 (eps / 3)).
  { apply QltT_to_Qlt. apply (qltT_div_pos eps 3 Heps qltT_0_3). }
  destruct (q_arch_inv (eps / 3) Heps3) as [N0 HN0].
  (* 2. 参数模阈值：Hu at eps/(3·(N0+1)) *)
  set (L := Z.of_nat (Datatypes.S N0) # 1).
  assert (HLpos : Qlt 0 L).
  { unfold L. unfold Qlt. simpl. lia. }
  assert (HepsL : QltT 0 (eps / (3 * L))).
  { apply (qltT_div_pos eps (3 * L)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 3 L).
      + exact qltT_0_3.
      + apply Qlt_to_QltT. exact HLpos. }
  destruct (Hu (eps / (3 * L)) HepsL) as [N1 HN1].
  exists (Nat.max N0 N1).
  intros m n Hm Hn.
  apply Qlt_to_QltT.
  assert (Hm0 : (N0 <= m)%nat) by (apply NatLe_drop in Hm; lia).
  assert (Hn0 : (N0 <= n)%nat) by (apply NatLe_drop in Hn; lia).
  (* 3. 主链：|S_m(um) − S_n(un)| ≤ t1 + (mid + t2)；t1,t2 尾 ≤ B1；mid ≤ B2 *)
  set (B1 := 1 / (Z.of_nat (2 * N0 + 3) # 1)).
  apply (Qle_lt_trans _ (B1 + (L * Qabs (u m - u n) + B1)) _).
  - (* 三角 + 分块界 *)
    set (A := arctan_partial m (u m)).
    set (B := arctan_partial N0 (u m)).
    set (C := arctan_partial N0 (u n)).
    set (D := arctan_partial n (u n)).
    apply (Qle_trans _ (Qabs (A - B) + (Qabs (B - C) + Qabs (C - D))) _).
    + (* 两次三角 *)
      apply (Qle_trans _ (Qabs (A - B) + Qabs (B - D)) _).
      * apply (atan_triangle3 A B D).
      * apply Qplus_le_compat; [apply Qle_refl | apply (atan_triangle3 B C D)].
    + (* 分块界：t1 ≤ B1；mid ≤ L·|Δu|；t2 ≤ B1 *)
      apply Qplus_le_compat.
      * unfold A, B, B1.
        apply atan_tail_bound_le. exact (Hxu m). exact Hm0.
      * apply Qplus_le_compat.
        -- unfold B, C, L.
           apply (arctan_partial_lipschitz N0 (u m) (u n)); [apply Hxu | apply Hxu].
        -- unfold C, D, B1.
           apply (Qle_trans _ (Qabs (arctan_partial n (u n) - arctan_partial N0 (u n))) _).
           ++ apply qeq_le. rewrite Qabs_Qminus. reflexivity.
           ++ apply atan_tail_bound_le. exact (Hxu n). exact Hn0.
  - (* B1 + (L|Δ| + B1) < eps：每块 < eps/3 *)
    assert (Ht1 : Qlt B1 (eps / 3)).
    { unfold B1.
      apply (Qle_lt_trans _ (1 / (Z.of_nat (N0 + 2) # 1)) _).
      - apply atan_inv_chain. lia.
      - exact HN0. }
    assert (Ht2 : Qlt (L * Qabs (u m - u n)) (eps / 3)).
    { (* L·|Δ| == |Δ|·L < (eps/(3L))·L ≤ == eps/3 *)
      apply (Qlt_le_trans _ ((eps / (3 * L)) * L) _).
      - (* |Δ|·L < (eps/(3L))·L：L·|Δ| ≤ |Δ|·L（==），再 ×L 严格 *)
        apply (Qle_lt_trans _ (Qabs (u m - u n) * L) _).
        + (* L·|Δ| ≤ |Δ|·L：== *)
          apply qeq_imp_qle. ring.
        + (* |Δ|·L < (eps/(3L))·L：HN1 乘 L *)
          apply (Qmult_lt_compat_r (Qabs (u m - u n)) (eps / (3 * L)) L).
          * exact HLpos.
          * apply QltT_to_Qlt.
            apply (HN1 m n).
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N0 N1) _); [lia | apply NatLe_drop in Hm; lia].
            -- apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N0 N1) _); [lia | apply NatLe_drop in Hn; lia].
      - (* (eps/(3L))·L ≤ eps/3：== 恒等 *)
        apply qeq_imp_qle.
        unfold Qdiv. field.
        intro Hz. apply (q_neq_of_lt L).
        exact HLpos.
        exact Hz. }
    apply (Qlt_le_trans _ (eps / 3 + (eps / 3 + eps / 3)) _).
    + apply Qplus_lt_compat.
      * exact Ht1.
      * apply Qplus_lt_compat; [exact Ht2 | exact Ht1].
    + apply qeq_imp_qle. apply atan_third_sum.
Defined.

(* ---- 投影恒等 ---- *)
Lemma arctan_real_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  projT1 (cauchy_real_arctan x Hx) n == arctan_partial n (projT1 x n).
Proof.
  intros x Hx n. reflexivity.
Qed.

(* ============================================================ *)
(* SC-2 批（并入 204）：T-pi3 A2/B3-2 tan-arctan 完结链（sT2）  *)
(* real_tan + arctan(1) 域正性 + tan==1<->sin==cos 桥 + 倍角    *)
(* + N10->F1 完结装配（H4/Hsc 两解析输入 Section 化）            *)
(* ============================================================ *)

(* ================================================================== *)
(*  sT2_tan / p_tan_def.v   N9b 核心一：Real 层 tan 定义 + 代数桥     *)
(*  依赖：CW.ConstructiveWorld（迭代 203：N9a 已并入，rs_add_cos 在） *)
(*  内容：                                                             *)
(*    - real_tan w Hw := sin w · inv_pos(cos w) Hw（cos w > 0 域）     *)
(*    - tan w · cos w == sin w                                        *)
(*    - tan w == 1 ⟺ sin w == cos w（同一 cos w > 0 域内的双向桥）      *)
(*    - 倍角：sin X == cos X ⟹ cos(X+X) == 0（rs_add_cos 实例化）      *)
(* ================================================================== *)


(* ---- tan 定义：sin w · inv(cos w)，域 cos w > 0 ---- *)
Definition real_tan (w : Real) (Hw : real_lt real_zero (cauchy_real_cos w)) : Real :=
  real_mult (cauchy_real_sin w) (real_inv_pos (cauchy_real_cos w) Hw).

(* ---- 引理 A：tan w · cos w == sin w ---- *)
Lemma real_tan_mult_cos : forall (w : Real) (Hw : real_lt real_zero (cauchy_real_cos w)),
  real_eq (real_mult (real_tan w Hw) (cauchy_real_cos w)) (cauchy_real_sin w).
Proof.
  intros w Hw.
  unfold real_tan.
  (* (sin·inv c)·c == sin·(inv c·c) == sin·1 == sin *)
  apply (real_eq_trans _ (real_mult (cauchy_real_sin w)
                             (real_mult (real_inv_pos (cauchy_real_cos w) Hw) (cauchy_real_cos w))) _).
  - apply real_eq_sym. exact (real_mult_assoc (cauchy_real_sin w)
                                (real_inv_pos (cauchy_real_cos w) Hw) (cauchy_real_cos w)).
  - apply (real_eq_trans _ (real_mult (cauchy_real_sin w) real_one) _).
    + apply (RealSetoid.real_eq_mult_compat (cauchy_real_sin w)
               (real_mult (real_inv_pos (cauchy_real_cos w) Hw) (cauchy_real_cos w))
               (cauchy_real_sin w) real_one).
      * apply real_eq_refl.
      * (* inv c · c == 1：inv c · c == c · inv c == 1（comm + inv_correct） *)
        apply (real_eq_trans _ (real_mult (cauchy_real_cos w) (real_inv_pos (cauchy_real_cos w) Hw)) _).
        -- apply real_mult_comm.
        -- exact (real_inv_pos_correct (cauchy_real_cos w) Hw).
    + exact (real_mult_one (cauchy_real_sin w)).
Qed.

(* ---- 引理 B1：tan w == 1 ⟹ sin w == cos w ---- *)
Lemma real_tan_eq_one_sin_eq_cos : forall (w : Real) (Hw : real_lt real_zero (cauchy_real_cos w)),
  real_eq (real_tan w Hw) real_one ->
  real_eq (cauchy_real_sin w) (cauchy_real_cos w).
Proof.
  intros w Hw Htan.
  (* sin == tan·cos == 1·cos == cos *)
  apply (real_eq_trans _ (real_mult (real_tan w Hw) (cauchy_real_cos w)) _).
  - apply real_eq_sym. exact (real_tan_mult_cos w Hw).
  - apply (real_eq_trans _ (real_mult real_one (cauchy_real_cos w)) _).
    + apply (RealSetoid.real_eq_mult_compat (real_tan w Hw) (cauchy_real_cos w)
                                            real_one (cauchy_real_cos w)).
      * exact Htan.
      * apply real_eq_refl.
    + (* 1·c == c·1 == c *)
      apply (real_eq_trans _ (real_mult (cauchy_real_cos w) real_one) _).
      * apply real_mult_comm.
      * exact (real_mult_one (cauchy_real_cos w)).
Qed.

(* ---- 引理 B2：sin w == cos w ⟹ tan w == 1（cos w > 0 域） ---- *)
Lemma real_sin_eq_cos_tan_eq_one : forall (w : Real) (Hw : real_lt real_zero (cauchy_real_cos w)),
  real_eq (cauchy_real_sin w) (cauchy_real_cos w) ->
  real_eq (real_tan w Hw) real_one.
Proof.
  intros w Hw Hsc.
  (* tan == sin·inv c == c·inv c == 1 *)
  apply (real_eq_trans _ (real_mult (cauchy_real_cos w) (real_inv_pos (cauchy_real_cos w) Hw)) _).
  - apply (RealSetoid.real_eq_mult_compat (cauchy_real_sin w) (real_inv_pos (cauchy_real_cos w) Hw)
                                          (cauchy_real_cos w) (real_inv_pos (cauchy_real_cos w) Hw)).
    + exact Hsc.
    + apply real_eq_refl.
  - exact (real_inv_pos_correct (cauchy_real_cos w) Hw).
Qed.

(* ---- 倍角通道：sin X == cos X ⟹ cos(X+X) == 0（rs_add_cos 实例化） ---- *)
(* 路线：rs_add_cos X X：cos(X+X) == cosX·cosX − sinX·sinX；
   sinX==cosX ⟹ sin²X == cos²X（real_eq compat）⟹ cos² − sin² == 0（real_plus_opp）。 *)

(* ---- 引理 C 辅助：A == B ⟹ A + (−B) == 0（real_eq 层，eps 语义） ---- *)
Lemma real_sq_eq_sq_diff_zero : forall (A B : Real),
  real_eq A B -> real_eq (real_plus A (real_opp B)) real_zero.
Proof.
  intros A B Hab.
  apply (real_eq_trans _ (real_plus B (real_opp B)) _).
  - apply (RealSetoid.real_eq_plus_compat A (real_opp B) B (real_opp B)).
    + exact Hab.
    + apply real_eq_refl.
  - exact (real_plus_opp B).
Qed.

(* ---- 引理 C（最终形式）：sin X == cos X ⟹ cos(X+X) == 0 ---- *)
Lemma real_sin_eq_cos_cos_double_zero : forall (X : Real),
  real_eq (cauchy_real_sin X) (cauchy_real_cos X) ->
  real_eq (cauchy_real_cos (real_plus X X)) real_zero.
Proof.
  intros X Hsc.
  assert (Hsq : real_eq (real_mult (cauchy_real_sin X) (cauchy_real_sin X))
                        (real_mult (cauchy_real_cos X) (cauchy_real_cos X))).
  { apply (RealSetoid.real_eq_mult_compat (cauchy_real_sin X) (cauchy_real_sin X)
                                          (cauchy_real_cos X) (cauchy_real_cos X)).
    - exact Hsc.
    - exact Hsc. }
  assert (Hdiff : real_eq (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                                     (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X))))
                          real_zero).
  { (* cos² − sin² == 0：cos² − sin² == (sin² + (−sin²)) 代入 Hsq → 0 *)
    apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_sin X))
                                      (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
               (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))
               (real_mult (cauchy_real_sin X) (cauchy_real_sin X))
               (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))).
      + apply real_eq_sym. exact Hsq.
      + apply real_eq_refl.
    - exact (real_plus_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X))). }
  (* cos(X+X) == cos²−sin² == 0 *)
  apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                                    (real_opp (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))) _).
  - apply (rs_add_cos X X).
  - exact Hdiff.
Qed.

(* ---- 2·X == X + X（Real 层 ring 桥，供 2·arctan(1) == w_leibniz 侧用） ---- *)
Lemma real_two_mult_plus : forall (X : Real),
  real_eq (real_mult (real_const 2) X) (real_plus X X).
Proof.
  intro X.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_mult_proj (real_const 2) X n).
  rewrite (real_const_proj 2 n).
  rewrite !(real_plus_proj X X n).
  ring.
Qed.

(* ---- 倍角通道（2X 形态）：sin X == cos X ⟹ cos(2·X) == 0 ---- *)
Lemma real_sin_eq_cos_cos_two_zero : forall (X : Real),
  real_eq (cauchy_real_sin X) (cauchy_real_cos X) ->
  real_eq (cauchy_real_cos (real_mult (real_const 2) X)) real_zero.
Proof.
  intros X Hsc.
  apply (real_eq_trans _ (cauchy_real_cos (real_plus X X)) _).
  - apply real_cos_eq_compat.
    exact (real_two_mult_plus X).
  - exact (real_sin_eq_cos_cos_double_zero X Hsc).
Qed.
(* ================================================================== *)
(*  sT2_tan / p_atan1_bounds.v   N9b 核心二：arctan(1) 域正性         *)
(*  依赖：CW.ConstructiveWorld（迭代 203）+ 先行件 p_tan_def.v           *)
(*  内容：                                                             *)
(*    - θ := cauchy_real_arctan (real_const 1) Hone（x=1 处的 arctan） *)
(*    - 点态界 |S_n(1) − S_0(1)| ≤ 1/3（atan_tail_bound m=0）          *)
(*    - Real 层括号：0 < θ 且 θ < 3/2（cos/sin 正性引理的前提）        *)
(*    - cos(θ) > 0（经 cos 在 (0,3/2) 上沿 real_cos_strict_decr）       *)
(*    - sin(θ) > 0（real_sin_pos_lt_two，0 < θ < 2）                   *)
(*  即 N9b 需要的「cos w > 0 域」在 w := arctan(1) 处成立。            *)
(* ================================================================== *)


(* 逐点 |1| ≤ 1：cauchy_real_arctan (real_const 1) 的前提 *)
Lemma atan1_pt_bound : forall n : nat, QleT' (Qabs (projT1 (real_const 1) n)) 1.
Proof.
  intro n.
  apply Qle_to_QleT'.
  (* |projT1 (real_const 1) n| == |1| == 1 ≤ 1 *)
  apply (Qle_trans _ (Qabs 1) _).
  - apply qeq_imp_qle.
    apply (Qabs_wd (projT1 (real_const 1) n) 1).
    apply real_const_proj.
  - apply qeq_imp_qle.
    unfold Qabs. reflexivity.
Qed.

(* θ := arctan(1)（x=1 处的 arctan 级数实值） *)
Definition arctan_one_real : Real := cauchy_real_arctan (real_const 1) atan1_pt_bound.

(* 投影：projT1 θ n == arctan_partial n 1 *)
Lemma arctan_one_proj : forall n : nat, projT1 arctan_one_real n == arctan_partial n 1.
Proof.
  intro n.
  unfold arctan_one_real.
  rewrite (arctan_real_proj (real_const 1) atan1_pt_bound n).
  (* projT1 (real_const 1) n 定义为 1（逐点常序列） *)
  cbn [projT1].
  reflexivity.
Qed.

(* ---- 点态界：|S_n(1) − S_0(1)| ≤ 1/3（atan_tail_bound @ x=1, m=0） ---- *)
Lemma q_abs_one_le_one : QleT' (Qabs 1) 1.
Proof.
  apply Qle_to_QleT'.
  apply (Qle_trans _ 1 _).
  - apply qeq_imp_qle. apply Qabs_pos. unfold Qle; simpl; lia.
  - apply Qle_refl.
Qed.

Lemma atan1_pt_diff_le_third : forall n : nat,
  Qle (Qabs (arctan_partial n 1 - arctan_partial 0 1)) (1 / 3).
Proof.
  intro n.
  apply (Qle_trans _ (atan_mag 1 1) _).
  - apply (atan_tail_bound 1 0 n q_abs_one_le_one). lia.
  - unfold atan_mag.
    change (Qle (q_pow (Qabs 1) 3 / (Z.of_nat 3 # 1)) (1 / 3)).
    unfold Qabs, Qdiv, Qinv.
    change (Qle (1 * 1 * 1 * / 3) (1 * / 3)).
    unfold Qle; simpl. lia.
Qed.

(* S_0(1) == 1 *)
Lemma atan1_S0 : arctan_partial 0 1 == 1.
Proof.
  reflexivity.
Qed.

(* 直接形态：|S_n(1) − 1| ≤ 1/3（S_0(1) == 1 代入） *)
Lemma atan1_pt_abs_minus_one_le_third : forall n : nat,
  Qle (Qabs (arctan_partial n 1 - 1)) (1 / 3).
Proof.
  intro n.
  apply (Qle_trans _ (Qabs (arctan_partial n 1 - arctan_partial 0 1)) _).
  - apply qeq_imp_qle.
    apply (Qabs_wd (arctan_partial n 1 - 1) (arctan_partial n 1 - arctan_partial 0 1)).
    assert (Hd : arctan_partial n 1 - arctan_partial 0 1 == arctan_partial n 1 - 1).
    { setoid_rewrite atan1_S0. apply Qeq_refl. }
    apply Qeq_sym. exact Hd.
  - exact (atan1_pt_diff_le_third n).
Qed.

(* 点态上界：S_n(1) ≤ 4/3 < 3/2 *)
Lemma atan1_pt_le_four_thirds : forall n : nat, Qle (arctan_partial n 1) (4 / 3).
Proof.
  intro n.
  apply (Qle_trans _ ((arctan_partial n 1 - 1) + 1) _).
  - apply qeq_imp_qle. ring.
  - apply (Qle_trans _ (Qabs (arctan_partial n 1 - 1) + 1) _).
    + apply Qplus_le_compat; [apply Qle_Qabs | apply Qle_refl].
    + apply (Qle_trans _ (1 / 3 + 1) _).
      * apply Qplus_le_compat; [exact (atan1_pt_abs_minus_one_le_third n) | apply Qle_refl].
      * change (Qle (1 / 3 + 1) (4 / 3)). unfold Qle; simpl. lia.
Qed.

(* 点态下界：S_n(1) ≥ 2/3（|S_n−1| ≤ 1/3 ⟹ −1/3 ≤ S_n−1 ⟹ 1−1/3 ≤ 1+(S_n−1) == S_n） *)
Lemma atan1_pt_ge_two_thirds : forall n : nat, Qle (2 / 3) (arctan_partial n 1).
Proof.
  intro n.
  destruct (proj1 (Qabs_Qle_condition (arctan_partial n 1 - 1) (1 / 3))
                 (atan1_pt_abs_minus_one_le_third n)) as [Hlo Hhi].
  (* 2/3 ≤ 1 + (S_n − 1) == S_n *)
  apply (Qle_trans _ (1 + (arctan_partial n 1 - 1)) _).
  - (* 2/3 ≤ 1 + (S_n − 1)：2/3 == 1 + (−1/3) ≤ 1 + (S_n − 1) *)
    apply (Qle_trans _ (1 + - (1 / 3)) _).
    + apply qeq_imp_qle. field.
    + apply Qplus_le_compat; [apply Qle_refl | exact Hlo].
  - apply qeq_imp_qle. ring.
Qed.

(* ============ Real 层括号 1：0 < θ ============ *)
Lemma real_lt_zero_arctan_one : real_lt real_zero arctan_one_real.
Proof.
  unfold real_lt.
  exists (1 / 2).
  split.
  - apply Qlt_to_QltT. change (Qlt 0 (1 / 2)). compute. reflexivity.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    (* projT1 arctan_one_real n − 0 == arctan_partial n 1（投影代入 + ring） *)
    assert (Hproj : projT1 arctan_one_real n - 0 == arctan_partial n 1).
    { rewrite (arctan_one_proj n). ring. }
    rewrite Hproj.
    apply (Qlt_le_trans (1 / 2) (2 / 3) (arctan_partial n 1)).
    + change (Qlt (1 / 2) (2 / 3)). compute. reflexivity.
    + exact (atan1_pt_ge_two_thirds n).
Qed.

(* ============ Real 层括号 2：θ < 3/2 ============ *)
Lemma real_lt_arctan_one_three_halves : real_lt arctan_one_real (real_const (3 / 2)).
Proof.
  unfold real_lt.
  exists (1 / 12).
  split.
  - apply Qlt_to_QltT. change (Qlt 0 (1 / 12)). compute. reflexivity.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    (* 目标 Qlt (1/12) (3/2 − projT1 arctan_one_real n)；投影代入 *)
    assert (Hproj : projT1 (real_const (3 / 2)) n - projT1 arctan_one_real n ==
                    3 / 2 - arctan_partial n 1).
    { rewrite (real_const_proj (3 / 2) n). rewrite (arctan_one_proj n). ring. }
    rewrite Hproj.
    apply (Qlt_le_trans (1 / 12) (1 / 6) (3 / 2 - arctan_partial n 1)).
    + change (Qlt (1 / 12) (1 / 6)). compute. reflexivity.
    + (* 1/6 ≤ 3/2 − S_n ⟺ 0 ≤ (3/2−S_n) − 1/6 == 4/3 − S_n（S_n ≤ 4/3） *)
      apply (proj2 (Qle_minus_iff (1 / 6) (3 / 2 - arctan_partial n 1))).
      assert (Hc : (3 / 2 - arctan_partial n 1) - 1 / 6 == 4 / 3 - arctan_partial n 1) by field.
      rewrite Hc.
      apply (proj1 (Qle_minus_iff (arctan_partial n 1) (4 / 3))).
      exact (atan1_pt_le_four_thirds n).
Qed.

(* θ < 2（real_sin_pos_lt_two 前提：θ < 3/2 < 2） *)
Lemma real_lt_arctan_one_two : real_lt arctan_one_real (real_const 2).
Proof.
  apply (real_lt_trans _ (real_const (3 / 2)) _).
  - exact real_lt_arctan_one_three_halves.
  - apply real_const_lt. change (Qlt (3 / 2) 2). compute. reflexivity.
Qed.

(* ============ cos(θ) > 0 ============ *)
(* 路线：0 < θ < 3/2 < 2 且 cos 在 (0,2) 严格递减 ⟹ cos(3/2) < cos(θ)；
   cos(3/2) > 0（real_cos_three_halves_pos）⟹ 0 < cos(3/2) < cos(θ)。 *)
Lemma real_cos_arctan_one_pos : real_lt real_zero (cauchy_real_cos arctan_one_real).
Proof.
  apply (real_lt_trans _ (cauchy_real_cos (real_const (3 / 2))) _).
  - (* 0 < cos(3/2) *)
    exact real_cos_three_halves_pos.
  - (* cos(3/2) < cos(θ)：real_cos_strict_decr X:=θ Y:=3/2（0<θ<3/2<2） *)
    apply (real_cos_strict_decr arctan_one_real (real_const (3 / 2))).
    + exact real_lt_zero_arctan_one.
    + exact real_lt_arctan_one_three_halves.
    + apply real_const_lt. change (Qlt (3 / 2) 2). compute. reflexivity.
Qed.

(* ============ sin(θ) > 0 ============ *)
Lemma real_sin_arctan_one_pos : real_lt real_zero (cauchy_real_sin arctan_one_real).
Proof.
  apply (real_sin_pos_lt_two arctan_one_real).
  - exact real_lt_zero_arctan_one.
  - exact real_lt_arctan_one_two.
Qed.

(* ============ 顺带：θ 本身（arctan 值）在 (0, 3/2) —— 数值 sanity 用 ============ *)
(* 0 < θ 且 θ < 3/2 已证。另给 2/3 下括号的 Real 版本（可选，不强制）。 *)

(* ============ tan(arctan(1)) 良定义（域 cos θ > 0） ============ *)
Definition arctan_one_tan : Real := real_tan arctan_one_real real_cos_arctan_one_pos.

(* 检查：sin(θ)·inv(cos θ) 形态 == real_tan θ Hcos（unfold 即恒等） *)
Lemma arctan_one_tan_unfold :
  real_eq arctan_one_tan
          (real_mult (cauchy_real_sin arctan_one_real)
                     (real_inv_pos (cauchy_real_cos arctan_one_real) real_cos_arctan_one_pos)).
Proof.
  unfold arctan_one_tan, real_tan. apply real_eq_refl.
Qed.
(* ================================================================== *)
(*  sT2_tan / p_n10_channel.v   N9b 完结通道：B4（N10）装配骨架        *)
(*  依赖：p_tan_def.v + p_atan1_bounds.v + CW.ConstructiveWorld        *)
(*  内容：证明 B4/N10（cos(w_leibniz)==0 ⟹ F1）的每一步 glue 都是真证， *)
(*  仅保留两个解析输入为 Section 变量（合法：零公理面）：              *)
(*    - H4 : 4·arctan(1) == π_L（B3-3 值桥；A3 批纯级数可证）          *)
(*    - Hsc : sin(arctan(1)) == cos(arctan(1))                        *)
(*        （= tan(arctan(1)) == 1 经 real_tan B1/B2 桥；               *)
(*          需 arctan'(x)==1/(1+x²) 级数微商塔 —— 后补/多轮块）        *)
(*  = 一旦 Hsc 落地（cos(arctan1)>0 已证，域就绪），B4 即可照此装配。  *)
(* ================================================================== *)


(* 记号：θ := arctan(1)、w := π_L·(1/2)（w_leibniz） *)
Notation theta1 := arctan_one_real.
Notation w_leib := (real_mult cauchy_real_pi_leibniz (real_const (1 / 2))).

(* ============ A. 纯环 glue（真证）：4θ == π_L ⟹ 2θ == π_L·(1/2) ============ *)
(* 步骤 1：(1/2)·(4·θ) == 2·θ（real_const 环，逐点 field） *)
Lemma real_const_half_four : real_eq (real_mult (real_const (1 / 2)) (real_const 4))
                                     (real_const 2).
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite !(real_mult_proj (real_const (1 / 2)) (real_const 4) n).
  rewrite !(real_const_proj (1 / 2) n). rewrite !(real_const_proj 4 n).
  rewrite (real_const_proj 2 n). field.
Qed.

(* (1/2)·(4·X) == 2·X（对任意 X：assoc + const 桥） *)
Lemma real_half_four_mult : forall (X : Real),
  real_eq (real_mult (real_const (1 / 2)) (real_mult (real_const 4) X))
          (real_mult (real_const 2) X).
Proof.
  intro X.
  apply (real_eq_trans _ (real_mult (real_mult (real_const (1 / 2)) (real_const 4)) X) _).
  - exact (real_mult_assoc (real_const (1 / 2)) (real_const 4) X).
  - apply (RealSetoid.real_eq_mult_compat
             (real_mult (real_const (1 / 2)) (real_const 4)) X
             (real_const 2) X).
    + exact real_const_half_four.
    + apply real_eq_refl.
Qed.

(* 2·θ == θ + θ（p_tan_def 已有 real_two_mult_plus，方向 2X==X+X；
   此处用反向）。 *)
Lemma real_theta_double_eq_two : real_eq (real_plus theta1 theta1)
                                         (real_mult (real_const 2) theta1).
Proof.
  exact (real_eq_sym (real_mult (real_const 2) theta1) (real_plus theta1 theta1) (real_two_mult_plus theta1)).
Qed.

(* ============ B. N5：由 H4（B3-3 值桥）+ Hsc ⟹ cos(w_leibniz) == 0 ============ *)
Section N10Channel.

(* 输入 1（B3-3 值桥）：4·arctan(1) == π_L *)
Hypothesis H4 : real_eq (real_mult (real_const 4) theta1) cauchy_real_pi_leibniz.

(* 输入 2（N9b 核心，本件精确定义为唯一解析输入）：
   sin(arctan(1)) == cos(arctan(1))（等价 tan(arctan(1)) == 1） *)
Hypothesis Hsc : real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1).

(* ---- B1. cos(2·arctan(1)) == 0（倍角 + Hsc；p_tan_def 通道） ---- *)
Lemma channel_cos_double_zero :
  real_eq (cauchy_real_cos (real_mult (real_const 2) theta1)) real_zero.
Proof.
  exact (real_sin_eq_cos_cos_two_zero theta1 Hsc).
Qed.

(* ---- B2. w_leibniz == 2·θ（从 H4：乘 (1/2) 两侧） ---- *)
Lemma channel_w_eq_two_theta :
  real_eq w_leib (real_mult (real_const 2) theta1).
Proof.
  (* w == π_L·(1/2) == (1/2)·π_L == (1/2)·(4θ) == 2θ *)
  unfold w_leib.
  apply (real_eq_trans _ (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz) _).
  - apply real_mult_comm.
  - apply (real_eq_trans _ (real_mult (real_const (1 / 2)) (real_mult (real_const 4) theta1)) _).
    + apply (RealSetoid.real_eq_mult_compat
               (real_const (1 / 2)) cauchy_real_pi_leibniz
               (real_const (1 / 2)) (real_mult (real_const 4) theta1)).
      * apply real_eq_refl.
      * apply real_eq_sym. exact H4.
    + exact (real_half_four_mult theta1).
Qed.

(* ---- B3. N5：cos(w_leibniz) == 0 ---- *)
Lemma channel_n5 : real_eq (cauchy_real_cos w_leib) real_zero.
Proof.
  (* cos w == cos(2θ) == 0：real_cos_eq_compat（w == 2θ）+ B1 *)
  apply (real_eq_trans _ (cauchy_real_cos (real_mult (real_const 2) theta1)) _).
  - apply real_cos_eq_compat. exact channel_w_eq_two_theta.
  - exact channel_cos_double_zero.
Qed.

(* ============ C. F1：由 N5 + 唯一零桥 + 乘 2 回代（sD p1 装配，全真证） ============ *)
(* 前置：3/2 < w_leibniz（N1–N4 已在主库） *)
Lemma channel_w_lower : real_lt (real_const (3 / 2)) w_leib.
Proof.
  exact real_pi_leibniz_half_lower.
Qed.

(* w_leibniz < 5/3 < 2（N1–N4 上界 + 常数） *)
Lemma channel_w_upper_two : real_lt w_leib (real_const 2).
Proof.
  apply (real_lt_trans _ (real_const (5 / 3)) _).
  - exact real_pi_leibniz_half_upper.
  - apply real_const_lt. change (Qlt (5 / 3) 2). compute. reflexivity.
Qed.

(* 唯一零桥：w ∈ (3/2,2) ∧ cos w == 0 ⟹ w == cos_pi_half *)
Lemma channel_w_eq_cos_pi_half : real_eq w_leib cos_pi_half.
Proof.
  apply (cos_pi_half_unique_widened w_leib).
  - exact channel_w_lower.
  - exact channel_w_upper_two.
  - exact channel_n5.
Qed.

(* 乘 2：2·w == π_L（real_double_half_cancel：2·(x·(1/2)) == x） *)
Lemma channel_two_w_eq_pi : real_eq (real_mult (real_const 2) w_leib)
                                    cauchy_real_pi_leibniz.
Proof.
  unfold w_leib.
  exact (real_double_half_cancel cauchy_real_pi_leibniz).
Qed.

(* F1：π_geom == 2·cos_pi_half == 2·w == π_L *)
Lemma channel_f1 : real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  unfold real_pi_geom.
  apply (real_eq_trans _ (real_mult (real_const 2) w_leib) _).
  - apply (RealSetoid.real_eq_mult_compat (real_const 2) cos_pi_half
                                          (real_const 2) w_leib).
    + apply real_eq_refl.
    + apply real_eq_sym. exact channel_w_eq_cos_pi_half.
  - exact channel_two_w_eq_pi.
Qed.

End N10Channel.

(* ============ D. 装配层引理（Section 变量以外全部闭包形式） ============ *)
(* 把 Section 封成可实例化的引理形态：两个解析输入 ⟹ F1。 *)
Lemma n10_closure_f1 :
  (real_eq (real_mult (real_const 4) theta1) cauchy_real_pi_leibniz) ->
  (real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1)) ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intros H4 Hsc.
  exact (channel_f1 H4 Hsc).
Qed.

Lemma n10_closure_n5 :
  (real_eq (real_mult (real_const 4) theta1) cauchy_real_pi_leibniz) ->
  (real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1)) ->
  real_eq (cauchy_real_cos w_leib) real_zero.
Proof.
  intros H4 Hsc.
  exact (channel_n5 H4 Hsc).
Qed.

(* ============ E. tan(arctan(1)) == 1 ⟺ sin == cos（真证桥，域已备） ============ *)
(* 顺向：tan θ == 1 ⟹ sin θ == cos θ *)
Lemma arctan_one_tan_eq_one_to_sc :
  real_eq arctan_one_tan real_one ->
  real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1).
Proof.
  intro Ht.
  exact (real_tan_eq_one_sin_eq_cos theta1 real_cos_arctan_one_pos Ht).
Qed.

(* 反向：sin θ == cos θ ⟹ tan θ == 1 *)
Lemma arctan_one_sc_to_tan_eq_one :
  real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1) ->
  real_eq arctan_one_tan real_one.
Proof.
  intro Hsc.
  exact (real_sin_eq_cos_tan_eq_one theta1 real_cos_arctan_one_pos Hsc).
Qed.

(* 复合完结引理（供 B4 直接引用）：tan(arctan(1)) == 1 + B3-3 ⟹ F1 *)
Lemma n10_closure_f1_tan :
  (real_eq (real_mult (real_const 4) theta1) cauchy_real_pi_leibniz) ->
  (real_eq arctan_one_tan real_one) ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intros H4 Ht.
  apply (n10_closure_f1 H4).
  exact (arctan_one_tan_eq_one_to_sc Ht).
Qed.
(* ============ 0. 记号 ============ *)
(* θ := arctan(1)（主库 L66941）；π_L := cauchy_real_pi_leibniz（L56355）
   注：theta1/w_leib 记号主库已声明（theta1 := arctan_one_real），此处不重复。 *)

(* ============ 1. 纯 Q 小工具 ============ *)

(* 0 ≤ y ≤ x ⟹ |x − y| ≤ x *)
Lemma sc_qabs_le_x_minus_y : forall x y : Q, Qle 0 y -> Qle y x -> Qle (Qabs (x - y)) x.
Proof.
  intros x y Hy0 Hyx.
  apply (Qle_trans _ (x - y) _).
  - (* |x−y| == x−y（0 ≤ x−y） ≤ x−y *)
    apply qeq_imp_qle.
    apply (Qabs_pos (x - y)).
    apply (proj1 (Qle_minus_iff y x)). exact Hyx.
  - (* x − y ≤ x ⟺ 0 ≤ y *)
    apply (proj2 (Qle_minus_iff (x - y) x)).
    setoid_replace (x - (x - y)) with y by ring.
    exact Hy0.
Qed.

(* 任意 n 的奇偶二分（Set 层）：n = 2m 或 n = 2m+1 *)
Lemma sc_nat_parity : forall n : nat, {m : nat | n = (2 * m)%nat} + {m : nat | n = (2 * m + 1)%nat}.
Proof.
  induction n as [| n IH].
  - left. exists 0%nat. lia.
  - destruct IH as [[m Hm] | [m Hm]].
    + right. exists m. lia.
    + left. exists (Datatypes.S m). lia.
Qed.

(* 4 == lp_four（常数桥；lp_four := 1+1+1+1） *)
Lemma a3_four_eq_lp : 4 == lp_four.
Proof.
  unfold lp_four. ring.
Qed.

(* ============ 2. 偶指标桥界（sharp 1/(2·(2m)+3) == 1/(4m+3)） ============ *)
(* S_{2m}(1) == lp_odd m + lp_a(2m+1)（even 桥）；
   |S_{2m} − lp_odd(2m)| == lp_a(2m+1) − (lp_odd(2m) − lp_odd m) ≤ lp_a(2m+1) *)
Lemma a3_even_bound : forall m : nat,
  Qle (Qabs (arctan_partial (2 * m) 1 - lp_odd (2 * m)))
      (1 / (Z.of_nat (2 * (2 * m) + 3) # 1)).
Proof.
  intro m.
  setoid_rewrite (arctan_partial_even_one m).
  assert (Hb : (lp_odd m + lp_a (2 * m + 1)) - lp_odd (2 * m) ==
                lp_a (2 * m + 1) - (lp_odd (2 * m) - lp_odd m)) by ring.
  setoid_rewrite Hb.
  apply (Qle_trans _ (lp_a (2 * m + 1)) _).
  - (* |x − y| ≤ x（x := lp_a(2m+1)，y := lp_odd(2m) − lp_odd m；0 ≤ y ≤ x） *)
    apply (sc_qabs_le_x_minus_y (lp_a (2 * m + 1)) (lp_odd (2 * m) - lp_odd m)).
    + (* 0 ≤ y：差分非负（m ≤ 2m） *)
      apply sc_lp_odd_diff_nonneg. lia.
    + (* y ≤ x：y ≤ lp_a(2m+2)（sc_lp_odd_diff_bound m 2m）≤ lp_a(2m+1)（decr） *)
      apply (Qle_trans _ (lp_a (2 * m + 2)) _).
      * apply sc_lp_odd_diff_bound. lia.
      * apply sc_lpa_decr_le. lia.
  - (* lp_a(2m+1) == 1/(Z.of_nat (2·(2m)+3)#1)（2·(2m+1)+1 == 2·(2m)+3） *)
    apply qeq_imp_qle.
    unfold lp_a.
    replace (2 * (2 * m + 1) + 1)%nat with (2 * (2 * m) + 3)%nat by lia.
    reflexivity.
Qed.

(* ============ 3. 奇指标桥界（sharp 1/(2·(2m+1)+3) == 1/(4m+5)） ============ *)
(* S_{2m+1}(1) == lp_odd m（odd 桥）；|S − lp_odd(2m+1)| == lp_odd(2m+1) − lp_odd m *)
Lemma a3_odd_bound : forall m : nat,
  Qle (Qabs (arctan_partial (2 * m + 1) 1 - lp_odd (2 * m + 1)))
      (1 / (Z.of_nat (2 * (2 * m + 1) + 3) # 1)).
Proof.
  intro m.
  setoid_rewrite (arctan_partial_odd_one m).
  apply (Qle_trans _ (lp_a (2 * m + 2)) _).
  - (* |lp_odd m − lp_odd(2m+1)| ≤ lp_a(2m+2) *)
    apply (Qle_trans _ (Qabs (lp_odd (2 * m + 1) - lp_odd m)) _).
    + (* |a − b| == |b − a| ⟹ ≤ *)
      apply qeq_imp_qle.
      apply (sc_lp_abs_sym (lp_odd m) (lp_odd (2 * m + 1))).
    + (* |lp_odd(2m+1) − lp_odd m| == lp_odd(2m+1) − lp_odd m（单调 m ≤ 2m+1） ≤ 尾界 *)
      assert (Hmo : Qle (lp_odd m) (lp_odd (2 * m + 1)))
        by (apply sc_lp_odd_chain; lia).
      assert (Hpos : Qle 0 (lp_odd (2 * m + 1) - lp_odd m)).
      { apply (proj1 (Qle_minus_iff (lp_odd m) (lp_odd (2 * m + 1)))). exact Hmo. }
      rewrite (Qabs_pos (lp_odd (2 * m + 1) - lp_odd m) Hpos).
      apply sc_lp_odd_diff_bound. lia.
  - (* lp_a(2m+2) == 1/(Z.of_nat (2·(2m+1)+3)#1)（2·(2m+2)+1 == 2·(2m+1)+3） *)
    apply qeq_imp_qle.
    unfold lp_a.
    replace (2 * (2 * m + 2) + 1)%nat with (2 * (2 * m + 1) + 3)%nat by lia.
    reflexivity.
Qed.

(* ============ 4. 统一（对角）界：|S_n(1) − lp_odd n| ≤ 1/(2n+3) ============ *)
Lemma a3_ptw_bound : forall n : nat,
  Qle (Qabs (arctan_partial n 1 - lp_odd n)) (1 / (Z.of_nat (2 * n + 3) # 1)).
Proof.
  intro n.
  destruct (sc_nat_parity n) as [[m Hm] | [m Hm]]; subst n.
  - exact (a3_even_bound m).
  - exact (a3_odd_bound m).
Qed.

(* ============ 5. 对角差恒等：|projT1 (4·θ) n − projT1 π_L n| == lp_four·|S_n − lp_odd n| ============ *)
Lemma a3_diag_abs : forall n : nat,
  Qabs (projT1 (real_mult (real_const 4) arctan_one_real) n - projT1 cauchy_real_pi_leibniz n)
  == lp_four * Qabs (arctan_partial n 1 - lp_odd n).
Proof.
  intro n.
  rewrite (real_mult_proj (real_const 4) arctan_one_real n).
  rewrite (real_const_proj 4 n).
  rewrite (arctan_one_proj n).
  rewrite (real_pi_leibniz_proj n).
  (* 4 → lp_four（常数桥） *)
  setoid_rewrite a3_four_eq_lp.
  (* |lp_four·S − lp_four·lp| == |lp_four·(S − lp)| == lp_four·|S − lp| *)
  apply (Qeq_trans _ (Qabs (lp_four * (arctan_partial n 1 - lp_odd n))) _).
  - apply (Qabs_wd (lp_four * arctan_partial n 1 - lp_four * lp_odd n)
                   (lp_four * (arctan_partial n 1 - lp_odd n))).
    ring.
  - rewrite Qabs_Qmult.
    assert (Hlp : Qabs lp_four == lp_four) by (apply Qabs_pos; exact sc_lp_four_nonneg).
    rewrite Hlp. reflexivity.
Qed.

(* ============ 6. 主定理 H4（A3/B3-3 值桥，闭式，零假设） ============ *)
(* real_eq 对角 eps：∀eps ∃N ∀n ≥ N：|projT1 (4·θ) n − projT1 π_L n| < eps
   链：|u n − v n| == lp_four·|S_n − lp_odd n| ≤ lp_four·(1/(2n+3))
       ≤ lp_four·(1/(N+2)) < eps（N 由 q_arch_inv (eps/lp_four) 给出） *)
Lemma a3_h4_value_bridge :
  real_eq (real_mult (real_const 4) arctan_one_real) cauchy_real_pi_leibniz.
Proof.
  intro eps. intro Heps.
  assert (Hq : Qlt 0 (eps / lp_four)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv lp_four)).
    - apply (QltT_to_Qlt 0 eps Heps).
    - apply Qinv_lt_0_compat. exact sc_lp_four_pos. }
  destruct (q_arch_inv (eps / lp_four) Hq) as [N HN].
  exists N.
  intro n. intro Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (lp_four * (1 / (Z.of_nat (N + 2) # 1))) _).
  - (* |u n − v n| ≤ lp_four·(1/(2n+3)) ≤ lp_four·(1/(N+2)) *)
    apply (Qle_trans _ (lp_four * (1 / (Z.of_nat (2 * n + 3) # 1))) _).
    + (* |u n − v n| == lp_four·|S_n − lp_odd n| ≤ lp_four·(1/(2n+3)) *)
      rewrite (a3_diag_abs n).
      apply (sc_qmult_le_l (Qabs (arctan_partial n 1 - lp_odd n))
                           (1 / (Z.of_nat (2 * n + 3) # 1)) lp_four).
      * exact (a3_ptw_bound n).
      * exact sc_lp_four_nonneg.
    + (* lp_four·(1/(2n+3)) ≤ lp_four·(1/(N+2))（n ≥ N ⟹ 2n+3 ≥ N+2） *)
      apply (sc_qmult_le_l (1 / (Z.of_nat (2 * n + 3) # 1))
                           (1 / (Z.of_nat (N + 2) # 1)) lp_four).
      * apply (atan_inv_chain N n). apply NatLe_drop in Hn. lia.
      * exact sc_lp_four_nonneg.
  - (* lp_four·(1/(N+2)) < eps（HN : 1/(N+2) < eps/lp_four） *)
    apply (sc_lp_four_arch_lt eps N).
    + apply (QltT_to_Qlt 0 eps Heps).
    + exact HN.
Qed.

(* ============ 7. 可选加分：H4（本件闭证）+ Section 变量 Hsc ⟹ F1 ============ *)
(* F1（real_pi_geom == π_L）本体等 N9b 批的 Hsc；Hsc 作 Section 变量不实例化。
   n10_closure_f1（主库 L67256）已备好同一 glue：此处仅把 H4 从假设换成真证。 *)
Section A3HscToF1.

  (* 唯一解析输入（N9b 核，留给其批）：sin(arctan(1)) == cos(arctan(1)) *)
  Hypothesis HscA3 : real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real).

  Lemma a3_section_f1 : real_eq real_pi_geom cauchy_real_pi_leibniz.
  Proof.
    exact (n10_closure_f1 a3_h4_value_bridge HscA3).
  Qed.

  Lemma a3_section_n5 : real_eq (cauchy_real_cos w_leib) real_zero.
  Proof.
    exact (n10_closure_n5 a3_h4_value_bridge HscA3).
  Qed.

End A3HscToF1.

(* 闭包形态（H4 已闭证 ⟹ 只剩 Hsc 一个输入；N9b 批实例化即完结） *)
Lemma a3_closure_f1 :
  (real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real)) ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intro Hsc. exact (a3_section_f1 Hsc).
Qed.

Lemma a3_closure_n5 :
  (real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real)) ->
  real_eq (cauchy_real_cos w_leib) real_zero.
Proof.
  intro Hsc. exact (a3_section_n5 Hsc).
Qed.

(* ============================================================ *)
(* T-π3 Hsc Phase A 并入（迭代 207）：B1+B2 sin/cos 可微          *)
(* 来源：sc2_f1_sincos（19+15 Qed）；零公理面。                    *)
(* ============================================================ *)

Open Scope Q_scope.

(* ---- Qeq setoid 形态注册（根文件在 L8372-8375 手动注册、不随模块导出；
       沙箱内补注册，恢复上下文内 Qeq 重写） ---- *)
#[global] Instance Qeq_rewrite_rel : RewriteRelation Qeq := {}.

#[global] Instance Qplus_morph : Proper (Qeq ==> Qeq ==> Qeq) Qplus.
Proof. intros x y Hxy z w Hzw. exact (Qplus_comp x y Hxy z w Hzw). Qed.

#[global] Instance Qopp_morph : Proper (Qeq ==> Qeq) Qopp.
Proof. intros x y Hxy. exact (Qopp_comp x y Hxy). Qed.

#[global] Instance Qminus_morph : Proper (Qeq ==> Qeq ==> Qeq) Qminus.
Proof. intros x y Hxy z w Hzw. exact (Qminus_comp x y Hxy z w Hzw). Qed.

#[global] Instance Qmult_morph : Proper (Qeq ==> Qeq ==> Qeq) Qmult.
Proof. intros x y Hxy z w Hzw. exact (Qmult_comp x y Hxy z w Hzw). Qed.

(* ============ 批 B1 第 1 部分：Q 层闭式线性化界 ============ *)
(* 原料（205 实测行号）：sc_sin_partial_upper_x L57150、        *)
(*   sc_sin_partial_lower_c1 L57162（x−x³/6 ≤ sin ≤ x）、       *)
(*   sc_cos_partial_upper_one L57184、sc_cos_partial_lower_c1   *)
(*   L57196（1−x²/2 ≤ cos ≤ 1）、sc_sin_alt1_cube L57558、      *)
(*   sc_cos_alt1_half L57877、sc_sin_partial_neg L55563、       *)
(*   sc_cos_partial_neg L55571。全部按名 Require。              *)

(* ---- 整式奇偶桥：sin_partial n (−t) − (−t) == −(sin_partial n t − t) ---- *)
Lemma sc_sin_lin_odd : forall (n : nat) (t : Q),
  sin_partial n (- t) - (- t) == - (sin_partial n t - t).
Proof.
  intros n t.
  rewrite (sc_sin_partial_neg n t).
  ring.
Qed.

(* ---- 整式偶性桥：cos_partial n (−t) − 1 == cos_partial n t − 1 ---- *)
Lemma sc_cos_lin_even : forall (n : nat) (t : Q),
  cos_partial n (- t) - 1 == cos_partial n t - 1.
Proof.
  intros n t.
  rewrite (sc_cos_partial_neg n t).
  reflexivity.
Qed.

(* ---- sin：0 ≤ x ≤ 1 ⟹ |sin_partial n x − x| ≤ x³/6 ---- *)
Lemma sc_sin_cube_bound_pos : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  Qle (Qabs (sin_partial n x - x)) (q_pow x 3 / 6).
Proof.
  intros n x Hx0 Hx1.
  assert (Hu : Qle (sin_partial n x) x).
  { apply sc_sin_partial_upper_x. exact Hx0. exact Hx1. }
  assert (Hl : Qle (x - sc_sin_alt 1 x) (sin_partial n x)).
  { apply sc_sin_partial_lower_c1. exact Hx0. exact Hx1. }
  (* x − sin_partial ≤ sc_sin_alt 1 x（由 Hl 移项） *)
  assert (Hsub : Qle (x - sin_partial n x) (sc_sin_alt 1 x)).
  { apply (proj2 (Qle_minus_iff (x - sin_partial n x) (sc_sin_alt 1 x))).
    assert (Heq : sc_sin_alt 1 x - (x - sin_partial n x) ==
                  sin_partial n x - (x - sc_sin_alt 1 x)) by ring.
    rewrite Heq.
    apply (proj1 (Qle_minus_iff (x - sc_sin_alt 1 x) (sin_partial n x))).
    exact Hl. }
  (* 0 ≤ x − sin_partial（由 Hu） *)
  assert (Hnonneg : Qle 0 (x - sin_partial n x)).
  { apply (proj1 (Qle_minus_iff (sin_partial n x) x)). exact Hu. }
  apply (Qle_trans _ (x - sin_partial n x) _).
  - (* |sin − x| == x − sin *)
    assert (Habs : Qabs (sin_partial n x - x) == x - sin_partial n x).
    { assert (H1 : sin_partial n x - x == - (x - sin_partial n x)) by ring.
      rewrite H1.
      rewrite (Qabs_opp (x - sin_partial n x)).
      rewrite (Qabs_pos (x - sin_partial n x) Hnonneg).
      reflexivity. }
    apply qeq_le. exact Habs.
  - apply (Qle_trans _ (sc_sin_alt 1 x) _).
    + exact Hsub.
    + rewrite (sc_sin_alt1_cube x). apply Qle_refl.
Qed.

(* ---- sin：|x| ≤ 1 ⟹ |sin_partial n x − x| ≤ |x|³/6（奇偶桥归约） ---- *)
Lemma sc_sin_cube_bound : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 ->
  Qle (Qabs (sin_partial n x - x)) (q_pow (Qabs x) 3 / 6).
Proof.
  intros n x Hxabs.
  destruct (Qlt_le_dec x 0) as [Hxneg | Hxnn].
  - (* x < 0：整式奇偶桥到 −x ≥ 0，再桥 q_pow 底 *)
    assert (Habsx : Qabs x == - x).
    { apply Qabs_neg. apply (Qlt_le_weak x 0). exact Hxneg. }
    assert (Ht0 : Qle 0 (- x)).
    { apply (Qle_trans 0 (0 - x) (- x)).
      - apply (proj1 (Qle_minus_iff x 0)).
        apply (Qlt_le_weak x 0). exact Hxneg.
      - apply qeq_le. ring. }
    assert (Ht1 : Qle (- x) 1).
    { apply (Qle_trans (- x) (Qabs x) 1).
      - apply qeq_le. apply Qeq_sym. exact Habsx.
      - exact Hxabs. }
    assert (Hpos : Qle (Qabs (sin_partial n (- x) - (- x))) (q_pow (- x) 3 / 6)).
    { apply (sc_sin_cube_bound_pos n (- x) Ht0 Ht1). }
    (* 目标：|f(x)| ≤ q_pow (Qabs x) 3/6 *)
    assert (Hbr : Qabs (sin_partial n x - x) ==
                  Qabs (sin_partial n (- x) - (- x))).
    { apply Qeq_sym.
      apply (Qeq_trans _ (Qabs (- (sin_partial n x - x))) _).
      - apply Qabs_wd. exact (sc_sin_lin_odd n x).
      - apply Qabs_opp. }
    apply (Qle_trans (Qabs (sin_partial n x - x))
                     (Qabs (sin_partial n (- x) - (- x)))
                     (q_pow (Qabs x) 3 / 6)).
    + apply qeq_le. exact Hbr.
    + apply (Qle_trans _ (q_pow (- x) 3 / 6) _).
      * exact Hpos.
      * rewrite (q_pow_wd (- x) (Qabs x) 3 (Qeq_sym (Qabs x) (- x) Habsx)).
        apply Qle_refl.
  - (* x ≥ 0：Qabs x == x *)
    assert (Habsx : Qabs x == x).
    { apply Qabs_pos. exact Hxnn. }
    assert (Hx1 : Qle x 1) by (rewrite <- Habsx; exact Hxabs).
    rewrite Habsx.
    apply (sc_sin_cube_bound_pos n x Hxnn Hx1).
Qed.

(* ---- cos：0 ≤ x ≤ 1 ⟹ |cos_partial n x − 1| ≤ x²/2 ---- *)
Lemma sc_cos_sq_bound_pos : forall (n : nat) (x : Q),
  Qle 0 x -> Qle x 1 ->
  Qle (Qabs (cos_partial n x - 1)) (q_pow x 2 / 2).
Proof.
  intros n x Hx0 Hx1.
  assert (Hu : Qle (cos_partial n x) 1).
  { apply sc_cos_partial_upper_one. exact Hx0. exact Hx1. }
  assert (Hl : Qle (1 - sc_cos_alt 1 x) (cos_partial n x)).
  { apply sc_cos_partial_lower_c1. exact Hx0. exact Hx1. }
  (* 1 − cos_partial ≤ sc_cos_alt 1 x *)
  assert (Hsub : Qle (1 - cos_partial n x) (sc_cos_alt 1 x)).
  { apply (proj2 (Qle_minus_iff (1 - cos_partial n x) (sc_cos_alt 1 x))).
    assert (Heq : sc_cos_alt 1 x - (1 - cos_partial n x) ==
                  cos_partial n x - (1 - sc_cos_alt 1 x)) by ring.
    rewrite Heq.
    apply (proj1 (Qle_minus_iff (1 - sc_cos_alt 1 x) (cos_partial n x))).
    exact Hl. }
  (* 0 ≤ 1 − cos_partial *)
  assert (Hnonneg : Qle 0 (1 - cos_partial n x)).
  { apply (proj1 (Qle_minus_iff (cos_partial n x) 1)). exact Hu. }
  apply (Qle_trans _ (1 - cos_partial n x) _).
  - (* |cos − 1| == 1 − cos *)
    assert (Habs : Qabs (cos_partial n x - 1) == 1 - cos_partial n x).
    { assert (H1 : cos_partial n x - 1 == - (1 - cos_partial n x)) by ring.
      rewrite H1.
      rewrite (Qabs_opp (1 - cos_partial n x)).
      rewrite (Qabs_pos (1 - cos_partial n x) Hnonneg).
      reflexivity. }
    apply qeq_le. exact Habs.
  - apply (Qle_trans _ (sc_cos_alt 1 x) _).
    + exact Hsub.
    + rewrite (sc_cos_alt1_half x). apply Qle_refl.
Qed.

(* ---- cos：|x| ≤ 1 ⟹ |cos_partial n x − 1| ≤ |x|²/2（偶性桥归约） ---- *)
Lemma sc_cos_sq_bound : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 ->
  Qle (Qabs (cos_partial n x - 1)) (q_pow (Qabs x) 2 / 2).
Proof.
  intros n x Hxabs.
  destruct (Qlt_le_dec x 0) as [Hxneg | Hxnn].
  - (* x < 0：整式偶性桥到 −x ≥ 0 *)
    assert (Habsx : Qabs x == - x).
    { apply Qabs_neg. apply (Qlt_le_weak x 0). exact Hxneg. }
    assert (Ht0 : Qle 0 (- x)).
    { apply (Qle_trans 0 (0 - x) (- x)).
      - apply (proj1 (Qle_minus_iff x 0)).
        apply (Qlt_le_weak x 0). exact Hxneg.
      - apply qeq_le. ring. }
    assert (Ht1 : Qle (- x) 1).
    { apply (Qle_trans (- x) (Qabs x) 1).
      - apply qeq_le. apply Qeq_sym. exact Habsx.
      - exact Hxabs. }
    assert (Hpos : Qle (Qabs (cos_partial n (- x) - 1)) (q_pow (- x) 2 / 2)).
    { apply (sc_cos_sq_bound_pos n (- x) Ht0 Ht1). }
    assert (Hbr : Qabs (cos_partial n x - 1) ==
                  Qabs (cos_partial n (- x) - 1)).
    { apply Qabs_wd. apply Qeq_sym. exact (sc_cos_lin_even n x). }
    apply (Qle_trans (Qabs (cos_partial n x - 1))
                     (Qabs (cos_partial n (- x) - 1))
                     (q_pow (Qabs x) 2 / 2)).
    + apply qeq_le. exact Hbr.
    + apply (Qle_trans _ (q_pow (- x) 2 / 2) _).
      * exact Hpos.
      * rewrite (q_pow_wd (- x) (Qabs x) 2 (Qeq_sym (Qabs x) (- x) Habsx)).
        apply Qle_refl.
  - (* x ≥ 0：Qabs x == x *)
    assert (Habsx : Qabs x == x).
    { apply Qabs_pos. exact Hxnn. }
    assert (Hx1 : Qle x 1) by (rewrite <- Habsx; exact Hxabs).
    rewrite Habsx.
    apply (sc_cos_sq_bound_pos n x Hxnn Hx1).
Qed.

(* ============ 批 B1 第 2 部分：Q 层粗化与点值吸收链 ============ *)

(* 左乘子单调：0 ≤ a、b ≤ c ⟹ a·b ≤ a·c（Stdlib 只给右乘子版） *)
Lemma sc_qmult_le_l_f1 : forall (a b c : Q),
  Qle 0 a -> Qle b c -> Qle (Qmult a b) (Qmult a c).
Proof.
  intros a b c Ha Hbc.
  apply (Qle_trans (Qmult a b) (Qmult b a) (Qmult a c)).
  - apply qeq_le. ring.
  - apply (Qle_trans (Qmult b a) (Qmult c a) (Qmult a c)).
    + apply (Qmult_le_compat_r b c a Hbc Ha).
    + apply qeq_le. ring.
Qed.

(* 粗化：x ≥ 0 ⟹ x³/6 ≤ x³ *)
Lemma sc_qpow3_div6_le : forall x : Q, Qle 0 x ->
  Qle (q_pow x 3 / 6) (q_pow x 3).
Proof.
  intros x Hx0.
  unfold Qdiv.
  apply (Qle_trans _ (Qmult (q_pow x 3) 1) _).
  - apply (sc_qmult_le_l_f1 (q_pow x 3) (Qinv 6) 1%Q).
    + apply (q_pow_nonneg x 3 Hx0).
    + apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - apply qeq_le. ring.
Qed.

(* 粗化：x ≥ 0 ⟹ x²/2 ≤ x² *)
Lemma sc_qpow2_div2_le : forall x : Q, Qle 0 x ->
  Qle (q_pow x 2 / 2) (q_pow x 2).
Proof.
  intros x Hx0.
  unfold Qdiv.
  apply (Qle_trans _ (Qmult (q_pow x 2) 1) _).
  - apply (sc_qmult_le_l_f1 (q_pow x 2) (Qinv 2) 1%Q).
    + apply (q_pow_nonneg x 2 Hx0).
    + apply Qlt_le_weak. unfold Qlt. simpl. lia.
  - apply qeq_le. ring.
Qed.

(* |x| ≤ 1 ⟹ |sin_partial n x − x| ≤ |x|³（C = 1 粗版） *)
Lemma sc_sin_cube_bound_c1 : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 ->
  Qle (Qabs (sin_partial n x - x)) (q_pow (Qabs x) 3).
Proof.
  intros n x Hxabs.
  apply (Qle_trans _ (q_pow (Qabs x) 3 / 6) _).
  - apply (sc_sin_cube_bound n x Hxabs).
  - apply (sc_qpow3_div6_le (Qabs x)). apply Qabs_nonneg.
Qed.

(* |x| ≤ 1 ⟹ |cos_partial n x − 1| ≤ |x|²（C = 1 粗版） *)
Lemma sc_cos_sq_bound_c1 : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 ->
  Qle (Qabs (cos_partial n x - 1)) (q_pow (Qabs x) 2).
Proof.
  intros n x Hxabs.
  apply (Qle_trans _ (q_pow (Qabs x) 2 / 2) _).
  - apply (sc_cos_sq_bound n x Hxabs).
  - apply (sc_qpow2_div2_le (Qabs x)). apply Qabs_nonneg.
Qed.

(* q_pow 底形式 *)
Lemma sc_qpow3_form : forall x : Q, q_pow x 3 == x * x * x.
Proof. intro x. cbn [q_pow]. ring. Qed.

Lemma sc_qpow2_form : forall x : Q, q_pow x 2 == x * x.
Proof. intro x. cbn [q_pow]. ring. Qed.

(* x ≤ a ∧ x ≤ b ∧ x ≥ 0 ⟹ x³ ≤ x·a·b *)
Lemma sc_qpow3_le_xab : forall (x a b : Q),
  Qle 0 x -> Qle x a -> Qle x b ->
  Qle (q_pow x 3) (Qmult (Qmult x a) b).
Proof.
  intros x a b Hx0 Hxa Hxb.
  rewrite (sc_qpow3_form x).
  assert (Hx2 : Qle (x * x) (a * b)).
  { apply (Qle_trans (x * x) (x * b) (a * b)).
    - apply (sc_qmult_le_l_f1 x x b Hx0). exact Hxb.
    - apply (Qmult_le_compat_r x a b Hxa).
      apply (Qle_trans 0 x b Hx0 Hxb). }
  apply (Qle_trans _ (x * (x * x)) _).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (x * (a * b)) _).
    + apply (sc_qmult_le_l_f1 x (x * x) (a * b) Hx0). exact Hx2.
    + apply qeq_le. ring.
Qed.

(* x ≤ a ∧ x ≥ 0 ⟹ x² ≤ x·a *)
Lemma sc_qpow2_le_xa : forall (x a : Q),
  Qle 0 x -> Qle x a ->
  Qle (q_pow x 2) (Qmult x a).
Proof.
  intros x a Hx0 Hxa.
  rewrite (sc_qpow2_form x).
  apply (sc_qmult_le_l_f1 x x a Hx0). exact Hxa.
Qed.

(* 点值主链 sin：x ≥ 0、x ≤ 1/2、x ≤ en/2、en ≥ 0 ⟹ x³ ≤ en·x *)
Lemma sc_sin_main_le : forall (x en : Q),
  Qle 0 x -> Qle x (Qinv 2) -> Qle x (Qmult en (Qinv 2)) -> Qle 0 en ->
  Qle (q_pow x 3) (Qmult en x).
Proof.
  intros x en Hx0 Hx12 Hxe Hen0.
  apply (Qle_trans _ (Qmult (Qmult x (Qinv 2)) (Qmult en (Qinv 2))) _).
  - apply (sc_qpow3_le_xab x (Qinv 2) (Qmult en (Qinv 2))). exact Hx0. exact Hx12. exact Hxe.
  - apply (Qle_trans _ (Qmult en (Qmult x (1 # 4))) _).
    + apply qeq_le. field.
    + apply (Qle_trans _ (Qmult en (Qmult x 1)) _).
      * apply (sc_qmult_le_l_f1 en (Qmult x (1 # 4)) (Qmult x 1) Hen0).
        apply (sc_qmult_le_l_f1 x (1 # 4) 1%Q Hx0).
        unfold Qle. simpl. lia.
      * apply qeq_le. ring.
Qed.

(* 点值主链 cos：x ≥ 0、x ≤ en/2、en ≥ 0 ⟹ x² ≤ en·x *)
Lemma sc_cos_main_le : forall (x en : Q),
  Qle 0 x -> Qle x (Qmult en (Qinv 2)) -> Qle 0 en ->
  Qle (q_pow x 2) (Qmult en x).
Proof.
  intros x en Hx0 Hxe Hen0.
  apply (Qle_trans _ (Qmult x (Qmult en (Qinv 2))) _).
  - apply (sc_qpow2_le_xa x (Qmult en (Qinv 2))). exact Hx0. exact Hxe.
  - apply (Qle_trans _ (Qmult en (Qmult x (1 # 2))) _).
    + apply qeq_le. field.
    + apply (Qle_trans _ (Qmult en (Qmult x 1)) _).
      * apply (sc_qmult_le_l_f1 en (Qmult x (1 # 2)) (Qmult x 1) Hen0).
        apply (sc_qmult_le_l_f1 x (1 # 2) 1%Q Hx0).
        unfold Qle. simpl. lia.
      * apply qeq_le. ring.
Qed.

(* ============ 批 B1 第 3 部分：Real 层 sin/cos 在 0 的逐 eps 线性化 ============ *)
(* 语句同构 exp_minus_one_linear（L47823，205 实测）。设计 §2-D1 的 B1 产物：
   "|sin h − h| ≤ C|h|³、|cos h − 1| ≤ C|h|²（|h| ≤ 1）" 的 Real 层逐 eps 形态
   （real_le 闭式非严格形式受库 real_le := Or real_lt real_eq 定义限制不可构造，
   见根文件 L13513 注释；逐 eps 形态为库 idiom，且为 B2 直接所需）。
   C 常数信息保留在 Q 层：sc_sin_cube_bound（C=1/6）、sc_cos_sq_bound（C=1/2）。 *)

(* ---- |sin h − h| ≤ eps·|h| + eps'（|h| < delta；delta := min(1/2, eps/2)） ---- *)
Lemma real_sin_zero_linear_bound : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_sin h) (real_opp h)))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros eps Heps.
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (delta := real_min two_inv (real_mult eps two_inv)).
  exists delta.
  split.
  - (* 0 < delta *)
    unfold delta, two_inv.
    apply real_min_pos.
    + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
    + apply real_mult_positive.
      * exact Heps.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
  - intros h Hh eps' Heps'.
    assert (Hh_half : real_lt (real_abs h) two_inv)
      by (unfold delta in Hh; apply (real_min_lt_l h two_inv (real_mult eps two_inv)); exact Hh).
    assert (Hh_eps2 : real_lt (real_abs h) (real_mult eps two_inv))
      by (unfold delta in Hh; apply (real_min_lt_r h two_inv (real_mult eps two_inv)); exact Hh).
    (* real_le 左分支：real_lt 构造（见证 eps1'） *)
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
    destruct Hh_eps2 as [eps3 [Heps3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one real_one) (real_two_pos_local)) as [Ni HNi].
    exists eps1'.
    split.
    + exact Heps1'.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) Ni).
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
      (* 逐点展开 A、B *)
      assert (HA : projT1 (real_abs (real_plus (cauchy_real_sin h) (real_opp h))) n ==
                    Qabs (sin_partial n hn - hn)).
      { unfold hn.
        setoid_rewrite (real_abs_proj (real_plus (cauchy_real_sin h) (real_opp h)) n).
        setoid_rewrite (real_plus_proj (cauchy_real_sin h) (real_opp h) n).
        setoid_rewrite (real_opp_proj h n).
        rewrite (real_sin_proj h n).
        cbn [projT1].
        unfold Qminus. ring. }
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [projT1]. ring. }
      (* 逐点界 1：|hn| < 1/2 *)
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hni : (Ni <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
      { apply (Qlt_le_trans eps2 (Qminus (projT1 two_inv n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold two_inv.
          rewrite (HNi n Hni).
          rewrite (real_plus_proj real_one real_one n).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
        - apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). exact HN2q.
        - assert (Heps2q : Qle 0 eps2).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
          apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
          + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
          + apply qeq_le. ring. }
      (* 逐点界 2：|hn| < en/2 *)
      assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qinv 2)) (Qabs hn))).
      { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps two_inv) n) (projT1 (real_abs h) n))
                                (Qminus (Qmult en (Qinv 2)) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold two_inv, en.
          setoid_rewrite (real_mult_proj eps (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) n).
          setoid_rewrite (HNi n Hni).
          rewrite (real_plus_proj real_one real_one n).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_eps2 : Qlt (Qabs hn) (Qmult en (Qinv 2))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qinv 2)) eps3) (Qmult en (Qinv 2))).
        - apply (q_lt_minus_shift eps3 (Qmult en (Qinv 2)) (Qabs hn)). exact HN3q.
        - assert (Heps3q : Qle 0 eps3).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
          apply (Qle_trans (Qminus (Qmult en (Qinv 2)) eps3)
                           (Qplus (Qminus (Qmult en (Qinv 2)) eps3) eps3)
                           (Qmult en (Qinv 2))).
          + apply (Qle_trans (Qminus (Qmult en (Qinv 2)) eps3)
                             (Qplus (Qminus (Qmult en (Qinv 2)) eps3) 0)
                             (Qplus (Qminus (Qmult en (Qinv 2)) eps3) eps3)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en (Qinv 2)) eps3)
                                     (Qminus (Qmult en (Qinv 2)) eps3) 0 eps3 (Qle_refl _) Heps3q).
          + apply qeq_le. ring. }
      (* 主链：A_n ≤ en·|hn|（立方界 + 吸收） *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Henq : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (Hhn_le1 : Qle (Qabs hn) 1).
      { apply (Qle_trans (Qabs hn) (Qinv 2) 1).
        - apply Qlt_le_weak. exact Hhn_half.
        - unfold Qle. simpl. lia. }
      assert (Hhn_le12 : Qle (Qabs hn) (Qinv 2)) by (apply Qlt_le_weak; exact Hhn_half).
      assert (Hhn_leE2 : Qle (Qabs hn) (Qmult en (Qinv 2))) by (apply Qlt_le_weak; exact Hhn_eps2).
      assert (Hmain : Qle (Qabs (sin_partial n hn - hn)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (q_pow (Qabs hn) 3) _).
        - apply (sc_sin_cube_bound_c1 n hn Hhn_le1).
        - apply (sc_sin_main_le (Qabs hn) en).
          + apply Qabs_nonneg.
          + exact Hhn_le12.
          + exact Hhn_leE2.
          + exact Henq. }
      (* eps1' < B_n − A_n *)
      assert (Heps1e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (real_plus (cauchy_real_sin h) (real_opp h))) n))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (sin_partial n hn - hn)))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_sin h) (real_opp h))) n)
                           (Qabs (sin_partial n hn - hn)) HA). }
      assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (sin_partial n hn - hn)))).
      { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (sin_partial n hn - hn))))
                           (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (sin_partial n hn - hn)))).
        - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (sin_partial n hn - hn))))).
          + apply qeq_le. ring.
          + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (sin_partial n hn - hn)))
                                   (Qle_refl en')
                                   (proj1 (Qle_minus_iff (Qabs (sin_partial n hn - hn)) (Qmult en (Qabs hn))) Hmain)).
        - apply qeq_le. ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                            (projT1 (real_abs (real_plus (cauchy_real_sin h) (real_opp h))) n))).
      { apply QltT_to_Qlt. exact Heps1e. }
      { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (sin_partial n hn - hn)))
                               (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                       (projT1 (real_abs (real_plus (cauchy_real_sin h) (real_opp h))) n))).
        - exact Henle.
        - apply qeq_le. apply Qeq_sym. exact Hrepl. }
Qed.

(* ---- |cos h − 1| ≤ eps·|h| + eps'（|h| < delta；delta := min(1/2, eps/2)） ---- *)
Lemma real_cos_zero_linear_bound : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one)))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros eps Heps.
  set (two_inv := real_inv_pos (real_plus real_one real_one) (real_two_pos_local)).
  set (delta := real_min two_inv (real_mult eps two_inv)).
  exists delta.
  split.
  - (* 0 < delta *)
    unfold delta, two_inv.
    apply real_min_pos.
    + apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
    + apply real_mult_positive.
      * exact Heps.
      * apply (real_inv_pos_pos (real_plus real_one real_one) (real_two_pos_local)).
  - intros h Hh eps' Heps'.
    assert (Hh_half : real_lt (real_abs h) two_inv)
      by (unfold delta in Hh; apply (real_min_lt_l h two_inv (real_mult eps two_inv)); exact Hh).
    assert (Hh_eps2 : real_lt (real_abs h) (real_mult eps two_inv))
      by (unfold delta in Hh; apply (real_min_lt_r h two_inv (real_mult eps two_inv)); exact Hh).
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    destruct Hh_half as [eps2 [Heps2 [N2 HN2]]].
    destruct Hh_eps2 as [eps3 [Heps3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one real_one) (real_two_pos_local)) as [Ni HNi].
    exists eps1'.
    split.
    + exact Heps1'.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) Ni).
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n). set (en' := projT1 eps' n). set (hn := projT1 h n).
      (* 逐点展开 A、B *)
      assert (HA : projT1 (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one))) n ==
                    Qabs (cos_partial n hn - 1)).
      { unfold hn.
        setoid_rewrite (real_abs_proj (real_plus (cauchy_real_cos h) (real_opp real_one)) n).
        setoid_rewrite (real_plus_proj (cauchy_real_cos h) (real_opp real_one) n).
        setoid_rewrite (real_opp_proj real_one n).
        rewrite (real_cos_proj h n).
        cbn [projT1 real_one].
        unfold Qminus. ring. }
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [projT1]. ring. }
      (* 逐点界 1：|hn| < 1/2 *)
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hni : (Ni <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (HN2q : Qlt eps2 (Qminus (Qinv 2) (Qabs hn))).
      { apply (Qlt_le_trans eps2 (Qminus (projT1 two_inv n) (projT1 (real_abs h) n)) (Qminus (Qinv 2) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold two_inv.
          rewrite (HNi n Hni).
          rewrite (real_plus_proj real_one real_one n).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) (Qinv 2)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qinv 2) eps2) (Qinv 2)).
        - apply (q_lt_minus_shift eps2 (Qinv 2) (Qabs hn)). exact HN2q.
        - assert (Heps2q : Qle 0 eps2).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
          apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) eps2) (Qinv 2)).
          + apply (Qle_trans (Qminus (Qinv 2) eps2) (Qplus (Qminus (Qinv 2) eps2) 0) (Qplus (Qminus (Qinv 2) eps2) eps2)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qinv 2) eps2) (Qminus (Qinv 2) eps2) 0 eps2 (Qle_refl _) Heps2q).
          + apply qeq_le. ring. }
      (* 逐点界 2：|hn| < en/2 *)
      assert (HN3q : Qlt eps3 (Qminus (Qmult en (Qinv 2)) (Qabs hn))).
      { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps two_inv) n) (projT1 (real_abs h) n))
                                (Qminus (Qmult en (Qinv 2)) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold two_inv, en.
          setoid_rewrite (real_mult_proj eps (real_inv_pos (real_plus real_one real_one) (real_two_pos_local)) n).
          setoid_rewrite (HNi n Hni).
          rewrite (real_plus_proj real_one real_one n).
          cbn [real_one real_const projT1].
          reflexivity. }
      assert (Hhn_eps2 : Qlt (Qabs hn) (Qmult en (Qinv 2))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en (Qinv 2)) eps3) (Qmult en (Qinv 2))).
        - apply (q_lt_minus_shift eps3 (Qmult en (Qinv 2)) (Qabs hn)). exact HN3q.
        - assert (Heps3q : Qle 0 eps3).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
          apply (Qle_trans (Qminus (Qmult en (Qinv 2)) eps3)
                           (Qplus (Qminus (Qmult en (Qinv 2)) eps3) eps3)
                           (Qmult en (Qinv 2))).
          + apply (Qle_trans (Qminus (Qmult en (Qinv 2)) eps3)
                             (Qplus (Qminus (Qmult en (Qinv 2)) eps3) 0)
                             (Qplus (Qminus (Qmult en (Qinv 2)) eps3) eps3)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en (Qinv 2)) eps3)
                                     (Qminus (Qmult en (Qinv 2)) eps3) 0 eps3 (Qle_refl _) Heps3q).
          + apply qeq_le. ring. }
      (* 主链：A_n ≤ en·|hn|（平方界 + 吸收） *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Henq : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (Hhn_le1 : Qle (Qabs hn) 1).
      { apply (Qle_trans (Qabs hn) (Qinv 2) 1).
        - apply Qlt_le_weak. exact Hhn_half.
        - unfold Qle. simpl. lia. }
      assert (Hhn_leE2 : Qle (Qabs hn) (Qmult en (Qinv 2))) by (apply Qlt_le_weak; exact Hhn_eps2).
      assert (Hmain : Qle (Qabs (cos_partial n hn - 1)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (q_pow (Qabs hn) 2) _).
        - apply (sc_cos_sq_bound_c1 n hn Hhn_le1).
        - apply (sc_cos_main_le (Qabs hn) en).
          + apply Qabs_nonneg.
          + exact Hhn_leE2.
          + exact Henq. }
      (* eps1' < B_n − A_n *)
      assert (Heps1e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one))) n))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (cos_partial n hn - 1)))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one))) n)
                           (Qabs (cos_partial n hn - 1)) HA). }
      assert (Henle : Qle en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (cos_partial n hn - 1)))).
      { apply (Qle_trans en' (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (cos_partial n hn - 1))))
                           (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (cos_partial n hn - 1)))).
        - apply (Qle_trans en' (Qplus en' 0) (Qplus en' (Qminus (Qmult en (Qabs hn)) (Qabs (cos_partial n hn - 1))))).
          + apply qeq_le. ring.
          + apply (Qplus_le_compat en' en' 0 (Qminus (Qmult en (Qabs hn)) (Qabs (cos_partial n hn - 1)))
                                   (Qle_refl en')
                                   (proj1 (Qle_minus_iff (Qabs (cos_partial n hn - 1)) (Qmult en (Qabs hn))) Hmain)).
        - apply qeq_le. ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eps1' en' (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                            (projT1 (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one))) n))).
      { apply QltT_to_Qlt. exact Heps1e. }
      { apply (Qle_trans en' (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (cos_partial n hn - 1)))
                               (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                       (projT1 (real_abs (real_plus (cauchy_real_cos h) (real_opp real_one))) n))).
        - exact Henle.
        - apply qeq_le. apply Qeq_sym. exact Hrepl. }
Qed.

Open Scope Q_scope.

(* Qeq 形态实例随上游 sc2_f1_sincos_b1 的 Require 导入（#[global]）。 *)

(* ---- sin_partial / cos_partial 的 Qeq 全等（重写进参数所需） ---- *)
Lemma sc_sin_term_wd : forall (j : nat) (x y : Q), x == y -> sin_term j x == sin_term j y.
Proof.
  intros j x y Hxy.
  unfold sin_term, Qdiv.
  apply Qmult_comp.
  - apply Qeq_refl.
  - apply Qmult_comp.
    + apply (q_pow_wd x y (Datatypes.S (2 * j)) Hxy).
    + apply Qeq_refl.
Qed.

Lemma sc_cos_term_wd : forall (j : nat) (x y : Q), x == y -> cos_term j x == cos_term j y.
Proof.
  intros j x y Hxy.
  unfold cos_term, Qdiv.
  apply Qmult_comp.
  - apply Qeq_refl.
  - apply Qmult_comp.
    + apply (q_pow_wd x y (2 * j) Hxy).
    + apply Qeq_refl.
Qed.

Lemma sc_sin_partial_wd : forall (n : nat) (x y : Q), x == y ->
  sin_partial n x == sin_partial n y.
Proof.
  intros n x y Hxy.
  induction n as [| n IH]; simpl.
  - apply (sc_sin_term_wd 0 x y Hxy).
  - apply Qplus_comp.
    + exact IH.
    + apply (sc_sin_term_wd (Datatypes.S n) x y Hxy).
Qed.

Lemma sc_cos_partial_wd : forall (n : nat) (x y : Q), x == y ->
  cos_partial n x == cos_partial n y.
Proof.
  intros n x y Hxy.
  induction n as [| n IH]; simpl.
  - apply (sc_cos_term_wd 0 x y Hxy).
  - apply Qplus_comp.
    + exact IH.
    + apply (sc_cos_term_wd (Datatypes.S n) x y Hxy).
Qed.

#[global] Instance sc_sin_partial_morph (n : nat) : Proper (Qeq ==> Qeq) (sin_partial n).
Proof. intros x y Hxy. apply (sc_sin_partial_wd n x y Hxy). Qed.

#[global] Instance sc_cos_partial_morph (n : nat) : Proper (Qeq ==> Qeq) (cos_partial n).
Proof. intros x y Hxy. apply (sc_cos_partial_wd n x y Hxy). Qed.

(* ============ 批 B2 第 0 部分：Q 层共享点值链 ============ *)

(* |sn·An + cn·Bn| ≤ |sn||An| + |cn||Bn| 的三角+绝对值拆解 *)
Lemma sc_pair_sum_abs_le : forall (sn cn An Bn : Q),
  Qle (Qabs (Qplus (Qmult sn An) (Qmult cn Bn)))
      (Qplus (Qmult (Qabs sn) (Qabs An)) (Qmult (Qabs cn) (Qabs Bn))).
Proof.
  intros sn cn An Bn.
  assert (H1 : Qle (Qabs (Qplus (Qmult sn An) (Qmult cn Bn)))
                  (Qplus (Qabs (Qmult sn An)) (Qabs (Qmult cn Bn)))).
  { exact (Qabs_triangle (Qmult sn An) (Qmult cn Bn)). }
  apply (Qle_trans _ (Qplus (Qabs (Qmult sn An)) (Qabs (Qmult cn Bn))) _).
  - exact H1.
  - apply Qplus_le_compat.
    + apply qeq_le. rewrite (Qabs_Qmult sn An). reflexivity.
    + apply qeq_le. rewrite (Qabs_Qmult cn Bn). reflexivity.
Qed.

(* |a+b+c| ≤ |a|+|b|+|c|（右结合形式） *)
Lemma sc_abs_plus3_le : forall (a b c : Q),
  Qle (Qabs (Qplus a (Qplus b c))) (Qplus (Qabs a) (Qplus (Qabs b) (Qabs c))).
Proof.
  intros a b c.
  apply (Qle_trans _ (Qplus (Qabs a) (Qabs (Qplus b c))) _).
  - exact (Qabs_triangle a (Qplus b c)).
  - apply (Qle_trans _ (Qplus (Qabs a) (Qplus (Qabs b) (Qabs c))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (Qabs_triangle b c).
    + apply qeq_le. ring.
Qed.

(* 乘积绝对值拆：|P| ≤ Ms、|A| ≤ X ⟹ |P·A| ≤ Ms·X *)
Lemma sc_abs_prod_le : forall (P A Ms X : Q),
  Qle (Qabs P) Ms -> Qle (Qabs A) X ->
  Qle (Qabs (Qmult P A)) (Qmult Ms X).
Proof.
  intros P A Ms X HP HA.
  rewrite (Qabs_Qmult P A).
  apply (Qle_trans _ (Qmult Ms (Qabs A)) _).
  - apply (Qmult_le_compat_r (Qabs P) Ms (Qabs A) HP (Qabs_nonneg A)).
  - apply (sc_qmult_le_l_f1 Ms (Qabs A) X).
    + apply (Qle_trans 0 (Qabs P) Ms (Qabs_nonneg P) HP).
    + exact HA.
Qed.

(* |h| ≤ en·k 且 |h| ≤ 1 ⟹ |h|² ≤ (en·k)·1 的引理参数化 *)
Lemma sc_abs_sq_le_hk : forall (h en k : Q),
  Qle (Qabs h) (Qmult en k) -> Qle (Qabs h) 1 -> Qle 0 (Qmult en k) ->
  Qle (q_pow (Qabs h) 2) (Qmult (Qmult en k) (Qabs h)).
Proof.
  intros h en k HhE Hh1 Hk0.
  rewrite (sc_qpow2_form (Qabs h)).
  apply (Qle_trans _ (Qmult (Qmult en k) (Qabs h)) _).
  - apply (Qmult_le_compat_r (Qabs h) (Qmult en k) (Qabs h) HhE (Qabs_nonneg h)).
  - apply Qle_refl.
Qed.

(* |h| ≤ en·k 且 |h| ≤ 1 且 en·k ≥ 0 ⟹ |h|³ ≤ (en·k)·|h| *)
Lemma sc_abs_cube_le_hk : forall (h en k : Q),
  Qle (Qabs h) (Qmult en k) -> Qle (Qabs h) 1 -> Qle 0 (Qmult en k) ->
  Qle (q_pow (Qabs h) 3) (Qmult (Qmult en k) (Qabs h)).
Proof.
  intros h en k HhE Hh1 Hk0.
  rewrite (sc_qpow3_form (Qabs h)).
  (* |h|·(|h|·|h|)：|h|·|h| ≤ (en·k)·1，再乘 |h| *)
  assert (Hs : Qle (Qmult (Qabs h) (Qabs h)) (Qmult (Qmult en k) 1)).
  { apply (Qle_trans (Qmult (Qabs h) (Qabs h)) (Qmult (Qmult en k) (Qabs h))
                     (Qmult (Qmult en k) 1)).
    - apply (Qmult_le_compat_r (Qabs h) (Qmult en k) (Qabs h) HhE (Qabs_nonneg h)).
    - apply (sc_qmult_le_l_f1 (Qmult en k) (Qabs h) 1 Hk0). exact Hh1. }
  apply (Qle_trans _ (Qmult (Qabs h) (Qmult (Qabs h) (Qabs h))) _).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (Qmult (Qabs h) (Qmult (Qmult en k) 1)) _).
    + apply (sc_qmult_le_l_f1 (Qabs h) (Qmult (Qabs h) (Qabs h)) (Qmult (Qmult en k) 1) (Qabs_nonneg h)).
      exact Hs.
    + apply qeq_le. ring.
Qed.

(* Ms·(x·(en·k)) == (en·x)·(Ms·k) 组装目标（点值两项合计 ≤ (en·|h|)·(1#4)） *)
Lemma sc_pair_abs_le : forall (sn cn An Bn G en hn Ms Mc k : Q),
  Qle (Qabs sn) Ms -> Qle (Qabs cn) Mc ->
  Qle (Qabs An) (q_pow (Qabs hn) 2) ->
  Qle (Qabs Bn) (q_pow (Qabs hn) 3) ->
  Qle (Qabs G) (Qabs G) ->
  Qle (Qabs hn) 1 -> Qle (Qabs hn) (Qmult en k) ->
  Qle 0 en -> Qle 0 k ->
  Qle (Qmult Ms k) (1 # 8) -> Qle (Qmult Mc k) (1 # 8) ->
  Qle (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))
      (Qplus (Qabs G) (Qmult (Qmult en (Qabs hn)) (1 # 4))).
Proof.
  intros sn cn An Bn G en hn Ms Mc k
         Hsn Hcn HAn HBn HG Hh1 HhE Hen0 Hk0 HMsK HMcK.
  (* 三角拆解 *)
  apply (Qle_trans _ (Qplus (Qabs G) (Qabs (Qplus (Qmult sn An) (Qmult cn Bn)))) _).
  - exact (Qabs_triangle G (Qplus (Qmult sn An) (Qmult cn Bn))).
  - apply (Qle_trans _ (Qplus (Qabs G)
                     (Qplus (Qmult (Qabs sn) (Qabs An)) (Qmult (Qabs cn) (Qabs Bn)))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (sc_pair_sum_abs_le sn cn An Bn).
    + (* 两项各自收进 en·|h| 预算：1/8 + 1/8 = 1/4 *)
      apply (Qle_trans _ (Qplus (Qabs G)
                     (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 8))
                            (Qmult (Qmult en (Qabs hn)) (1 # 8)))) _).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply Qplus_le_compat.
           ++ (* |sn||An| ≤ en·|h|/8 *)
              assert (Hek0 : Qle 0 (Qmult en k)).
              { apply (Qmult_le_0_compat en k Hen0 Hk0). }
              apply (Qle_trans _ (Qmult Ms (Qabs An)) _).
              ** apply (Qmult_le_compat_r (Qabs sn) Ms (Qabs An) Hsn (Qabs_nonneg An)).
              ** apply (Qle_trans _ (Qmult Ms (q_pow (Qabs hn) 2)) _).
                 { apply (sc_qmult_le_l_f1 Ms (Qabs An) (q_pow (Qabs hn) 2)).
                   - apply (Qle_trans 0 (Qabs sn) Ms (Qabs_nonneg sn) Hsn).
                   - exact HAn. }
                 { apply (Qle_trans _ (Qmult Ms (Qmult (Qmult en k) (Qabs hn))) _).
                   - apply (sc_qmult_le_l_f1 Ms (q_pow (Qabs hn) 2) (Qmult (Qmult en k) (Qabs hn))).
                     + apply (Qle_trans 0 (Qabs sn) Ms (Qabs_nonneg sn) Hsn).
                     + apply (sc_abs_sq_le_hk hn en k HhE Hh1 Hek0).
                   - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Ms k)) _).
                     + apply qeq_le. ring.
                     + apply (sc_qmult_le_l_f1 (Qmult en (Qabs hn)) (Qmult Ms k) (1 # 8)).
                       * apply (Qmult_le_0_compat en (Qabs hn) Hen0 (Qabs_nonneg hn)).
                       * exact HMsK. }
           ++ (* |cn||Bn| ≤ en·|h|/8 *)
              assert (Hek0b : Qle 0 (Qmult en k)).
              { apply (Qmult_le_0_compat en k Hen0 Hk0). }
              apply (Qle_trans _ (Qmult Mc (Qabs Bn)) _).
              ** apply (Qmult_le_compat_r (Qabs cn) Mc (Qabs Bn) Hcn (Qabs_nonneg Bn)).
              ** apply (Qle_trans _ (Qmult Mc (q_pow (Qabs hn) 3)) _).
                 { apply (sc_qmult_le_l_f1 Mc (Qabs Bn) (q_pow (Qabs hn) 3)).
                   - apply (Qle_trans 0 (Qabs cn) Mc (Qabs_nonneg cn) Hcn).
                   - exact HBn. }
                 { apply (Qle_trans _ (Qmult Mc (Qmult (Qmult en k) (Qabs hn))) _).
                   - apply (sc_qmult_le_l_f1 Mc (q_pow (Qabs hn) 3) (Qmult (Qmult en k) (Qabs hn))).
                     + apply (Qle_trans 0 (Qabs cn) Mc (Qabs_nonneg cn) Hcn).
                     + apply (sc_abs_cube_le_hk hn en k HhE Hh1 Hek0b).
                   - apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Mc k)) _).
                     + apply qeq_le. ring.
                     + apply (sc_qmult_le_l_f1 (Qmult en (Qabs hn)) (Qmult Mc k) (1 # 8)).
                       * apply (Qmult_le_0_compat en (Qabs hn) Hen0 (Qabs_nonneg hn)).
                       * exact HMcK. }
      * apply qeq_le. ring.
Qed.

(* ============ 批 B2 第 1 部分：Real 层 sin 可微 ============ *)
(* 语句同构 real_exp_deriv_eq_self（根 L63005，205 实测），sin/cos 全域定义故          *)
(* 无 x>0 前提（设计 §4-R3）。证明：rs_add_sin（根 L64560）分解 D = G + sin x·A +     *)
(* cos x·B（A := cos h − 1、B := sin h − h），逐点 |P_n| ≤ M_s、|C_n| ≤ M_c 用       *)
(* real_norm_bounded，δ := min(1, eps·(1/(8(M_s+M_c+1))))，real_lt 见证 eps1'/2。   *)

(* 辅助：0 < c ⟹ 0 < real_const c *)
Lemma real_const_pos_f1 : forall c : Q, Qlt 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  exists (Qmult c (Qinv 2)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat c (Qinv 2)).
    + exact Hc.
    + apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 (real_const c) n - projT1 real_zero n == c)
      by (cbn [real_const real_zero projT1]; ring).
    rewrite Hz.
    apply (q_half_lt c Hc).
Qed.

(* k 不等式：Ms·inv(8(Ms+Mc+1)) ≤ 1/8 *)
Lemma sc_k_ineq_s : forall (Ms Mc : Q), Qlt 0 Ms -> Qlt 0 Mc ->
  Qle (Qmult Ms (Qinv (8 * (Ms + Mc + 1)))) (1 # 8).
Proof.
  intros Ms Mc HMs HMc.
  set (D := Ms + Mc + 1).
  assert (HD : Qlt 0 D).
  { unfold D.
    apply (Qlt_le_trans 0 1 (Ms + Mc + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (0 + 1) (Ms + Mc + 1)).
      + apply qeq_le. ring.
      + apply Qplus_le_compat.
        * apply (Qle_trans 0 Ms (Ms + Mc)).
          -- apply (Qlt_le_weak 0 Ms). exact HMs.
          -- apply Qle_plus_nonneg_r. apply (Qlt_le_weak 0 Mc). exact HMc.
        * apply Qle_refl. }
  assert (H8D : Qlt 0 (8 * D)).
  { apply (Qmult_lt_0_compat 8 D).
    - unfold Qlt. simpl. lia.
    - exact HD. }
  assert (HMsle : Qle Ms D).
  { unfold D.
    apply (Qle_trans Ms (Ms + 0) (Ms + Mc + 1)).
    - apply qeq_le. ring.
    - apply (Qle_trans (Ms + 0) (Ms + (Mc + 1)) (Ms + Mc + 1)).
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply (Qle_trans 0 Mc (Mc + 1)).
          -- apply (Qlt_le_weak 0 Mc). exact HMc.
          -- apply Qle_plus_nonneg_r. unfold Qle. simpl. lia.
      + apply qeq_le. ring. }
  assert (H8le : Qle (8 * Ms) (8 * D)).
  { apply (Qle_trans (8 * Ms) (Ms * 8) (8 * D)).
    - apply qeq_le. ring.
    - apply (Qle_trans (Ms * 8) (D * 8) (8 * D)).
      + apply (Qmult_le_compat_r Ms D 8 HMsle).
        unfold Qle. simpl. lia.
      + apply qeq_le. ring. }
  assert (Hconcl : Qle (Qdiv Ms (8 * D)) (Qdiv 1 8)).
  { apply (q_le_div_le Ms (8 * D) 1 8 H8D).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans (Ms * 8) (8 * Ms) (1 * (8 * D))).
      + apply qeq_le. ring.
      + apply (Qle_trans (8 * Ms) (8 * D) (1 * (8 * D))).
        * exact H8le.
        * apply qeq_le. ring. }
  apply (Qle_trans (Qmult Ms (Qinv (8 * D)))
                   (Qdiv Ms (8 * D))
                   (Qdiv 1 8)).
  - apply qeq_le. unfold Qdiv. reflexivity.
  - apply (Qle_trans (Qdiv Ms (8 * D)) (Qdiv 1 8) (1 # 8)).
    + exact Hconcl.
    + apply qeq_le. unfold Qdiv. field.
Qed.

(* k 不等式：Mc·inv(8(Ms+Mc+1)) ≤ 1/8（对称） *)
Lemma sc_k_ineq_c : forall (Ms Mc : Q), Qlt 0 Ms -> Qlt 0 Mc ->
  Qle (Qmult Mc (Qinv (8 * (Ms + Mc + 1)))) (1 # 8).
Proof.
  intros Ms Mc HMs HMc.
  set (D := Ms + Mc + 1).
  assert (HD : Qlt 0 D).
  { unfold D.
    apply (Qlt_le_trans 0 1 (Ms + Mc + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans 1 (0 + 1) (Ms + Mc + 1)).
      + apply qeq_le. ring.
      + apply Qplus_le_compat.
        * apply (Qle_trans 0 Mc (Ms + Mc)).
          -- apply (Qlt_le_weak 0 Mc). exact HMc.
          -- apply (Qle_trans Mc (Mc + Ms) (Ms + Mc)).
             ++ apply Qle_plus_nonneg_r. apply (Qlt_le_weak 0 Ms). exact HMs.
             ++ apply qeq_le. ring.
        * apply Qle_refl. }
  assert (H8D : Qlt 0 (8 * D)).
  { apply (Qmult_lt_0_compat 8 D).
    - unfold Qlt. simpl. lia.
    - exact HD. }
  assert (HMcle : Qle Mc D).
  { unfold D.
    apply (proj2 (Qle_minus_iff Mc (Ms + Mc + 1))).
    assert (Heq : Qminus (Ms + Mc + 1) Mc == Qplus Ms 1) by ring.
    rewrite Heq.
    apply (Qle_trans 0 Ms (Ms + 1)).
    - apply (Qlt_le_weak 0 Ms). exact HMs.
    - apply Qle_plus_nonneg_r. unfold Qle. simpl. lia. }
  assert (H8le : Qle (8 * Mc) (8 * D)).
  { apply (Qle_trans (8 * Mc) (Mc * 8) (8 * D)).
    - apply qeq_le. ring.
    - apply (Qle_trans (Mc * 8) (D * 8) (8 * D)).
      + apply (Qmult_le_compat_r Mc D 8 HMcle).
        unfold Qle. simpl. lia.
      + apply qeq_le. ring. }
  assert (Hconcl : Qle (Qdiv Mc (8 * D)) (Qdiv 1 8)).
  { apply (q_le_div_le Mc (8 * D) 1 8 H8D).
    - unfold Qlt. simpl. lia.
    - apply (Qle_trans (Mc * 8) (8 * Mc) (1 * (8 * D))).
      + apply qeq_le. ring.
      + apply (Qle_trans (8 * Mc) (8 * D) (1 * (8 * D))).
        * exact H8le.
        * apply qeq_le. ring. }
  apply (Qle_trans (Qmult Mc (Qinv (8 * D)))
                   (Qdiv Mc (8 * D))
                   (Qdiv 1 8)).
  - apply qeq_le. unfold Qdiv. reflexivity.
  - apply (Qle_trans (Qdiv Mc (8 * D)) (Qdiv 1 8) (1 # 8)).
    + exact Hconcl.
    + apply qeq_le. unfold Qdiv. field.
Qed.

(* ---- 主定理：sin 可微（Bishop 显式，导数 = cos x） ---- *)
Lemma real_sin_deriv_linear : forall (x : Real), forall (eps : Real),
  real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                     (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
Proof.
  intros x eps Heps.
  destruct (real_norm_bounded (cauchy_real_sin x)) as [Ms [HMs_pos HMs]].
  destruct (real_norm_bounded (cauchy_real_cos x)) as [Mc [HMc_pos HMc]].
  set (k := Qinv (8 * (Ms + Mc + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k.
    apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 8 (Ms + Mc + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Ms + Mc + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Ms + Mc + 1)).
        * apply qeq_le. ring.
        * apply Qplus_le_compat.
          -- apply (Qle_trans 0 Ms (Ms + Mc)).
             ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs_pos.
             ++ apply Qle_plus_nonneg_r. apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc_pos.
          -- apply Qle_refl. }
  assert (Hk_posT : QltT 0 k) by (apply Qlt_to_QltT; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  assert (HMsK : Qle (Qmult Ms k) (1 # 8)).
  { unfold k. apply (sc_k_ineq_s Ms Mc).
    - apply QltT_to_Qlt. exact HMs_pos.
    - apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMcK : Qle (Qmult Mc k) (1 # 8)).
  { unfold k. apply (sc_k_ineq_c Ms Mc).
    - apply QltT_to_Qlt. exact HMs_pos.
    - apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMs0 : Qle 0 Ms) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HMs_pos).
  assert (HMc0 : Qle 0 Mc) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HMc_pos).
  (* delta := min(1, eps·k) *)
  set (delta := real_min (real_const 1) (real_mult eps rk)).
  exists delta.
  split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1. unfold Qlt. simpl. lia.
    + apply real_mult_positive.
      * exact Heps.
      * exact Hrk_pos.
  - intros h Hh eps' Heps'.
    assert (Hh_one : real_lt (real_abs h) (real_const 1))
      by (unfold delta in Hh; unfold rk in Hh; apply (real_min_lt_l h (real_const 1) (real_mult eps (real_const k))); exact Hh).
    assert (Hh_k : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; unfold rk in Hh; apply (real_min_lt_r h (real_const 1) (real_mult eps (real_const k))); exact Hh).
    (* real_le 左分支：见证 eps1'/2 *)
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    destruct Hh_one as [eps2 [Heps2 [N2 HN2]]].
    destruct Hh_k as [eps3 [Heps3 [N3 HN3]]].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta.
      apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    (* rs_add_sin 逐点误差 |G_n| < eps1'/2 *)
    assert (HepsG_pos : QltT 0 (Qmult eps1' (Qinv 2))).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (rs_add_sin x h (Qmult eps1' (Qinv 2)) HepsG_pos) as [NG HG].
    exists eta.
    split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) NG) 0).
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (hn := projT1 h n). set (xn := projT1 x n).
      set (sn := sin_partial n xn). set (cn := cos_partial n xn).
      set (ch := cos_partial n hn). set (sh := sin_partial n hn).
      set (An := ch - 1). set (Bn := sh - hn).
      set (L := projT1 (cauchy_real_sin (real_plus x h)) n).
      set (R := projT1 (real_plus (real_mult (cauchy_real_sin x) (cauchy_real_cos h))
                                  (real_mult (cauchy_real_cos x) (cauchy_real_sin h))) n).
      set (G := L - R).
      (* 逐点主分解恒等式：D_n == G + sn·An + cn·Bn *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                  (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h))))) n ==
                      Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))).
      { subst G An Bn sn cn ch sh L R.
        setoid_rewrite (real_abs_proj (real_plus (cauchy_real_sin (real_plus x h))
                  (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h)))) n).
        setoid_rewrite (real_plus_proj (cauchy_real_sin (real_plus x h))
                  (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h))) n).
        setoid_rewrite (real_opp_proj (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h)) n).
        setoid_rewrite (real_plus_proj (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h) n).
        setoid_rewrite (real_mult_proj (cauchy_real_cos x) h n).
        (* rs_add_sin 右侧 R 的 plus 与两个乘积的外层投影 *)
        setoid_rewrite (real_plus_proj (real_mult (cauchy_real_sin x) (cauchy_real_cos h))
                                       (real_mult (cauchy_real_cos x) (cauchy_real_sin h)) n).
        setoid_rewrite (real_mult_proj (cauchy_real_sin x) (cauchy_real_cos h) n).
        setoid_rewrite (real_mult_proj (cauchy_real_cos x) (cauchy_real_sin h) n).
        setoid_rewrite (real_sin_proj x n).
        setoid_rewrite (real_cos_proj h n).
        setoid_rewrite (real_cos_proj x n).
        setoid_rewrite (real_sin_proj h n).
        setoid_rewrite (real_sin_proj (real_plus x h) n).
        setoid_rewrite (real_plus_proj x h n).
        cbn [projT1].
        unfold Qminus.
        unfold xn, hn.
        apply Qabs_wd.
        ring. }
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [projT1]. ring. }
      (* 逐点界 1：|hn| ≤ 1（Hh_one 见证） *)
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (HnG : (NG <= n)%nat) by lia.
      assert (HN2q : Qlt eps2 (Qminus 1 (Qabs hn))).
      { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const 1) n) (projT1 (real_abs h) n)) (Qminus 1 (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          cbn [real_const projT1].
          reflexivity. }
      assert (Hhn_one : Qlt (Qabs hn) 1).
      { apply (Qlt_le_trans (Qabs hn) (Qminus 1 eps2) 1).
        - apply (q_lt_minus_shift eps2 1 (Qabs hn)). exact HN2q.
        - assert (Heps2q : Qle 0 eps2).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
          apply (Qle_trans (Qminus 1 eps2) (Qplus (Qminus 1 eps2) eps2) 1).
          + apply (Qle_trans (Qminus 1 eps2) (Qplus (Qminus 1 eps2) 0) (Qplus (Qminus 1 eps2) eps2)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus 1 eps2) (Qminus 1 eps2) 0 eps2 (Qle_refl _) Heps2q).
          + apply qeq_le. ring. }
      assert (Hhn_le1 : Qle (Qabs hn) 1) by (apply Qlt_le_weak; exact Hhn_one).
      (* 逐点界 2：|hn| ≤ en·k（Hh_k 见证 + rk 投影） *)
      assert (HN3q : Qlt eps3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                                (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold rk, en.
          setoid_rewrite (real_mult_proj eps (real_const k) n).
          cbn [real_const projT1].
          reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) eps3) (Qmult en k)).
        - apply (q_lt_minus_shift eps3 (Qmult en k) (Qabs hn)). exact HN3q.
        - assert (Heps3q : Qle 0 eps3).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
          apply (Qle_trans (Qminus (Qmult en k) eps3)
                           (Qplus (Qminus (Qmult en k) eps3) eps3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) eps3)
                             (Qplus (Qminus (Qmult en k) eps3) 0)
                             (Qplus (Qminus (Qmult en k) eps3) eps3)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) eps3)
                                     (Qminus (Qmult en k) eps3) 0 eps3 (Qle_refl _) Heps3q).
          + apply qeq_le. ring. }
      assert (Hhn_leE : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* 正性：en > 0、en' > eps1' *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (Heps1e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* |G_n| < eps1'/2 *)
      assert (HGlt : Qlt (Qabs G) (Qmult eps1' (Qinv 2))).
      { unfold G.
        apply QltT_to_Qlt.
        apply (HG n (NatLe_lift _ _ HnG)). }
      (* |sn| ≤ Ms、|cn| ≤ Mc（全 n） *)
      assert (Hsn_le : Qle (Qabs sn) Ms).
      { unfold sn.
        apply (Qle_trans (Qabs (sin_partial n (projT1 x n)))
                         (Qabs (projT1 (cauchy_real_sin x) n))
                         Ms).
        - apply qeq_le. apply Qabs_wd. apply Qeq_sym. exact (real_sin_proj x n).
        - apply (QleT'_to_Qle (Qabs (projT1 (cauchy_real_sin x) n)) Ms).
          exact (HMs n). }
      assert (Hcn_le : Qle (Qabs cn) Mc).
      { unfold cn.
        apply (Qle_trans (Qabs (cos_partial n (projT1 x n)))
                         (Qabs (projT1 (cauchy_real_cos x) n))
                         Mc).
        - apply qeq_le. apply Qabs_wd. apply Qeq_sym. exact (real_cos_proj x n).
        - apply (QleT'_to_Qle (Qabs (projT1 (cauchy_real_cos x) n)) Mc).
          exact (HMc n). }
      (* |An| ≤ |hn|²、|Bn| ≤ |hn|³ *)
      assert (HAn_le : Qle (Qabs An) (q_pow (Qabs hn) 2)).
      { unfold An.
        apply (sc_cos_sq_bound_c1 n hn Hhn_le1). }
      assert (HBn_le : Qle (Qabs Bn) (q_pow (Qabs hn) 3)).
      { unfold Bn.
        apply (sc_sin_cube_bound_c1 n hn Hhn_le1). }
      (* 主点值界：|D_n| ≤ |G_n| + (en·|hn|)/4 *)
      assert (Hmain : Qle (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))
                          (Qplus (Qabs G) (Qmult (Qmult en (Qabs hn)) (1 # 4)))).
      { apply (sc_pair_abs_le sn cn An Bn G en hn Ms Mc k).
        - exact Hsn_le.
        - exact Hcn_le.
        - exact HAn_le.
        - exact HBn_le.
        - apply Qle_refl.
        - exact Hhn_le1.
        - exact Hhn_leE.
        - exact Hen0.
        - apply Qlt_le_weak. exact Hk_pos.
        - exact HMsK.
        - exact HMcK. }
      (* 组装：eta < B_n − A_n（eta := eps1'/2；|G| < eps1'/2、en' > eps1'） *)
      assert (Hq4 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
        - apply (sc_qmult_le_l_f1 (Qmult en (Qabs hn)) (1 # 4) 1%Q).
          + apply (Qmult_le_0_compat en (Qabs hn) Hen0 (Qabs_nonneg hn)).
          + unfold Qle. simpl. lia.
        - apply qeq_le. ring. }
      assert (HGhalf : Qle (Qabs G) (Qmult eps1' (Qinv 2)))
        by (apply Qlt_le_weak; exact HGlt).
      assert (HDbound : Qle (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))
                            (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))).
      { apply (Qle_trans _ (Qplus (Qabs G) (Qmult (Qmult en (Qabs hn)) (1 # 4))) _).
        - exact Hmain.
        - apply (Qle_trans _ (Qplus (Qmult eps1' (Qinv 2)) (Qmult (Qmult en (Qabs hn)) (1 # 4))) _).
          + apply Qplus_le_compat.
            * exact HGhalf.
            * apply Qle_refl.
          + apply (Qle_trans _ (Qplus (Qmult eps1' (Qinv 2)) (Qmult en (Qabs hn))) _).
            * apply Qplus_le_compat.
              -- apply Qle_refl.
              -- exact Hq4.
            * apply qeq_le. ring. }
      (* 与 real_abs 目标衔接 *)
      assert (Hrepl2 : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                   (projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                                 (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h))))) n))
                           (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                                 (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h))))) n)
                           (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))) Hrepl). }
      (* eta < en' − eta（en' > eps1' == 2·eta）——Hfin 内嵌 *)
      assert (Hfin : Qlt (Qmult eps1' (Qinv 2))
                         (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))))).
      { apply (Qlt_le_trans (Qmult eps1' (Qinv 2))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))))).
        - apply (proj2 (Qlt_minus_iff (Qmult eps1' (Qinv 2))
                                      (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))))).
          assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                                (Qmult eps1' (Qinv 2)) ==
                        Qminus en' (Qmult (Qmult eps1' (Qinv 2)) (1 + 1))) by ring.
          rewrite Heq.
          apply (proj1 (Qlt_minus_iff (Qmult (Qmult eps1' (Qinv 2)) (1 + 1)) en')).
          assert (HX : Qmult (Qmult eps1' (Qinv 2)) (1 + 1) == eps1') by field.
          rewrite HX.
          apply QltT_to_Qlt. exact Heps1e.
        - apply (proj2 (Qle_minus_iff
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))))).
          assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))))
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))
                                 (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn))))
                                      (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))).
          exact HDbound. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (Qmult eps1' (Qinv 2))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult sn An) (Qmult cn Bn)))))
                          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                                            (real_opp (real_plus (cauchy_real_sin x) (real_mult (cauchy_real_cos x) h))))) n))).
      { exact Hfin. }
      { apply qeq_le. apply Qeq_sym. exact Hrepl2. }
Qed.

(* ---- 主定理：cos 可微（Bishop 显式，导数 = −sin x） ---- *)
Lemma real_cos_deriv_linear : forall (x : Real), forall (eps : Real),
  real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall h : Real, real_lt (real_abs h) delta ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                     (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
Proof.
  intros x eps Heps.
  destruct (real_norm_bounded (cauchy_real_sin x)) as [Ms [HMs_pos HMs]].
  destruct (real_norm_bounded (cauchy_real_cos x)) as [Mc [HMc_pos HMc]].
  set (k := Qinv (8 * (Ms + Mc + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k.
    apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 8 (Ms + Mc + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Ms + Mc + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Ms + Mc + 1)).
        * apply qeq_le. ring.
        * apply Qplus_le_compat.
          -- apply (Qle_trans 0 Ms (Ms + Mc)).
             ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact HMs_pos.
             ++ apply Qle_plus_nonneg_r. apply Qlt_le_weak. apply QltT_to_Qlt. exact HMc_pos.
          -- apply Qle_refl. }
  assert (Hk_posT : QltT 0 k) by (apply Qlt_to_QltT; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  assert (HMsK : Qle (Qmult Ms k) (1 # 8)).
  { unfold k. apply (sc_k_ineq_s Ms Mc).
    - apply QltT_to_Qlt. exact HMs_pos.
    - apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMcK : Qle (Qmult Mc k) (1 # 8)).
  { unfold k. apply (sc_k_ineq_c Ms Mc).
    - apply QltT_to_Qlt. exact HMs_pos.
    - apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMs0 : Qle 0 Ms) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HMs_pos).
  assert (HMc0 : Qle 0 Mc) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HMc_pos).
  (* delta := min(1, eps·k) *)
  set (delta := real_min (real_const 1) (real_mult eps rk)).
  exists delta.
  split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1. unfold Qlt. simpl. lia.
    + apply real_mult_positive.
      * exact Heps.
      * exact Hrk_pos.
  - intros h Hh eps' Heps'.
    assert (Hh_one : real_lt (real_abs h) (real_const 1))
      by (unfold delta in Hh; unfold rk in Hh; apply (real_min_lt_l h (real_const 1) (real_mult eps (real_const k))); exact Hh).
    assert (Hh_k : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; unfold rk in Hh; apply (real_min_lt_r h (real_const 1) (real_mult eps (real_const k))); exact Hh).
    (* real_le 左分支：见证 eps1'/2 *)
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    destruct Hh_one as [eps2 [Heps2 [N2 HN2]]].
    destruct Hh_k as [eps3 [Heps3 [N3 HN3]]].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta.
      apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    (* rs_add_sin 逐点误差 |G_n| < eps1'/2 *)
    assert (HepsG_pos : QltT 0 (Qmult eps1' (Qinv 2))).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (rs_add_cos x h (Qmult eps1' (Qinv 2)) HepsG_pos) as [NG HG].
    exists eta.
    split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) NG) 0).
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (hn := projT1 h n). set (xn := projT1 x n).
      set (sn := sin_partial n xn). set (cn := cos_partial n xn).
      set (ch := cos_partial n hn). set (sh := sin_partial n hn).
      set (An := ch - 1). set (Bn := sh - hn).
      set (L := projT1 (cauchy_real_cos (real_plus x h)) n).
  set (R := projT1 (real_plus (real_mult (cauchy_real_cos x) (cauchy_real_cos h))
                                  (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin h)))) n).
      set (G := L - R).
      (* 逐点主分解恒等式：D_n == G + sn·An + cn·Bn *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                  (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)))))) n ==
                      Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))).
      { subst G An Bn sn cn ch sh L R.
        setoid_rewrite (real_abs_proj (real_plus (cauchy_real_cos (real_plus x h))
                  (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h))))) n).
        setoid_rewrite (real_plus_proj (cauchy_real_cos (real_plus x h))
                  (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)))) n).
        setoid_rewrite (real_opp_proj (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h))) n).
        setoid_rewrite (real_plus_proj (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)) n).
        setoid_rewrite (real_opp_proj (real_mult (cauchy_real_sin x) h) n).
        setoid_rewrite (real_mult_proj (cauchy_real_sin x) h n).
        (* rs_add_sin 右侧 R 的 plus 与两个乘积的外层投影 *)
        setoid_rewrite (real_plus_proj (real_mult (cauchy_real_cos x) (cauchy_real_cos h))
                                       (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin h))) n).
        setoid_rewrite (real_opp_proj (real_mult (cauchy_real_sin x) (cauchy_real_sin h)) n).
        setoid_rewrite (real_mult_proj (cauchy_real_cos x) (cauchy_real_cos h) n).
        setoid_rewrite (real_mult_proj (cauchy_real_sin x) (cauchy_real_sin h) n).
        setoid_rewrite (real_sin_proj x n).
        setoid_rewrite (real_cos_proj h n).
        setoid_rewrite (real_cos_proj x n).
        setoid_rewrite (real_sin_proj h n).
        setoid_rewrite (real_cos_proj (real_plus x h) n).
        setoid_rewrite (real_plus_proj x h n).
        cbn [projT1].
        unfold Qminus.
        unfold xn, hn.
        apply Qabs_wd.
        ring. }
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [projT1]. ring. }
      (* 逐点界 1：|hn| ≤ 1（Hh_one 见证） *)
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (HnG : (NG <= n)%nat) by lia.
      assert (HN2q : Qlt eps2 (Qminus 1 (Qabs hn))).
      { apply (Qlt_le_trans eps2 (Qminus (projT1 (real_const 1) n) (projT1 (real_abs h) n)) (Qminus 1 (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          cbn [real_const projT1].
          reflexivity. }
      assert (Hhn_one : Qlt (Qabs hn) 1).
      { apply (Qlt_le_trans (Qabs hn) (Qminus 1 eps2) 1).
        - apply (q_lt_minus_shift eps2 1 (Qabs hn)). exact HN2q.
        - assert (Heps2q : Qle 0 eps2).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps2. }
          apply (Qle_trans (Qminus 1 eps2) (Qplus (Qminus 1 eps2) eps2) 1).
          + apply (Qle_trans (Qminus 1 eps2) (Qplus (Qminus 1 eps2) 0) (Qplus (Qminus 1 eps2) eps2)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus 1 eps2) (Qminus 1 eps2) 0 eps2 (Qle_refl _) Heps2q).
          + apply qeq_le. ring. }
      assert (Hhn_le1 : Qle (Qabs hn) 1) by (apply Qlt_le_weak; exact Hhn_one).
      (* 逐点界 2：|hn| ≤ en·k（Hh_k 见证 + rk 投影） *)
      assert (HN3q : Qlt eps3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans eps3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                                (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. exact (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_le.
          rewrite (real_abs_proj h n).
          unfold rk, en.
          setoid_rewrite (real_mult_proj eps (real_const k) n).
          cbn [real_const projT1].
          reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) eps3) (Qmult en k)).
        - apply (q_lt_minus_shift eps3 (Qmult en k) (Qabs hn)). exact HN3q.
        - assert (Heps3q : Qle 0 eps3).
          { apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps3. }
          apply (Qle_trans (Qminus (Qmult en k) eps3)
                           (Qplus (Qminus (Qmult en k) eps3) eps3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) eps3)
                             (Qplus (Qminus (Qmult en k) eps3) 0)
                             (Qplus (Qminus (Qmult en k) eps3) eps3)).
            * apply qeq_le. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) eps3)
                                     (Qminus (Qmult en k) eps3) 0 eps3 (Qle_refl _) Heps3q).
          + apply qeq_le. ring. }
      assert (Hhn_leE : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* 正性：en > 0、en' > eps1' *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (Heps1e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_le. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* |G_n| < eps1'/2 *)
      assert (HGlt : Qlt (Qabs G) (Qmult eps1' (Qinv 2))).
      { unfold G.
        apply QltT_to_Qlt.
        apply (HG n (NatLe_lift _ _ HnG)). }
      (* |sn| ≤ Ms、|cn| ≤ Mc（全 n） *)
      assert (Hsn_le : Qle (Qabs sn) Ms).
      { unfold sn.
        apply (Qle_trans (Qabs (sin_partial n (projT1 x n)))
                         (Qabs (projT1 (cauchy_real_sin x) n))
                         Ms).
        - apply qeq_le. apply Qabs_wd. apply Qeq_sym. exact (real_sin_proj x n).
        - apply (QleT'_to_Qle (Qabs (projT1 (cauchy_real_sin x) n)) Ms).
          exact (HMs n). }
      assert (Hcn_le : Qle (Qabs cn) Mc).
      { unfold cn.
        apply (Qle_trans (Qabs (cos_partial n (projT1 x n)))
                         (Qabs (projT1 (cauchy_real_cos x) n))
                         Mc).
        - apply qeq_le. apply Qabs_wd. apply Qeq_sym. exact (real_cos_proj x n).
        - apply (QleT'_to_Qle (Qabs (projT1 (cauchy_real_cos x) n)) Mc).
          exact (HMc n). }
      assert (Hnsn_le : Qle (Qabs (- sn)) Ms).
      { apply (Qle_trans (Qabs (- sn)) (Qabs sn) Ms).
        - apply qeq_le. apply Qabs_opp.
        - exact Hsn_le. }
      (* |An| ≤ |hn|²、|Bn| ≤ |hn|³ *)
      assert (HAn_le : Qle (Qabs An) (q_pow (Qabs hn) 2)).
      { unfold An.
        apply (sc_cos_sq_bound_c1 n hn Hhn_le1). }
      assert (HBn_le : Qle (Qabs Bn) (q_pow (Qabs hn) 3)).
      { unfold Bn.
        apply (sc_sin_cube_bound_c1 n hn Hhn_le1). }
      (* 主点值界：|D_n| ≤ |G_n| + (en·|hn|)/4 *)
      assert (Hmain : Qle (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn))))
                          (Qplus (Qabs G) (Qmult (Qmult en (Qabs hn)) (1 # 4)))).
      { apply (sc_pair_abs_le cn (- sn) An Bn G en hn Mc Ms k).
        - exact Hcn_le.
        - exact Hnsn_le.
        - exact HAn_le.
        - exact HBn_le.
        - apply Qle_refl.
        - exact Hhn_le1.
        - exact Hhn_leE.
        - exact Hen0.
        - apply Qlt_le_weak. exact Hk_pos.
        - exact HMcK.
        - exact HMsK. }
      (* 组装：eta < B_n − A_n（eta := eps1'/2；|G| < eps1'/2、en' > eps1'） *)
      assert (Hq4 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
        - apply (sc_qmult_le_l_f1 (Qmult en (Qabs hn)) (1 # 4) 1%Q).
          + apply (Qmult_le_0_compat en (Qabs hn) Hen0 (Qabs_nonneg hn)).
          + unfold Qle. simpl. lia.
        - apply qeq_le. ring. }
      assert (HGhalf : Qle (Qabs G) (Qmult eps1' (Qinv 2)))
        by (apply Qlt_le_weak; exact HGlt).
      assert (HDbound : Qle (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn))))
                            (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))).
      { apply (Qle_trans _ (Qplus (Qabs G) (Qmult (Qmult en (Qabs hn)) (1 # 4))) _).
        - exact Hmain.
        - apply (Qle_trans _ (Qplus (Qmult eps1' (Qinv 2)) (Qmult (Qmult en (Qabs hn)) (1 # 4))) _).
          + apply Qplus_le_compat.
            * exact HGhalf.
            * apply Qle_refl.
          + apply (Qle_trans _ (Qplus (Qmult eps1' (Qinv 2)) (Qmult en (Qabs hn))) _).
            * apply Qplus_le_compat.
              -- apply Qle_refl.
              -- exact Hq4.
            * apply qeq_le. ring. }
      (* 与 real_abs 目标衔接 *)
      assert (Hrepl2 : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                   (projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                                 (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)))))) n))
                           (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                                 (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)))))) n)
                           (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))) Hrepl). }
      (* eta < en' − eta（en' > eps1' == 2·eta）——Hfin 内嵌 *)
      assert (Hfin : Qlt (Qmult eps1' (Qinv 2))
                         (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))))).
      { apply (Qlt_le_trans (Qmult eps1' (Qinv 2))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                            (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))))).
        - apply (proj2 (Qlt_minus_iff (Qmult eps1' (Qinv 2))
                                      (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))))).
          assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                                (Qmult eps1' (Qinv 2)) ==
                        Qminus en' (Qmult (Qmult eps1' (Qinv 2)) (1 + 1))) by ring.
          rewrite Heq.
          apply (proj1 (Qlt_minus_iff (Qmult (Qmult eps1' (Qinv 2)) (1 + 1)) en')).
          assert (HX : Qmult (Qmult eps1' (Qinv 2)) (1 + 1) == eps1') by field.
          rewrite HX.
          apply QltT_to_Qlt. exact Heps1e.
        - apply (proj2 (Qle_minus_iff
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn))))))).
          assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))))
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2)))
                                 (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn))))) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn))))
                                      (Qplus (Qmult en (Qabs hn)) (Qmult eps1' (Qinv 2))))).
          exact HDbound. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (Qmult eps1' (Qinv 2))
                          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs (Qplus G (Qplus (Qmult cn An) (Qmult (- sn) Bn)))))
                          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                                            (real_opp (real_plus (cauchy_real_cos x) (real_opp (real_mult (cauchy_real_sin x) h)))))) n))).
      { exact Hfin. }
      { apply qeq_le. apply Qeq_sym. exact Hrepl2. }
Qed.

(* ============================================================ *)
(* T-pi3 B3a 阶段并入（迭代 208）：arctan 导数 Q 层引擎        *)
(* 来源：sc2_b3_arctanp（20 Qed）；零公理面。                     *)
(* ============================================================ *)

Open Scope Q_scope.


(* ============================================================ *)
(* Q 层第 1 部分：几何部分和（−(x·x) 的幂）定义 + 幂恒等          *)
(* b3_dsum n x == Σ_{k=0}^{n} (−1)^k x^{2k} == Σ (−(x·x))^k       *)
(* ============================================================ *)
Fixpoint b3_dsum (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => 1
  | Datatypes.S m => b3_dsum m x + q_pow (- (x * x)) (Datatypes.S m)
  end.

(* 递归展开件（与 Fixpoint 定义同构，便于 rewrite） *)
Lemma b3_dsum_succ : forall (n : nat) (x : Q),
  b3_dsum (Datatypes.S n) x == b3_dsum n x + q_pow (- (x * x)) (Datatypes.S n).
Proof. intros. reflexivity. Qed.

(* (−1)^{2k} == 1 / (−1)^{2k+1} == −1（根 q_pow_neg1_even/odd 复用） *)
Lemma b3_sign_even : forall (k : nat), q_pow (-1) (2 * k) == 1.
Proof. exact q_pow_neg1_even. Qed.

Lemma b3_sign_odd : forall (k : nat), q_pow (-1) (2 * k + 1) == -1.
Proof. exact q_pow_neg1_odd. Qed.

(* (−(x·x))^p == (−1)^p · (x·x)^p *)
Lemma b3_pow_neg_sq : forall (x : Q) (p : nat),
  q_pow (- (x * x)) p == q_pow (-1) p * q_pow (x * x) p.
Proof.
  intros x p. induction p as [| p IH]; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.

(* (x·x)^p == x^{2p} *)
Lemma b3_pow_sq : forall (x : Q) (p : nat),
  q_pow (x * x) p == q_pow x (2 * p).
Proof.
  intros x p. induction p as [| p IH].
  - simpl. ring.
  - rewrite (q_pow_succ (x * x) p).
    rewrite IH.
    assert (Hnat : (2 * Datatypes.S p)%nat = (2 * p + 2)%nat) by lia.
    rewrite Hnat.
    rewrite (atan_q_pow_add x (2 * p) 2).
    assert (H2 : q_pow x 2 == x * x).
    { simpl. ring. }
    rewrite H2. ring.
Qed.

(* x^{2p} == (x·x)^p（b3_pow_sq 反向） *)
Lemma b3_even_pow : forall (x : Q) (p : nat),
  q_pow x (2 * p) == q_pow (x * x) p.
Proof. intros x p. apply Qeq_sym. apply b3_pow_sq. Qed.

(* |x·x| == x·x（平方非负 Qsquare_nonneg + Qabs_pos） *)
Lemma b3_abs_sq : forall (x : Q), Qabs (x * x) == x * x.
Proof.
  intros x.
  (* 绝对值定义体直落（分子绝对整面）：商展开、平方项投影归约至整数层，
     分子绝对值等式以线性算术非负见证装配，环等式闭合——不经绝对值
     正性桥单跳、不取用平方非负姊妹件。 *)
  unfold Qabs.
  destruct x as [n d].
  simpl.
  unfold Qeq. simpl.
  assert (Habs : (Z.abs (n * n) = n * n)%Z).
  { apply Z.abs_eq. nia. }
  rewrite Habs. ring.
Qed.

(* |(−(x·x))^p| == |x|^{2p}（(a) 余项引擎核心：幂模 + 负号消去） *)
Lemma b3_abs_pow_neg_sq : forall (x : Q) (p : nat),
  Qabs (q_pow (- (x * x)) p) == q_pow (Qabs x) (2 * p).
Proof.
  intros x p.
  rewrite (q_pow_abs (- (x * x)) p).
  (* |(−(x·x))| == x·x：Qabs_opp + |x·x| == x·x *)
  assert (Hba : Qabs (- (x * x)) == x * x).
  { rewrite (Qabs_opp (x * x)). apply (b3_abs_sq x). }
  rewrite (q_pow_wd (Qabs (- (x * x))) (x * x) p Hba).
  (* x·x == |x|·|x|（atan_sq_abs 方向为 x·x == |x|·|x|），再 b3_pow_sq at |x| *)
  assert (Hsq : x * x == Qabs x * Qabs x).
  { exact (atan_sq_abs x). }
  rewrite (q_pow_wd (x * x) (Qabs x * Qabs x) p Hsq).
  exact (b3_pow_sq (Qabs x) p).
Qed.


(* ============================================================ *)
(* Q 层第 2 部分：b3_dsum 几何闭式 + 余项 (a)                    *)
(* 闭式：(1+x²)·b3_dsum n x == 1 − (−x²)^{n+1}                  *)
(* 余项：|b3_dsum n x − Qinv(1+x²)| == |x|^{2n+2}·Qinv(1+x²)     *)
(*        ≤ |x|^{2n+2}（|x|≤1/2 时 ≤ (1/2)^{2n+2} = 4^{-(n+1)}） *)
(* ============================================================ *)

(* 辅助：0 < 1（用 Qle_0_1 + Qlt_le_weak 构造） *)
Lemma b3_lt_0_1 : Qlt 0 1.
Proof.
  apply (Qlt_le_trans 0 (1 / 2) 1).
  - unfold Qlt; simpl; lia.
  - unfold Qle; simpl; lia.
Qed.

(* 0 < 1 + x·x（1+x² ≥ 1 > 0） *)
Lemma b3_one_plus_sq_pos : forall x : Q, Qlt 0 (1 + x * x).
Proof.
  intros x.
  apply (Qlt_le_trans 0 1 (1 + x * x)).
  - exact b3_lt_0_1.
  - apply (Qle_trans 1 (1 + 0) (1 + x * x)).
    + apply qeq_le. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (Qsquare_nonneg x).
Qed.

(* 1 + x·x ≠ 0 *)
Lemma b3_one_plus_sq_neq : forall x : Q, ~ (1 + x * x == 0).
Proof.
  intros x Heq.
  (* 结构性推导（平方非负面相遇）：由零等式环换算出平方为负一的显式
     中立见证，与平方非负面在序定义体（整数层）相遇相抵——不经非等
     换形桥、不取用姊妹正性件。 *)
  assert (Hs : x * x == (1 + x * x) - 1) by ring.
  rewrite Heq in Hs.
  assert (Hsn : x * x == - 1) by (rewrite Hs; ring).
  pose proof (Qsquare_nonneg x) as Hle.
  rewrite Hsn in Hle.
  unfold Qle in Hle. simpl in Hle. lia.
Qed.

(* Qinv·denom == 1 / denom·Qinv == 1（分母正，非零） *)
Lemma b3_inv_sq_r : forall x : Q, (1 + x * x) * Qinv (1 + x * x) == 1.
Proof.
  intros x.
  (* 独立非零装配：平方非负面＋环换算就地构造非零见证，再入逆元
     反映面闭合——不取用姊妹非零件（其证明独立于本件成立）。 *)
  assert (Hnz : ~ (1 + x * x == 0)).
  { intro Heq.
    assert (Hs : x * x == (1 + x * x) - 1) by ring.
    rewrite Heq in Hs.
    assert (Hsn : x * x == - 1) by (rewrite Hs; ring).
    pose proof (Qsquare_nonneg x) as Hle.
    rewrite Hsn in Hle.
    unfold Qle in Hle. simpl in Hle. lia. }
  apply (Qmult_inv_r (1 + x * x)). exact Hnz.
Qed.

Lemma b3_inv_sq_l : forall x : Q, Qinv (1 + x * x) * (1 + x * x) == 1.
Proof.
  intros x.
  transitivity ((1 + x * x) * Qinv (1 + x * x)).
  - apply Qmult_comm.
  - exact (b3_inv_sq_r x).
Qed.

(* 主闭式（几何和，对 n 归纳）：
   (1+x²)·b3_dsum n x == 1 − (−x²)^{S n} *)
Lemma b3_dsum_geom : forall (n : nat) (x : Q),
  (1 + x * x) * b3_dsum n x == 1 - q_pow (- (x * x)) (Datatypes.S n).
Proof.
  intros n x. induction n as [| n IH]; simpl.
  - (* n = 0：b3_dsum 0 x == 1；(−x²)^1 == −x² *)
    transitivity ((1 + x * x) * 1).
    + apply Qmult_comp; [apply Qeq_refl | reflexivity].
    + simpl. ring.
  - (* n = S n：拆 b3_dsum 一步，先 ring 分布 *)
    rewrite (b3_dsum_succ n x).
    transitivity ((1 + x * x) * b3_dsum n x +
                  (1 + x * x) * q_pow (- (x * x)) (Datatypes.S n)).
    { ring. }
    rewrite IH.
    rewrite (q_pow_succ (- (x * x)) (Datatypes.S n)).
    ring.
Qed.

(* (a)-余项（绝对等式）：
   |b3_dsum n x − Qinv(1+x²)| == Qinv(1+x²)·|x|^{2n+2} *)
Lemma b3_dsum_rem_abs : forall (n : nat) (x : Q),
  Qabs (b3_dsum n x - Qinv (1 + x * x)) ==
  Qinv (1 + x * x) * q_pow (Qabs x) (2 * Datatypes.S n).
Proof.
  intros n x.
  (* 由 b3_dsum_geom 乘 Qinv(1+x²)：
     b3_dsum n x == Qinv(1+x²)·(1 − (−x²)^{S n}) *)
  assert (Hc : b3_dsum n x == Qinv (1 + x * x) * (1 - q_pow (- (x * x)) (Datatypes.S n))).
  { (* 链：b3_dsum == (Qinv·(1+x²))·b3_dsum == Qinv·((1+x²)·b3_dsum) == Qinv·(1−r) *)
    transitivity ((Qinv (1 + x * x) * (1 + x * x)) * b3_dsum n x).
    - rewrite (b3_inv_sq_l x). ring.
    - transitivity (Qinv (1 + x * x) * ((1 + x * x) * b3_dsum n x)).
      + apply Qeq_sym. apply (Qmult_assoc (Qinv (1 + x * x)) (1 + x * x) (b3_dsum n x)).
      + (* Qmult_comp 是 Proper 形态：apply 后两子目标 *)
        apply Qmult_comp.
        * apply Qeq_refl.
        * exact (b3_dsum_geom n x). }
  (* b3_dsum − Qinv == Qinv·(1 − r^{S n}) − Qinv == Qinv·(−r^{S n}) *)
  assert (Hdiff : b3_dsum n x - Qinv (1 + x * x) ==
                  - (Qinv (1 + x * x) * q_pow (- (x * x)) (Datatypes.S n))).
  { rewrite Hc.
    rewrite <- (Qmult_1_r (Qinv (1 + x * x))).
    ring. }
  rewrite Hdiff.
  rewrite (Qabs_opp (Qinv (1 + x * x) * q_pow (- (x * x)) (Datatypes.S n))).
  rewrite (Qabs_Qmult (Qinv (1 + x * x)) (q_pow (- (x * x)) (Datatypes.S n))).
  (* |Qinv(1+x²)| == Qinv(1+x²)（正性） *)
  assert (Hinvabs : Qabs (Qinv (1 + x * x)) == Qinv (1 + x * x)).
  { apply (Qabs_pos (Qinv (1 + x * x))).
    apply (Qlt_le_weak 0 (Qinv (1 + x * x))).
    apply Qinv_lt_0_compat.
    exact (b3_one_plus_sq_pos x). }
  rewrite Hinvabs.
  rewrite (b3_abs_pow_neg_sq x (Datatypes.S n)).
  reflexivity.
Qed.

(* ============================================================ *)
(* Q 层第 3 部分：(b) 引擎 — 加权几何和有界（Σ_{j<n}(j+1)q^j）  *)
(* 目标：0 ≤ q < 1 ⟹ Σ_{j=0}^{n-1} (j+1) q^j ≤ 1/(1−q)²           *)
(* 路径：闭式 Σ_{j=0}^{n-1}(j+1)q^j == (1−(n+1)q^n + n q^{n+1})/(1−q)² *)
(*       ≤ 1/(1−q)²（分子 ≤ 1：q ≤ 1 时 n·q^{n+1} ≤ (n+1)q^n）     *)
(* ============================================================ *)

(* 加权和（自己定义，避免纠缠 sum_upto 索引约定）：
   b3_wsum q n == Σ_{j=0}^{n-1} (j+1)·q^j，其中系数 j+1 用 (S j)#1 *)
Fixpoint b3_wsum (n : nat) (q : Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => b3_wsum m q + (Z.of_nat (Datatypes.S m) # 1) * q_pow q m
  end.

(* 单步展开件 *)
Lemma b3_wsum_succ : forall (n : nat) (q : Q),
  b3_wsum (Datatypes.S n) q == b3_wsum n q + (Z.of_nat (Datatypes.S n) # 1) * q_pow q n.
Proof. intros. reflexivity. Qed.

(* 桥：nat 后继 → Q：qn_succ (S n)#1 == n#1 + 1（根 L66555 区件） *)
Lemma b3_qn_succ : forall (n : nat),
  Z.of_nat (Datatypes.S n) # 1 == (Z.of_nat n # 1) + 1.
Proof. intros n. exact (qn_succ n). Qed.

(* 加权几何和闭式（归纳）：
   (1−q)²·b3_wsum n q == 1 − (n+1)·q^n + n·q^{n+1} *)
Lemma b3_wsum_closed : forall (n : nat) (q : Q),
  (1 - q) * (1 - q) * b3_wsum n q ==
  1 - (Z.of_nat (Datatypes.S n) # 1) * q_pow q n +
      (Z.of_nat n # 1) * q_pow q (Datatypes.S n).
Proof.
  intros n q. induction n as [| n IH].
  - (* n = 0：b3_wsum 0 q == 0；1 − 1·q^0 + 0 == 0 *)
    simpl. ring.
  - (* n → S n：b3_wsum (S n) == b3_wsum n + (S n)#1·q^n *)
    rewrite (b3_wsum_succ n q).
    (* 分布左乘 *)
    transitivity ((1 - q) * (1 - q) * b3_wsum n q +
                  (1 - q) * (1 - q) * ((Z.of_nat (Datatypes.S n) # 1) * q_pow q n)).
    { ring. }
    rewrite IH.
    (* RHS 换形：把 (S(S n))#1、q^{S n}、q^{S(S n)} 展开 *)
    setoid_replace (q_pow q (Datatypes.S (Datatypes.S n))) with (q * q * q_pow q n) by (rewrite (q_pow_succ q (Datatypes.S n)); rewrite (q_pow_succ q n); ring).
    setoid_replace (q_pow q (Datatypes.S n)) with (q * q_pow q n) by (rewrite (q_pow_succ q n); ring).
    rewrite (b3_qn_succ (Datatypes.S n)).
    rewrite (b3_qn_succ n).
    ring.
Qed.

(* 闭式分子 ≤ 1：n·q^{n+1} ≤ (n+1)·q^n（q ≤ 1，q^n ≥ 0） *)
(* 闭式分子 ≤ 1：n·q^{n+1} ≤ (n+1)·q^n（q ≤ 1，q^n ≥ 0）
   简化证：q^{S n} ≤ q^n（q^{S n}==q·q^n ≤ 1·q^n）再乘 n ≤ S n *)
(* 闭式分子 ≤ 1：n·q^{n+1} ≤ (n+1)·q^n（q ≤ 1，q^n ≥ 0）
   简化证：q^{S n} == q·q^n ≤ 1·q^n（q ≤ 1 且 q^n ≥ 0）
           再 n·(q·q^n) ≤ (n+1)·q^n 由 比较因子（n ≤ S n 且 q^n ≥ 0 与 q·q^n ≥ 0） *)
Lemma b3_q_pow_dec1 : forall (q : Q) (n : nat),
  Qle 0 q -> Qle q 1 -> Qle (q_pow q (Datatypes.S n)) (q_pow q n).
Proof.
  intros q n Hq0 Hq1.
  rewrite (q_pow_succ q n).
  apply (Qle_trans _ (1 * q_pow q n) _).
  - apply (Qmult_le_compat_r q 1 (q_pow q n)).
    + exact Hq1.
    + apply (q_pow_nonneg q n Hq0).
  - apply qeq_le. ring.
Qed.

(* 传乘：0 ≤ c ⟹ a ≤ b ⟹ c·a ≤ c·b（先交换到右乘再 Qmult_le_compat_r） *)
Lemma b3_qmult_le_l : forall (a b c : Q), Qle 0 c -> Qle a b -> Qle (c * a) (c * b).
Proof.
  intros a b c Hc Hab.
  apply (Qle_trans _ (a * c) _).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (b * c) _).
    + apply (Qmult_le_compat_r a b c Hab Hc).
    + apply qeq_le. ring.
Qed.

Lemma b3_wsum_num_le : forall (n : nat) (q : Q),
  Qle 0 q -> Qle q 1 ->
  Qle ((Z.of_nat n # 1) * q_pow q (Datatypes.S n))
      ((Z.of_nat (Datatypes.S n) # 1) * q_pow q n).
Proof.
  intros n q Hq0 Hq1.
  (* 左 = n·(q^{S n}) ≤ n·q^n（q^{S n} ≤ q^n 乘 n ≥ 0） *)
  assert (Hn0 : Qle 0 (Z.of_nat n # 1)) by (unfold Qle; simpl; lia).
  assert (Hstep1 : Qle ((Z.of_nat n # 1) * q_pow q (Datatypes.S n))
                      ((Z.of_nat n # 1) * q_pow q n)).
  { apply (b3_qmult_le_l (q_pow q (Datatypes.S n)) (q_pow q n) (Z.of_nat n # 1)).
    - exact Hn0.
    - apply (b3_q_pow_dec1 q n Hq0 Hq1). }
  (* 再 n·q^n ≤ (n+1)·q^n（n ≤ S n 且 q^n ≥ 0） *)
  assert (Hstep2 : Qle ((Z.of_nat n # 1) * q_pow q n)
                      ((Z.of_nat (Datatypes.S n) # 1) * q_pow q n)).
  { apply (Qmult_le_compat_r (Z.of_nat n # 1) (Z.of_nat (Datatypes.S n) # 1) (q_pow q n)).
    - unfold Qle; simpl; lia.
    - apply (q_pow_nonneg q n Hq0). }
  apply (Qle_trans _ ((Z.of_nat n # 1) * q_pow q n) _).
  - exact Hstep1.
  - exact Hstep2.
Qed.

(* 0 < 1 − q（q < 1） *)
Lemma b3_one_minus_q_pos : forall (q : Q), Qlt q 1 -> Qlt 0 (1 - q).
Proof.
  intros q Hq1.
  (* 展开至定义层：两侧同加减元（加法保序反映面第二投影装配），
     左端经环等式坍缩为零元，右端差式定义性即加负元形，转换闭合
     ——不经单跳换形引理转发。 *)
  assert (Hs : Qlt (q + -q) (1 + -q)).
  { apply (proj2 (Qplus_lt_l q 1 (-q))). exact Hq1. }
  assert (Hz : q + -q == 0) by ring.
  rewrite Hz in Hs.
  exact Hs.
Qed.

Lemma b3_den_pos : forall (q : Q), Qlt q 1 -> Qlt 0 ((1 - q) * (1 - q)).
Proof.
  intros q Hq1.
  apply (Qmult_lt_0_compat (1 - q) (1 - q)).
  - apply (b3_one_minus_q_pos q Hq1).
  - apply (b3_one_minus_q_pos q Hq1).
Qed.

(* 主界：0 ≤ q < 1 ⟹ b3_wsum n q ≤ 1/(1−q)² *)
Lemma b3_wsum_bound : forall (n : nat) (q : Q),
  Qle 0 q -> Qlt q 1 ->
  Qle (b3_wsum n q) (Qinv ((1 - q) * (1 - q))).
Proof.
  intros n q Hq0 Hq1.
  set (d := (1 - q) * (1 - q)).
  assert (Hd0 : Qlt 0 d) by (unfold d; apply (b3_den_pos q Hq1)).
  assert (Hdnz : ~ d == 0) by (apply q_neq_of_lt; exact Hd0).
  assert (Hinv0 : Qle 0 (Qinv d)) by (apply Qlt_le_weak; apply Qinv_lt_0_compat; exact Hd0).
  (* 第一步：b3_wsum·d ≤ 1（= 闭式分子 ≤ 1） *)
  assert (Hle1 : Qle (b3_wsum n q * d) 1).
  { assert (Hc : b3_wsum n q * d ==
                 1 - (Z.of_nat (Datatypes.S n) # 1) * q_pow q n +
                 (Z.of_nat n # 1) * q_pow q (Datatypes.S n)).
    { unfold d. apply (Qeq_trans _ ((1 - q) * (1 - q) * b3_wsum n q) _).
      - apply Qmult_comm.
      - exact (b3_wsum_closed n q). }
    (* b3_wsum·d == 分子 ≤ 1 *)
    apply (Qle_trans _ (1 - (Z.of_nat (Datatypes.S n) # 1) * q_pow q n +
                        (Z.of_nat n # 1) * q_pow q (Datatypes.S n)) _).
    - apply qeq_le. exact Hc.
    - (* 分子 ≤ 1：由 n·q^{S n} ≤ (S n)·q^n *)
      apply (Qle_trans _ (1 - (Z.of_nat (Datatypes.S n) # 1) * q_pow q n +
                          (Z.of_nat (Datatypes.S n) # 1) * q_pow q n) _).
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * exact (b3_wsum_num_le n q Hq0 (Qlt_le_weak _ _ Hq1)).
      + apply qeq_le. ring. }
  (* 目标：b3_wsum ≤ Qinv d。用 b3_wsum == (b3_wsum·d)·Qinv d ≤ 1·Qinv d *)
  apply (Qle_trans _ ((b3_wsum n q * d) * Qinv d) _).
  - (* b3_wsum == (b3_wsum·d)·Qinv d：先乘 1（d·/d）再结合 *)
    apply qeq_le.
    apply (Qeq_trans _ (b3_wsum n q * (d * Qinv d)) _).
    + rewrite (Qmult_inv_r d Hdnz). ring.
    + apply (Qmult_assoc (b3_wsum n q) d (Qinv d)).
  - (* (b3_wsum·d)·Qinv d ≤ 1·Qinv d（Hle1 乘 Qinv d ≥ 0） *)
    apply (Qle_trans _ (1 * Qinv d) _).
    + apply (Qmult_le_compat_r (b3_wsum n q * d) 1 (Qinv d)).
      * exact Hle1.
      * exact Hinv0.
    + apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* Q 层第 4 部分：(b) 引擎 — 单项二阶差界（复用 q_pow_diff_bound） *)
(* 目标：|y|,|x| ≤ M ⟹ |y^{S k} − x^{S k} − (S k)·x^{2k}·(y−x)|     *)
(*       ≤ (S k)²·M^{2k}·(y−x)²·...（本文件取更粗 C=2·(2k+1)² M^{2k}） *)
(* 实际路线：由一阶界 |u^p−v^p| ≤ p·B^{p−1}|u−v| 迭代两次 *) 
(* ============================================================ *)

(* 一阶幂差再界：|x^{S n} − y^{S n}| ≤ (S n)#1·B^n·|x−y|（根 q_pow_diff_bound 包装 Qle 形） *)
Lemma b3_pow_diff1 : forall (x y B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (q_pow x (Datatypes.S n) - q_pow y (Datatypes.S n)))
      (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S n) # 1) (q_pow B n))).
Proof.
  intros x y B n HB Hx Hy.
  exact (q_pow_diff_bound x y B n HB Hx Hy).
Qed.


(* ============================================================ *)
(* Q 层第 5 部分：(a) 余项上界（|x| ≤ r < 1 的闭式估计）          *)
(* |b3_dsum n x − Qinv(1+x²)| ≤ |x|^{2S n}·1 ≤ r^{2S n}          *)
(* 以及 r=1/2 常数版 ≤ 4^{-(S n)}                                 *)
(* ============================================================ *)

(* |b3_dsum n x − Qinv(1+x²)| ≤ |x|^{2(S n)}（Qinv(1+x²) ≤ 1） *)
(* |b3_dsum n x − Qinv(1+x²)| ≤ |x|^{2(S n)}（Qinv(1+x²) ≤ 1） *)
Lemma b3_dsum_rem_le : forall (n : nat) (x : Q),
  Qle (Qabs (b3_dsum n x - Qinv (1 + x * x)))
      (q_pow (Qabs x) (2 * Datatypes.S n)).
Proof.
  intros n x.
  rewrite (b3_dsum_rem_abs n x).
  (* Qinv(1+x²)·|x|^{2(S n)} ≤ |x|^{2(S n)}：Qinv(1+x²) ≤ 1 且 |x|^{2(S n)} ≥ 0 *)
  assert (Hinv0 : Qle 0 (Qinv (1 + x * x))).
  { apply (Qlt_le_weak 0 (Qinv (1 + x * x))).
    apply Qinv_lt_0_compat. exact (b3_one_plus_sq_pos x). }
  assert (Hge1 : Qle 1 (1 + x * x)).
  { apply (Qle_trans _ (1 + 0) _).
    - apply qeq_le. ring.
    - apply Qplus_le_compat. apply Qle_refl. apply (Qsquare_nonneg x). }
  assert (Hinv_le : Qle (Qinv (1 + x * x)) 1).
  { (* Qinv ≤ (1+x²)·Qinv == 1：右乘 1 ≤ 1+x²（因子 ≥0），再 b3_inv_sq_r *)
    apply (Qle_trans _ (1 * Qinv (1 + x * x)) _).
    - apply qeq_le. ring.
    - apply (Qle_trans _ ((1 + x * x) * Qinv (1 + x * x)) _).
      + apply (Qmult_le_compat_r 1 (1 + x * x) (Qinv (1 + x * x))).
        * exact Hge1.
        * exact Hinv0.
      + apply qeq_le. exact (b3_inv_sq_r x). }
  assert (Hpow0 : Qle 0 (q_pow (Qabs x) (2 * Datatypes.S n))) by (apply q_pow_nonneg; apply Qabs_nonneg).
  apply (Qle_trans _ (Qinv (1 + x * x) * q_pow (Qabs x) (2 * Datatypes.S n)) _).
  - apply qeq_le. reflexivity.
  - (* ≤ 1·pow（Hinv_le 乘 pow ≥ 0：b3_qmult_le_l，c := pow，再交换） *)
    apply (Qle_trans _ (q_pow (Qabs x) (2 * Datatypes.S n) * Qinv (1 + x * x)) _).
    + apply qeq_le. ring.
    + apply (Qle_trans _ (q_pow (Qabs x) (2 * Datatypes.S n) * 1) _).
      * apply (b3_qmult_le_l (Qinv (1 + x * x)) 1 (q_pow (Qabs x) (2 * Datatypes.S n))).
        -- exact Hpow0.
        -- exact Hinv_le.
      * apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* B3a Real 层 arctan 导数      *)
(* （|x| ≤ 1/2 逐 eps 可微，主定理 real_arctan_deriv_linear）；   *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b3_arctanp/sc2_b3_real.v *)
(* 30 Qed；零公理面、零承认件。                                   *)
(* ============================================================ *)

(* ============================================================ *)
(* Part 0：有限和 b3r_psum（Σ_{i=0}^{n-1} f i）+ 基础引理        *)
(* ============================================================ *)
Fixpoint b3r_psum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => b3r_psum m f + f m
  end.

Lemma b3r_psum_succ : forall (n : nat) (f : nat -> Q),
  b3r_psum (Datatypes.S n) f == b3r_psum n f + f n.
Proof. intros. reflexivity. Qed.

(* 范围逐点 Qeq ⟹ 和 Qeq（j < n） *)
Lemma b3r_psum_range_ext : forall (n : nat) (f g : nat -> Q),
  (forall j : nat, (j < n)%nat -> f j == g j) -> b3r_psum n f == b3r_psum n g.
Proof.
  induction n as [| n IH]; intros f g H.
  - reflexivity.
  - rewrite (b3r_psum_succ n f). rewrite (b3r_psum_succ n g).
    apply Qplus_comp.
    + apply IH. intros j Hj. apply H. lia.
    + apply H. lia.
Qed.

(* 范围逐点 Qle ⟹ 和 Qle *)
Lemma b3r_psum_le : forall (n : nat) (f g : nat -> Q),
  (forall j : nat, (j < n)%nat -> Qle (f j) (g j)) -> Qle (b3r_psum n f) (b3r_psum n g).
Proof.
  induction n as [| n IH]; intros f g H.
  - apply Qle_refl.
  - rewrite (b3r_psum_succ n f). rewrite (b3r_psum_succ n g).
    apply (Qplus_le_compat (b3r_psum n f) (b3r_psum n g) (f n) (g n)).
    + apply IH. intros j Hj. apply H. lia.
    + apply H. lia.
Qed.

(* |Σ f| ≤ Σ |f| *)
Lemma b3r_psum_abs_le : forall (n : nat) (f : nat -> Q),
  Qle (Qabs (b3r_psum n f)) (b3r_psum n (fun j => Qabs (f j))).
Proof.
  induction n as [| n IH]; intros f.
  - simpl. apply qeq_imp_qle. apply (Qabs_pos 0). apply Qle_refl.
  - rewrite (b3r_psum_succ n f).
    rewrite (b3r_psum_succ n (fun j => Qabs (f j))).
    apply (Qle_trans _ (Qabs (b3r_psum n f) + Qabs (f n)) _).
    + apply Qabs_triangle.
    + apply Qplus_le_compat. exact (IH f). apply Qle_refl.
Qed.

(* 常值求和闭式：psum n (const c) == n#1 · c *)
Lemma b3r_psum_const : forall (n : nat) (c : Q),
  b3r_psum n (fun _ : nat => c) == (Z.of_nat n # 1) * c.
Proof.
  induction n as [| n IH]; intros c.
  - simpl. ring.
  - rewrite (b3r_psum_succ n (fun _ : nat => c)).
    rewrite IH.
    rewrite (b3_qn_succ n).
    ring.
Qed.

(* 线性：psum(f) − psum(g) == psum(f − g) *)
Lemma b3r_psum_minus : forall (n : nat) (f g : nat -> Q),
  b3r_psum n f - b3r_psum n g == b3r_psum n (fun j => f j - g j).
Proof.
  induction n as [| n IH]; intros f g.
  - simpl. ring.
  - rewrite (b3r_psum_succ n f). rewrite (b3r_psum_succ n g).
    rewrite (b3r_psum_succ n (fun j => f j - g j)).
    transitivity ((b3r_psum n f - b3r_psum n g) + (f n - g n)).
    + ring.
    + rewrite IH. reflexivity.
Qed.

(* 常数左乘可提出：psum (fun j => c·f j) == c·psum f *)
Lemma b3r_psum_mul_const_l : forall (n : nat) (c : Q) (f : nat -> Q),
  b3r_psum n (fun j => c * f j) == c * b3r_psum n f.
Proof.
  induction n as [| n IH]; intros c f.
  - simpl. ring.
  - rewrite (b3r_psum_succ n (fun j => c * f j)).
    rewrite (b3r_psum_succ n f).
    rewrite IH. ring.
Qed.

(* 常数右乘可提出：psum (fun j => f j·c) == (psum f)·c *)
Lemma b3r_psum_mul_const_r : forall (n : nat) (f : nat -> Q) (c : Q),
  b3r_psum n (fun j => f j * c) == b3r_psum n f * c.
Proof.
  induction n as [| n IH]; intros f c.
  - simpl. ring.
  - rewrite (b3r_psum_succ n (fun j => f j * c)).
    rewrite (b3r_psum_succ n f).
    rewrite IH. ring.
Qed.

(* ============================================================ *)
(* Part 1：幂一阶差（任意指数 p，p=0 平凡，指数 (p−1) 截断无害） *)
(* |y^p − x^p| ≤ p#1 · B^{p−1} · |y−x|（0 ≤ B，|x|,|y| ≤ B）    *)
(* ============================================================ *)
Lemma b3r_pow_diff : forall (x y B : Q) (p : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (q_pow y p - q_pow x p))
      (Qmult (Qabs (y - x)) (Qmult (Z.of_nat p # 1) (q_pow B (p - 1)))).
Proof.
  intros x y B p HB Hx Hy.
  destruct p as [| n].
  - (* p = 0：|1 − 1| == 0 ≤ 0·… *)
    apply (Qle_trans _ 0 _).
    + apply qeq_imp_qle. apply q_abs_self_zero.
    + apply qeq_imp_qle. ring.
  - (* p = S n：q_pow_diff_bound 包装（y 为先序） *)
    apply (Qle_trans _ (Qmult (Qabs (y - x)) (Qmult (Z.of_nat (Datatypes.S n) # 1) (q_pow B n))) _).
    + apply (q_pow_diff_bound y x B n HB Hy Hx).
    + apply qeq_imp_qle.
      assert (Hsub : (Datatypes.S n - 1)%nat = n) by lia.
      rewrite Hsub.
      reflexivity.
Qed.

(* |(−1)^k| == 1 *)
Lemma b3r_abs_neg1_pow : forall (k : nat), Qabs (q_pow (-1) k) == 1.
Proof.
  intros k.
  rewrite (q_pow_abs (-1) k).
  assert (H : Qabs (-1) == 1).
  { apply Qabs_neg. unfold Qle. simpl. lia. }
  rewrite H.
  apply q_pow_one.
Qed.

(* ============================================================ *)
(* Part 2：幂差因子化：y^{p+1} − x^{p+1} == (y−x)·Σ_{j=0}^{p} y^{p−j} x^j *)
(* ============================================================ *)
Lemma b3r_pow_factor : forall (p : nat) (x y : Q),
  q_pow y (Datatypes.S p) - q_pow x (Datatypes.S p) ==
  (y - x) * b3r_psum (Datatypes.S p) (fun j : nat => q_pow y (p - j) * q_pow x j).
Proof.
  induction p as [| p IH]; intros x y.
  - (* p = 0：y − x == (y−x)·(y^{0−0}·x^0) *)
    simpl. ring.
  - (* p → S p *)
    rewrite (b3r_psum_succ (Datatypes.S p) (fun j : nat => q_pow y (Datatypes.S p - j) * q_pow x j)).
    assert (Htail : q_pow y (Datatypes.S p - Datatypes.S p) * q_pow x (Datatypes.S p) ==
                    q_pow x (Datatypes.S p)).
    { assert (Hz : (Datatypes.S p - Datatypes.S p)%nat = 0%nat) by lia.
      rewrite Hz. simpl. ring. }
    assert (Hfront : b3r_psum (Datatypes.S p) (fun j : nat => q_pow y (Datatypes.S p - j) * q_pow x j) ==
                     y * b3r_psum (Datatypes.S p) (fun j : nat => q_pow y (p - j) * q_pow x j)).
    { transitivity (b3r_psum (Datatypes.S p) (fun j : nat => y * (q_pow y (p - j) * q_pow x j))).
      - apply b3r_psum_range_ext. intros j Hj.
        assert (Hnat : (Datatypes.S p - j)%nat = Datatypes.S (p - j)) by lia.
        rewrite Hnat.
        rewrite (q_pow_succ y (p - j)).
        ring.
      - apply b3r_psum_mul_const_l. }
    rewrite Hfront. rewrite Htail.
    set (B := b3r_psum (Datatypes.S p) (fun j : nat => q_pow y (p - j) * q_pow x j)).
    assert (HIH : (y - x) * B == q_pow y (Datatypes.S p) - q_pow x (Datatypes.S p)).
    { unfold B. apply Qeq_sym. exact (IH x y). }
    assert (Hy_ : q_pow y (Datatypes.S p) == (y - x) * B + q_pow x (Datatypes.S p)).
    { rewrite HIH. ring. }
    rewrite (q_pow_succ y (Datatypes.S p)).
    rewrite (q_pow_succ x (Datatypes.S p)).
    rewrite Hy_.
    ring.
Qed.

(* ============================================================ *)
(* Part 3：单项二阶差界（(b) 引擎核心）                          *)
(* |y^{2k+1}−x^{2k+1}−(2k+1)x^{2k}(y−x)|                         *)
(*   ≤ (2k)(2k+1)·M^{2k−1}·|y−x|²（|x|,|y| ≤ M，0 ≤ M）          *)
(* 路线：因子化 y^{2k+1}−x^{2k+1} == (y−x)·Σ_{j≤2k} y^{2k−j}x^j， *)
(*   D_k == (y−x)·Σ_j x^j(y^{2k−j}−x^{2k−j})，逐 j 一阶界，      *)
(*   Σ_j(2k−j) ≤ (2k+1)(2k) 度向和。                             *)
(* ============================================================ *)

(* 度向组合件：coeff·(M^j·M^{(2k−j)−1}) ≤ coeff·M^{2k−1}（j ≤ 2k；j=2k 时两边 0） *)
Lemma b3r_pow2diff_deg : forall (M : Q) (k j : nat),
  Qle 0 M -> (j <= 2 * k)%nat ->
  Qle (Qmult (Z.of_nat (2 * k - j) # 1)
             (Qmult (q_pow M j) (q_pow M (2 * k - j - 1))))
      (Qmult (Z.of_nat (2 * k - j) # 1) (q_pow M (2 * k - 1))).
Proof.
  intros M k j HM Hjk.
  destruct ((2 * k - j)%nat) as [| t] eqn:E.
  - (* 2k−j == 0：destruct 已代入，coeff == 0，两边 == 0 *)
    apply qeq_imp_qle. ring.
  - (* 2k−j == S t（destruct 已代入，指数 (S t)−1 ⟹ t）：M^j·M^t == M^{j+t} == M^{2k−1} *)
    apply qeq_imp_qle.
    apply Qmult_comp.
    + reflexivity.
    + assert (Ht : (Datatypes.S t - 1)%nat = t) by lia.
      rewrite Ht.
      rewrite <- (atan_q_pow_add M j t).
      assert (Hnat : (j + t)%nat = (2 * k - 1)%nat).
      { lia. }
      rewrite Hnat.
      reflexivity.
Qed.

(* 逐 j 项界：|x|^j·|y^{2k−j} − x^{2k−j}| ≤ (2k−j)#1·M^{2k−1}·|y−x| *)
Lemma b3r_pow2diff_term : forall (x y M : Q) (k j : nat),
  Qle 0 M -> Qle (Qabs x) M -> Qle (Qabs y) M -> (j <= 2 * k)%nat ->
  Qle (Qmult (q_pow (Qabs x) j) (Qabs (q_pow y (2 * k - j) - q_pow x (2 * k - j))))
      (Qmult (Z.of_nat (2 * k - j) # 1) (Qmult (q_pow M (2 * k - 1)) (Qabs (y - x)))).
Proof.
  intros x y M k j HM Hx Hy Hjk.
  set (Coeff := Z.of_nat (2 * k - j) # 1).
  set (AY := Qabs (y - x)).
  set (Axj := q_pow (Qabs x) j).
  set (Mp1 := q_pow M (2 * k - j - 1)).
  set (Mj := q_pow M j).
  assert (Hinner : Qle (Qabs (q_pow y (2 * k - j) - q_pow x (2 * k - j)))
      (Qmult AY (Qmult Coeff Mp1))).
  { unfold AY, Coeff, Mp1.
    apply (b3r_pow_diff x y M (2 * k - j)); assumption. }
  assert (Hj0 : Qle 0 Axj).
  { unfold Axj. apply q_pow_nonneg. apply Qabs_nonneg. }
  assert (HxM : Qle Axj Mj).
  { unfold Axj, Mj. apply q_pow_mono. apply Qabs_nonneg. exact Hx. }
  assert (Hp0 : Qle 0 Mp1).
  { unfold Mp1. apply q_pow_nonneg. exact HM. }
  assert (Hc0 : Qle 0 Coeff).
  { unfold Coeff. unfold Qle. simpl. lia. }
  assert (HAY0 : Qle 0 AY) by (unfold AY; apply Qabs_nonneg).
  assert (Hmid0 : Qle 0 (Qmult Coeff AY)).
  { apply (Qmult_le_0_compat Coeff AY). exact Hc0. exact HAY0. }
  apply (Qle_trans _ (Qmult Axj (Qmult AY (Qmult Coeff Mp1))) _).
  - (* LHS ≤ Axj·内层界（乘 |x|^j ≥ 0，左乘） *)
    apply (b3_qmult_le_l (Qabs (q_pow y (2 * k - j) - q_pow x (2 * k - j)))
                         (Qmult AY (Qmult Coeff Mp1)) Axj).
    + exact Hj0.
    + exact Hinner.
  - apply (Qle_trans _ (Qmult (Qmult Coeff AY) (Qmult Axj Mp1)) _).
    + apply qeq_imp_qle. unfold Coeff, AY, Axj, Mp1. ring.
    + apply (Qle_trans _ (Qmult (Qmult Coeff AY) (Qmult Mj Mp1)) _).
      * apply (b3_qmult_le_l (Qmult Axj Mp1) (Qmult Mj Mp1) (Qmult Coeff AY)).
        -- exact Hmid0.
        -- apply (Qmult_le_compat_r Axj Mj Mp1). exact HxM. exact Hp0.
      * apply (Qle_trans _ (Qmult (Qmult Coeff AY) (q_pow M (2 * k - 1))) _).
        -- apply (Qle_trans _ (Qmult AY (Qmult Coeff (Qmult Mj Mp1))) _).
           ++ apply qeq_imp_qle. unfold Coeff, AY. ring.
           ++ apply (Qle_trans _ (Qmult AY (Qmult Coeff (q_pow M (2 * k - 1)))) _).
              ** apply (b3_qmult_le_l (Qmult Coeff (Qmult Mj Mp1))
                                      (Qmult Coeff (q_pow M (2 * k - 1))) AY).
                 --- exact HAY0.
                 --- unfold Coeff, Mj, Mp1. apply (b3r_pow2diff_deg M k j HM Hjk).
              ** apply qeq_imp_qle. unfold Coeff, AY. ring.
        -- apply qeq_imp_qle. unfold Coeff, AY. ring.
Qed.

(* 度向和 ≤ (2k)(2k+1)：Σ_{j=0}^{2k} (2k−j) ≤ (2k+1)·(2k)（每项 ≤ 2k） *)
Lemma b3r_pow2diff_coeffsum : forall (k : nat),
  Qle (b3r_psum (2 * k + 1) (fun j : nat => Z.of_nat (2 * k - j) # 1))
      (Qmult (Z.of_nat (2 * k + 1) # 1) (Z.of_nat (2 * k) # 1)).
Proof.
  intros k.
  apply (Qle_trans _ (b3r_psum (2 * k + 1) (fun _ : nat => Z.of_nat (2 * k) # 1)) _).
  - apply b3r_psum_le. intros j Hj.
    unfold Qle. simpl. lia.
  - apply qeq_imp_qle. apply (b3r_psum_const (2 * k + 1) (Z.of_nat (2 * k) # 1)).
Qed.

(* 主：单项二阶差界 *)
Lemma b3r_pow2diff : forall (x y M : Q) (k : nat),
  Qle 0 M -> Qle (Qabs x) M -> Qle (Qabs y) M ->
  Qle (Qabs (q_pow y (2 * k + 1) - q_pow x (2 * k + 1) -
              ((Z.of_nat (2 * k + 1) # 1) * q_pow x (2 * k)) * (y - x)))
      (Qmult (Z.of_nat (2 * k) # 1)
             (Qmult (Z.of_nat (2 * k + 1) # 1)
                    (Qmult (q_pow M (2 * k - 1))
                           (Qmult (Qabs (y - x)) (Qabs (y - x)))))).
Proof.
  intros x y M k HM Hx Hy.
  assert (Hfac' : q_pow y (Datatypes.S (2 * k)) - q_pow x (Datatypes.S (2 * k)) ==
                  (y - x) * b3r_psum (Datatypes.S (2 * k))
                    (fun j : nat => q_pow y (2 * k - j) * q_pow x j)).
  { exact (b3r_pow_factor (2 * k) x y). }
  assert (He1 : (2 * k + 1)%nat = Datatypes.S (2 * k)) by lia.
  assert (Hfac : q_pow y (2 * k + 1) - q_pow x (2 * k + 1) ==
                 (y - x) * b3r_psum (2 * k + 1)
                   (fun j : nat => q_pow y (2 * k - j) * q_pow x j)).
  { rewrite <- He1 in Hfac'. exact Hfac'. }
  assert (Hconst : (Z.of_nat (2 * k + 1) # 1) * q_pow x (2 * k) ==
                   b3r_psum (2 * k + 1) (fun _ : nat => q_pow x (2 * k))).
  { apply Qeq_sym. apply (b3r_psum_const (2 * k + 1) (q_pow x (2 * k))). }
  assert (Hsplit : q_pow y (2 * k + 1) - q_pow x (2 * k + 1) -
                   ((Z.of_nat (2 * k + 1) # 1) * q_pow x (2 * k)) * (y - x) ==
                   (y - x) * b3r_psum (2 * k + 1)
                     (fun j : nat => q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j)))).
  { rewrite Hfac. rewrite Hconst.
    transitivity ((y - x) * (b3r_psum (2 * k + 1)
                   (fun j : nat => q_pow y (2 * k - j) * q_pow x j) -
                   b3r_psum (2 * k + 1) (fun _ : nat => q_pow x (2 * k)))).
    + ring.
    + rewrite (b3r_psum_minus (2 * k + 1)
                (fun j : nat => q_pow y (2 * k - j) * q_pow x j)
                (fun _ : nat => q_pow x (2 * k))).
      apply Qmult_comp.
      - reflexivity.
      - apply b3r_psum_range_ext. intros j Hj.
        assert (Hadd : (j + (2 * k - j))%nat = (2 * k)%nat) by lia.
        assert (Heq : q_pow x (2 * k) == q_pow x (j + (2 * k - j))).
        { rewrite Hadd. reflexivity. }
        rewrite Heq.
        rewrite (atan_q_pow_add x j (2 * k - j)).
        ring. }
  apply (Qle_trans _ (Qmult (Qabs (y - x))
      (b3r_psum (2 * k + 1)
        (fun j : nat => Qmult (q_pow (Qabs x) j)
             (Qabs (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))) _).
  - apply (Qle_trans _ (Qmult (Qabs (y - x))
        (Qabs (b3r_psum (2 * k + 1)
           (fun j : nat => q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))) _).
    + apply qeq_imp_qle.
      rewrite (Qabs_wd _ _ Hsplit).
      rewrite (Qabs_Qmult (y - x)
                (b3r_psum (2 * k + 1)
                  (fun j : nat => q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j))))).
      reflexivity.
    + apply (Qle_trans _ (Qmult (Qabs (y - x))
        (b3r_psum (2 * k + 1)
          (fun j : nat => Qabs (q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))) _).
      * apply (b3_qmult_le_l (Qabs (b3r_psum (2 * k + 1)
             (fun j : nat => q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))
             (b3r_psum (2 * k + 1)
               (fun j : nat => Qabs (q_pow x j * (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))
             (Qabs (y - x))).
        -- apply Qabs_nonneg.
        -- apply b3r_psum_abs_le.
      * apply qeq_imp_qle.
        apply Qmult_comp.
        -- reflexivity.
        -- apply b3r_psum_range_ext. intros j Hj.
           rewrite (Qabs_Qmult (q_pow x j) (q_pow y (2 * k - j) - q_pow x (2 * k - j))).
           rewrite (q_pow_abs x j).
           reflexivity.
  - apply (Qle_trans _ (Qmult (Qabs (y - x))
        (b3r_psum (2 * k + 1)
          (fun j : nat => (Z.of_nat (2 * k - j) # 1) *
                 (q_pow M (2 * k - 1) * Qabs (y - x))))) _).
    + apply (b3_qmult_le_l
        (b3r_psum (2 * k + 1)
          (fun j : nat => Qmult (q_pow (Qabs x) j)
               (Qabs (q_pow y (2 * k - j) - q_pow x (2 * k - j)))))
        (b3r_psum (2 * k + 1)
          (fun j : nat => (Z.of_nat (2 * k - j) # 1) *
                 (q_pow M (2 * k - 1) * Qabs (y - x))))
        (Qabs (y - x))).
      * apply Qabs_nonneg.
      * apply b3r_psum_le. intros j Hj.
        apply (b3r_pow2diff_term x y M k j HM Hx Hy). lia.
    + apply (Qle_trans _ (Qmult (Qabs (y - x))
        (Qmult (b3r_psum (2 * k + 1) (fun j : nat => Z.of_nat (2 * k - j) # 1))
               (q_pow M (2 * k - 1) * Qabs (y - x)))) _).
      * apply qeq_imp_qle.
        rewrite (b3r_psum_mul_const_r (2 * k + 1)
                  (fun j : nat => Z.of_nat (2 * k - j) # 1)
                  (q_pow M (2 * k - 1) * Qabs (y - x))).
        reflexivity.
      * assert (HC0 : Qle 0 (q_pow M (2 * k - 1) * Qabs (y - x))).
        { apply (Qmult_le_0_compat (q_pow M (2 * k - 1)) (Qabs (y - x))).
          - apply q_pow_nonneg. exact HM.
          - apply Qabs_nonneg. }
        assert (Hcs : Qle (b3r_psum (2 * k + 1) (fun j : nat => Z.of_nat (2 * k - j) # 1))
                          (Qmult (Z.of_nat (2 * k + 1) # 1) (Z.of_nat (2 * k) # 1)))
          by apply b3r_pow2diff_coeffsum.
        apply (Qle_trans _ (Qmult (Qabs (y - x))
            (Qmult (Qmult (Z.of_nat (2 * k + 1) # 1) (Z.of_nat (2 * k) # 1))
                   (q_pow M (2 * k - 1) * Qabs (y - x)))) _).
        -- apply (b3_qmult_le_l (Qmult (b3r_psum (2 * k + 1) (fun j : nat => Z.of_nat (2 * k - j) # 1))
                                       (q_pow M (2 * k - 1) * Qabs (y - x)))
                 (Qmult (Qmult (Z.of_nat (2 * k + 1) # 1) (Z.of_nat (2 * k) # 1))
                        (q_pow M (2 * k - 1) * Qabs (y - x)))
                 (Qabs (y - x))).
           ++ apply Qabs_nonneg.
           ++ apply (Qmult_le_compat_r
                (b3r_psum (2 * k + 1) (fun j : nat => Z.of_nat (2 * k - j) # 1))
                (Qmult (Z.of_nat (2 * k + 1) # 1) (Z.of_nat (2 * k) # 1))
                (q_pow M (2 * k - 1) * Qabs (y - x))).
              ** exact Hcs.
              ** exact HC0.
        -- apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* Part 4：(b) 部分和变差 |S_n(y) − S_n(x) − (y−x)·b3_dsum n x| *)
(*   ≤ 2·M·b3_wsum n (M²)·|y−x|²（|x|,|y| ≤ M，0 ≤ M）           *)
(* 归纳步增量 |B_k| ≤ (2k)#1·M^{2k−1}·|y−x|²（k = S m）         *)
(* ============================================================ *)

(* 系数恒等：(2k)#1 == 2·(k#1) *)
Lemma b3r_coef2 : forall (k : nat), (Z.of_nat (2 * k) # 1) == 2 * (Z.of_nat k # 1).
Proof.
  intros k.
  assert (Hz : Z.of_nat (2 * k) = (2 * Z.of_nat k)%Z).
  { rewrite Znat.Nat2Z.inj_mul. lia. }
  rewrite Hz. reflexivity.
Qed.

(* 指数恒等：M^{2(Sm)−1} == M·(M²)^m *)
Lemma b3r_Mpow : forall (M : Q) (m : nat),
  q_pow M (2 * Datatypes.S m - 1) == M * q_pow (M * M) m.
Proof.
  intros M m.
  assert (Hnat : (2 * Datatypes.S m - 1)%nat = (2 * m + 1)%nat) by lia.
  rewrite Hnat.
  assert (Hnat2 : (2 * m + 1)%nat = Datatypes.S (2 * m)) by lia.
  rewrite Hnat2.
  rewrite (q_pow_succ M (2 * m)).
  rewrite (b3_even_pow M m).
  ring.
Qed.

(* 增量界：|arctan_term (S m) y − arctan_term (S m) x − (y−x)(−(x·x))^{S m}|
   ≤ (2·(S m))#1·M^{2(Sm)−1}·|y−x|² *)
Lemma b3r_inc : forall (x y M : Q) (m : nat),
  Qle 0 M -> Qle (Qabs x) M -> Qle (Qabs y) M ->
  Qle (Qabs (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
              - (y - x) * q_pow (- (x * x)) (Datatypes.S m)))
      (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
             (Qmult (q_pow M (2 * Datatypes.S m - 1))
                    (Qmult (Qabs (y - x)) (Qabs (y - x))))).
Proof.
  intros x y M m HM Hx Hy.
  set (d := Z.of_nat (2 * Datatypes.S m + 1) # 1).
  set (e := (2 * Datatypes.S m + 1)%nat).
  set (D := q_pow y e - q_pow x e -
            (d * q_pow x (2 * Datatypes.S m)) * (y - x)).
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply atan_odd_pos. }
  assert (Hdnz : ~ d == 0) by (apply q_neq_of_lt; exact Hd0).
  assert (Hinv0 : Qle 0 (Qinv d)).
  { apply (Qlt_le_weak 0 (Qinv d)). apply Qinv_lt_0_compat. exact Hd0. }
  assert (Hinvr : d * Qinv d == 1).
  { apply (Qmult_inv_r d Hdnz). }
  assert (Halg1 : arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
                  - (y - x) * q_pow (- (x * x)) (Datatypes.S m) ==
                  q_pow (-1) (Datatypes.S m) *
                  ((q_pow y e - q_pow x e) * Qinv d - q_pow x (2 * Datatypes.S m) * (y - x))).
  { unfold e, d. unfold arctan_term. unfold Qdiv.
    rewrite (b3_pow_neg_sq x (Datatypes.S m)).
    rewrite (b3_pow_sq x (Datatypes.S m)).
    ring. }
  assert (Hc : (q_pow y e - q_pow x e) * Qinv d - q_pow x (2 * Datatypes.S m) * (y - x) ==
               D * Qinv d).
  { unfold D.
    transitivity ((q_pow y e - q_pow x e) * Qinv d -
                  (q_pow x (2 * Datatypes.S m) * (y - x)) * (d * Qinv d)).
    - rewrite Hinvr. ring.
    - ring. }
  assert (Habs : Qabs (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
              - (y - x) * q_pow (- (x * x)) (Datatypes.S m)) == Qabs D * Qinv d).
  { rewrite Halg1.
    rewrite (Qabs_Qmult (q_pow (-1) (Datatypes.S m))
              ((q_pow y e - q_pow x e) * Qinv d - q_pow x (2 * Datatypes.S m) * (y - x))).
    rewrite (b3r_abs_neg1_pow (Datatypes.S m)).
    rewrite (Qabs_wd _ _ Hc).
    rewrite (Qabs_Qmult D (Qinv d)).
    assert (Hinvabs : Qabs (Qinv d) == Qinv d).
    { apply (Qabs_pos (Qinv d)). exact Hinv0. }
    rewrite Hinvabs. ring. }
  assert (Hpow : Qle (Qabs D)
     (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
            (Qmult d (Qmult (q_pow M (2 * Datatypes.S m - 1))
                            (Qmult (Qabs (y - x)) (Qabs (y - x))))))).
  { unfold D, d, e. apply (b3r_pow2diff x y M (Datatypes.S m) HM Hx Hy). }
  apply (Qle_trans _ (Qmult (Qabs D) (Qinv d)) _).
  - apply qeq_imp_qle. exact Habs.
  - apply (Qle_trans _ (Qmult
       (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
              (Qmult d (Qmult (q_pow M (2 * Datatypes.S m - 1))
                              (Qmult (Qabs (y - x)) (Qabs (y - x))))))
       (Qinv d)) _).
    + apply (Qmult_le_compat_r (Qabs D)
        (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
              (Qmult d (Qmult (q_pow M (2 * Datatypes.S m - 1))
                              (Qmult (Qabs (y - x)) (Qabs (y - x))))))
        (Qinv d)).
      * exact Hpow.
      * exact Hinv0.
    + apply qeq_imp_qle.
      transitivity (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
                     (Qmult (Qmult (q_pow M (2 * Datatypes.S m - 1))
                                   (Qmult (Qabs (y - x)) (Qabs (y - x))))
                            (d * Qinv d))).
      * ring.
      * rewrite Hinvr. ring.
Qed.

(* S_0(z) == z *)
Lemma b3r_ap0 : forall (z : Q), arctan_partial 0 z == z.
Proof.
  intros z.
  simpl. unfold arctan_term. unfold Qdiv.
  assert (He : (2 * 0 + 1)%nat = 1%nat) by lia.
  rewrite He.
  rewrite (q_pow_succ z 0).
  assert (Hi : Qinv (Z.of_nat 1 # 1) == 1).
  { reflexivity. }
  rewrite Hi.
  simpl. ring.
Qed.

(* 主：(b) 部分和变差 *)
Lemma b3r_partial_var : forall (n : nat) (x y M : Q),
  Qle 0 M -> Qle (Qabs x) M -> Qle (Qabs y) M ->
  Qle (Qabs (arctan_partial n y - arctan_partial n x - (y - x) * b3_dsum n x))
      (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult M (b3_wsum n (M * M))))
             (Qmult (Qabs (y - x)) (Qabs (y - x)))).
Proof.
  induction n as [| m IH]; intros x y M HM Hx Hy.
  - (* n = 0：LHS == 0、RHS == 0 *)
    apply qeq_imp_qle.
    transitivity 0.
    + rewrite (b3r_ap0 y). rewrite (b3r_ap0 x).
      change (Qabs (y - x - (y - x) * 1) == 0).
      assert (Hin : y - x - (y - x) * 1 == 0) by ring.
      rewrite Hin.
      apply (Qabs_pos 0). apply Qle_refl.
    + simpl. ring.
  - (* n = S m *)
    assert (Hdec : arctan_partial (Datatypes.S m) y - arctan_partial (Datatypes.S m) x
                   - (y - x) * b3_dsum (Datatypes.S m) x ==
        (arctan_partial m y - arctan_partial m x - (y - x) * b3_dsum m x) +
        (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
         - (y - x) * q_pow (- (x * x)) (Datatypes.S m))).
    { rewrite (b3_dsum_succ m x). simpl. ring. }
    assert (Hinc : Qle
      (Qabs (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
             - (y - x) * q_pow (- (x * x)) (Datatypes.S m)))
      (Qmult (Z.of_nat 2 # 1)
             (Qmult M (Qmult (Z.of_nat (Datatypes.S m) # 1)
                             (Qmult (q_pow (M * M) m)
                                    (Qmult (Qabs (y - x)) (Qabs (y - x)))))))).
    { apply (Qle_trans _ (Qmult (Z.of_nat (2 * Datatypes.S m) # 1)
             (Qmult (q_pow M (2 * Datatypes.S m - 1))
                    (Qmult (Qabs (y - x)) (Qabs (y - x))))) _).
      - apply (b3r_inc x y M m HM Hx Hy).
      - apply qeq_imp_qle.
        rewrite (b3r_coef2 (Datatypes.S m)).
        rewrite (b3r_Mpow M m).
        ring. }
    apply (Qle_trans _ (Qplus
        (Qabs (arctan_partial m y - arctan_partial m x - (y - x) * b3_dsum m x))
        (Qabs (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
               - (y - x) * q_pow (- (x * x)) (Datatypes.S m)))) _).
    + apply (Qle_trans _ (Qabs
        ((arctan_partial m y - arctan_partial m x - (y - x) * b3_dsum m x) +
         (arctan_term (Datatypes.S m) y - arctan_term (Datatypes.S m) x
          - (y - x) * q_pow (- (x * x)) (Datatypes.S m)))) _).
      * apply qeq_imp_qle. apply Qabs_wd. exact Hdec.
      * apply Qabs_triangle.
    + apply (Qle_trans _ (Qplus
        (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult M (b3_wsum m (M * M))))
               (Qmult (Qabs (y - x)) (Qabs (y - x))))
        (Qmult (Z.of_nat 2 # 1)
               (Qmult M (Qmult (Z.of_nat (Datatypes.S m) # 1)
                               (Qmult (q_pow (M * M) m)
                                      (Qmult (Qabs (y - x)) (Qabs (y - x)))))))) _).
      * apply Qplus_le_compat.
        -- apply IH; assumption.
        -- exact Hinc.
      * apply qeq_imp_qle.
        rewrite (b3_wsum_succ m (M * M)).
        ring.
Qed.

(* ============================================================ *)
(* Part 5：Cb 常量 + (b)-界实例化（M := 3/4）+ 域证书 + 衰减     *)
(* ============================================================ *)

Definition b3r_Cb : Q :=
  Qmult (Z.of_nat 2 # 1) (Qmult (3 # 4)
    (Qinv ((1 - (3 # 4) * (3 # 4)) * (1 - (3 # 4) * (3 # 4))))).

Lemma b3r_Cb0 : Qle 0 b3r_Cb.
Proof.
  unfold b3r_Cb.
  apply (Qmult_le_0_compat (Z.of_nat 2 # 1)
          (Qmult (3 # 4) (Qinv ((1 - (3 # 4) * (3 # 4)) * (1 - (3 # 4) * (3 # 4)))))).
  - unfold Qle. simpl. lia.
  - apply (Qmult_le_0_compat (3 # 4)
          (Qinv ((1 - (3 # 4) * (3 # 4)) * (1 - (3 # 4) * (3 # 4))))).
    + unfold Qle. simpl. lia.
    + apply (Qlt_le_weak 0 (Qinv ((1 - (3 # 4) * (3 # 4)) * (1 - (3 # 4) * (3 # 4))))).
      apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat (1 - (3 # 4) * (3 # 4)) (1 - (3 # 4) * (3 # 4))).
      * compute. reflexivity.
      * compute. reflexivity.
Qed.

(* (b)-界实例（|x|,|y| ≤ 3/4）：≤ Cb·|y−x|² *)
Lemma b3r_var34 : forall (n : nat) (x y : Q),
  Qle (Qabs x) (3 # 4) -> Qle (Qabs y) (3 # 4) ->
  Qle (Qabs (arctan_partial n y - arctan_partial n x - (y - x) * b3_dsum n x))
      (Qmult b3r_Cb (Qmult (Qabs (y - x)) (Qabs (y - x)))).
Proof.
  intros n x y Hx Hy.
  assert (HM : Qle 0 (3 # 4)) by (unfold Qle; simpl; lia).
  set (q := (3 # 4) * (3 # 4)).
  assert (Hq0 : Qle 0 q).
  { unfold q. apply (Qmult_le_0_compat (3 # 4) (3 # 4)).
    - unfold Qle; simpl; lia.
    - unfold Qle; simpl; lia. }
  assert (Hq1 : Qlt q 1).
  { unfold q. compute. reflexivity. }
  apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult (3 # 4) (b3_wsum n q)))
                                   (Qabs (y - x))) (Qabs (y - x))) _).
  - apply (Qle_trans _
      (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult (3 # 4) (b3_wsum n q)))
             (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
    + apply (b3r_partial_var n x y (3 # 4) HM Hx Hy).
    + apply qeq_imp_qle. unfold q. ring.
  - apply (Qle_trans _
      (Qmult (Qmult (Z.of_nat 2 # 1)
              (Qmult (3 # 4) (Qinv ((1 - q) * (1 - q)))))
             (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
    + assert (Hw : Qle (b3_wsum n q) (Qinv ((1 - q) * (1 - q))))
        by (apply (b3_wsum_bound n q Hq0 Hq1)).
      assert (Hc0 : Qle 0 (Qmult (Z.of_nat 2 # 1) (3 # 4)))
        by (apply (Qmult_le_0_compat (Z.of_nat 2 # 1) (3 # 4));
            [unfold Qle; simpl; lia | unfold Qle; simpl; lia]).
      assert (Hvv0 : Qle 0 (Qmult (Qabs (y - x)) (Qabs (y - x))))
        by (apply (Qmult_le_0_compat (Qabs (y - x)) (Qabs (y - x)));
            [apply Qabs_nonneg | apply Qabs_nonneg]).
      apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) (3 # 4)) (b3_wsum n q))
                                (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
      * apply qeq_imp_qle. ring.
      * apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) (3 # 4))
                                         (Qinv ((1 - q) * (1 - q))))
                                  (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
        -- apply (Qmult_le_compat_r (Qmult (Qmult (Z.of_nat 2 # 1) (3 # 4)) (b3_wsum n q))
                   (Qmult (Qmult (Z.of_nat 2 # 1) (3 # 4)) (Qinv ((1 - q) * (1 - q))))
                   (Qmult (Qabs (y - x)) (Qabs (y - x)))).
           ++ apply (b3_qmult_le_l (b3_wsum n q) (Qinv ((1 - q) * (1 - q)))
                                    (Qmult (Z.of_nat 2 # 1) (3 # 4))).
              ** exact Hc0.
              ** exact Hw.
           ++ exact Hvv0.
        -- apply qeq_imp_qle. unfold q. ring.
    + apply qeq_imp_qle. unfold b3r_Cb. unfold q. ring.
Qed.

(* 域证书：|x| ≤ 1/2（逐点 QleT'）⟹ |x| ≤ 1 *)
Lemma b3r_half_dom : forall (x : Real),
  (forall n : nat, QleT' (Qabs (projT1 x n)) (Qinv 2)) ->
  forall n : nat, QleT' (Qabs (projT1 x n)) 1.
Proof.
  intros x Hxb n.
  apply (qleT'_trans (Qabs (projT1 x n)) (Qinv 2) 1).
  - apply Hxb.
  - apply Qle_to_QleT'.
    unfold Qle. simpl. lia.
Qed.

(* 投影：projT1 real_one n == 1 *)
Lemma b3r_one_proj : forall (n : nat), projT1 real_one n == 1.
Proof. intros n. cbn [projT1]. reflexivity. Qed.

(* 投影：projT1 real_zero n == 0 *)
Lemma b3r_zero_proj : forall (n : nat), projT1 real_zero n == 0.
Proof. intros n. cbn [projT1]. reflexivity. Qed.

(* 正性件：0 < 1 + x·x（Real 见证 eps := 1/2，N := 0） *)
Lemma b3r_one_sq_real_pos : forall (x : Real),
  real_lt real_zero (real_plus real_one (real_mult x x)).
Proof.
  intros x.
  unfold real_lt.
  exists (1 # 2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj real_one (real_mult x x) n).
    rewrite (real_mult_proj x x n).
    rewrite (b3r_one_proj n).
    rewrite (b3r_zero_proj n).
    apply (Qlt_le_trans (1 # 2) (1 + projT1 x n * projT1 x n) (1 + projT1 x n * projT1 x n - 0)).
    + apply (Qlt_le_trans (1 # 2) 1 (1 + projT1 x n * projT1 x n)).
      * unfold Qlt. simpl. lia.
      * apply (Qle_plus_nonneg_r 1 (projT1 x n * projT1 x n)).
        apply (Qsquare_nonneg (projT1 x n)).
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* Part 6：几何衰减                                            *)
(* ============================================================ *)
(* (1/2)^d ≤ 1（0 ≤ 1/2 ≤ 1） *)
Lemma b3r_half_pow_le1 : forall (d : nat), Qle (q_pow (1 # 2) d) 1.
Proof.
  intros d.
  apply (Qle_trans _ (q_pow 1 d) _).
  - apply q_pow_mono.
    + unfold Qle. simpl. lia.
    + unfold Qle. simpl. lia.
  - apply qeq_imp_qle. apply q_pow_one.
Qed.

(* 衰减：(1/2)^m ≤ e（e > 0，m ≥ N）：经 q_pow_arch *)
Lemma b3r_geom_decay : forall (e : Q), Qlt 0 e ->
  sigT (fun N : nat => forall m : nat, (N <= m)%nat -> Qle (q_pow (1 # 2) m) e).
Proof.
  intros e He.
  assert (H1 : Qle 0 1) by (unfold Qle; simpl; lia).
  destruct (q_pow_arch 1 e H1 He) as [t Ht].
  exists t.
  intros m Hm.
  assert (Hm' : m = (t + (m - t))%nat) by lia.
  rewrite Hm'.
  rewrite (atan_q_pow_add (1 # 2) t (m - t)).
  apply (Qle_trans _ (q_pow (1 # 2) t * 1) _).
  - apply (b3_qmult_le_l (q_pow (1 # 2) (m - t)) 1 (q_pow (1 # 2) t)).
    + apply q_pow_nonneg. unfold Qle. simpl. lia.
    + apply b3r_half_pow_le1.
  - apply (Qle_trans _ (q_pow (1 # 2) t) _).
    + apply qeq_imp_qle. ring.
    + apply Qlt_le_weak.
      rewrite (Qmult_1_l (q_pow (1 # 2) t)) in Ht.
      exact Ht.
Qed.

(* k 小性：Cb·Qinv(4(Cb+1)) ≤ 1/4 *)
Lemma b3r_CbK : Qle (b3r_Cb * Qinv (4 * (b3r_Cb + 1))) (1 # 4).
Proof.
  set (d := 4 * (b3r_Cb + 1)).
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply (Qmult_lt_0_compat 4 (b3r_Cb + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (b3r_Cb + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (b3r_Cb + 1)).
        * apply qeq_imp_qle. ring.
        * apply Qplus_le_compat. apply b3r_Cb0. apply Qle_refl. }
  assert (Hdnz : ~ d == 0) by (apply q_neq_of_lt; exact Hd0).
  assert (Hinv0 : Qle 0 (Qinv d)).
  { apply (Qlt_le_weak 0 (Qinv d)). apply Qinv_lt_0_compat. exact Hd0. }
  apply (Qle_trans _ (Qmult (b3r_Cb + 1) (Qinv d)) _).
  - apply (Qmult_le_compat_r b3r_Cb (b3r_Cb + 1) (Qinv d)).
    + apply (Qle_trans _ (b3r_Cb + 0) _).
      * apply qeq_imp_qle. ring.
      * apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia.
    + exact Hinv0.
  - assert (H44 : (1 # 4) * 4 == 1).
    { unfold Qeq. simpl. lia. }
    assert (Hmid : (1 # 4) * d == b3r_Cb + 1).
    { unfold d.
      transitivity (((1 # 4) * 4) * (b3r_Cb + 1)).
      - apply Qeq_sym. apply (Qmult_assoc (1 # 4) 4 (b3r_Cb + 1)).
      - rewrite H44. ring. }
    assert (Hdd : d * Qinv d == 1).
    { apply (Qmult_inv_r d Hdnz). }
    apply qeq_imp_qle.
    transitivity ((1 # 4) * (d * Qinv d)).
    + transitivity (((1 # 4) * d) * Qinv d).
      * rewrite Hmid. reflexivity.
      * apply Qeq_sym. apply (Qmult_assoc (1 # 4) d (Qinv d)).
    + rewrite Hdd. ring.
Qed.

(* 逐点核心界：|S_n(u+h) − S_n(u) − h·Qinv(1+u²)|
   ≤ Cb·|h|² + |h|·(1/2)^{2(Sn)}（|u| ≤ 1/2，|h| ≤ 1/4） *)
Lemma b3r_core : forall (n : nat) (u h : Q),
  Qle (Qabs u) (1 # 2) -> Qle (Qabs h) (1 # 4) ->
  Qle (Qabs (arctan_partial n (u + h) - arctan_partial n u - h * Qinv (1 + u * u)))
      (Qplus (Qmult b3r_Cb (Qmult (Qabs h) (Qabs h)))
             (Qmult (Qabs h) (q_pow (1 # 2) (2 * Datatypes.S n)))).
Proof.
  intros n u h Hu Hh.
  assert (Hu34 : Qle (Qabs u) (3 # 4)).
  { apply (Qle_trans _ (1 # 2) _); [exact Hu | unfold Qle; simpl; lia]. }
  assert (Huh34 : Qle (Qabs (u + h)) (3 # 4)).
  { apply (Qle_trans _ (Qabs u + Qabs h) _).
    - apply Qabs_triangle.
    - apply (Qle_trans _ (Qplus (1 # 2) (1 # 4)) _).
      + apply Qplus_le_compat. exact Hu. exact Hh.
      + apply qeq_imp_qle. unfold Qeq. simpl. lia. }
  assert (Hdec : arctan_partial n (u + h) - arctan_partial n u - h * Qinv (1 + u * u) ==
        (arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u) +
        h * (b3_dsum n u - Qinv (1 + u * u))).
  { ring. }
  apply (Qle_trans _ (Qplus
      (Qabs (arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u))
      (Qabs (h * (b3_dsum n u - Qinv (1 + u * u))))) _).
  - apply (Qle_trans _ (Qabs
        ((arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u) +
         h * (b3_dsum n u - Qinv (1 + u * u)))) _).
    + apply qeq_imp_qle. apply Qabs_wd. exact Hdec.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (Qplus
        (Qmult b3r_Cb (Qmult (Qabs h) (Qabs h)))
        (Qmult (Qabs h) (Qabs (b3_dsum n u - Qinv (1 + u * u))))) _).
    + apply Qplus_le_compat.
      * assert (Hd : (u + h) - u == h) by ring.
        apply (Qle_trans _ (Qmult b3r_Cb (Qmult (Qabs ((u + h) - u)) (Qabs ((u + h) - u)))) _).
        -- apply (Qle_trans _ (Qabs (arctan_partial n (u + h) - arctan_partial n u
                                      - (u + h - u) * b3_dsum n u)) _).
           ++ apply qeq_imp_qle. apply Qabs_wd. rewrite Hd. reflexivity.
           ++ apply (b3r_var34 n u (u + h) Hu34 Huh34).
        -- apply qeq_imp_qle.
           rewrite Hd.
           reflexivity.
      * apply qeq_imp_qle.
        rewrite (Qabs_Qmult h (b3_dsum n u - Qinv (1 + u * u))).
        reflexivity.
    + apply (Qle_trans _ (Qplus
        (Qmult b3r_Cb (Qmult (Qabs h) (Qabs h)))
        (Qmult (Qabs h) (q_pow (Qabs u) (2 * Datatypes.S n)))) _).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (b3_qmult_le_l (Qabs (b3_dsum n u - Qinv (1 + u * u)))
                 (q_pow (Qabs u) (2 * Datatypes.S n)) (Qabs h)).
           ++ apply Qabs_nonneg.
           ++ apply (b3_dsum_rem_le n u).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (b3_qmult_le_l (q_pow (Qabs u) (2 * Datatypes.S n))
                 (q_pow (1 # 2) (2 * Datatypes.S n)) (Qabs h)).
           ++ apply Qabs_nonneg.
           ++ apply q_pow_mono.
              ** apply Qabs_nonneg.
              ** exact Hu.
Qed.

(* ============================================================ *)
(* Part 7：arctan_partial 对 Qeq 的形态（投影链在 partial 内重写）*)
(* ============================================================ *)
(* arctan_term/arctan_partial 对 Qeq 的形态（供投影链在 arctan_partial 内重写） *)
Lemma b3r_ap_term_wd : forall (k : nat) (x y : Q), x == y -> arctan_term k x == arctan_term k y.
Proof. intros k x y H. unfold arctan_term. rewrite H. reflexivity. Qed.
Lemma b3r_ap_wd : forall (n : nat) (x y : Q), x == y -> arctan_partial n x == arctan_partial n y.
Proof.
  intros n. induction n as [| n IH]; intros x y H; simpl.
  - apply b3r_ap_term_wd. exact H.
  - apply Qplus_comp.
    + apply IH. exact H.
    + apply b3r_ap_term_wd. exact H.
Qed.
#[export] Instance b3r_ap_proper : Proper (eq ==> Qeq ==> Qeq) arctan_partial.
Proof.
  intros n m Hnm x y Hxy. destruct Hnm. apply b3r_ap_wd. exact Hxy.
Qed.

(* ============================================================ *)
(* Part 8：Real 层主定理 real_arctan_deriv_linear（|x| ≤ 1/2）   *)
(* ============================================================ *)
Lemma real_arctan_deriv_linear :
  forall (x : Real),
  forall (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) (Qinv 2)),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                           (b3r_one_sq_real_pos x)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hxb eps Heps.
  set (k := Qinv (4 * (b3r_Cb + 1))).
  assert (HCb0 : Qle 0 b3r_Cb) by apply b3r_Cb0.
  assert (Hk_pos : Qlt 0 k).
  { unfold k. apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (b3r_Cb + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (b3r_Cb + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (b3r_Cb + 1)).
        * apply qeq_imp_qle. ring.
        * apply Qplus_le_compat. exact HCb0. apply Qle_refl. }
  assert (HCbK : Qle (b3r_Cb * k) (1 # 4)).
  { unfold k. apply b3r_CbK. }
  assert (Hk0 : Qle 0 k) by (apply Qlt_le_weak; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  set (delta := real_min (real_const (1 # 4)) (real_mult eps rk)).
  exists delta. split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1. unfold Qlt. simpl. lia.
    + apply real_mult_positive. exact Heps. exact Hrk_pos.
  - intros h Hh Hxh eps' Heps'.
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    assert (Hh_l : real_lt (real_abs h) (real_const (1 # 4)))
      by (unfold delta in Hh; apply (real_min_lt_l h (real_const (1 # 4)) (real_mult eps rk)); exact Hh).
    assert (Hh_r : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; apply (real_min_lt_r h (real_const (1 # 4)) (real_mult eps rk)); exact Hh).
    destruct Hh_l as [e2 [He2 [N2 HN2]]].
    destruct Hh_r as [e3 [He3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)) as [Ninv HNinv].
    assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
    { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (b3r_geom_decay (Qmult eps1' (Qinv 2)) Hh2) as [Ng HNg].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. exact Hh2. }
    exists eta. split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) (Nat.max Ninv Ng)).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hninv : (Ninv <= n)%nat) by lia.
      assert (Hng : (Ng <= n)%nat) by lia.
      set (un := projT1 x n). set (hn := projT1 h n).
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (yn := un + hn).
      set (Dform := arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)).
      set (wreal := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
      (* 正性：en ≥ 0、en' > eps1' *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (HN1'e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* 见证→点界：|hn| ≤ 1/4、|hn| ≤ en·k *)
      assert (Hq2 : Qlt e2 (Qminus (1 # 4) (Qabs hn))).
      { apply (Qlt_le_trans e2 (Qminus (projT1 (real_const (1 # 4)) n) (projT1 (real_abs h) n))
                             (Qminus (1 # 4) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n). cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn14 : Qlt (Qabs hn) (1 # 4)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (1 # 4) e2) (1 # 4)).
        - apply (q_lt_minus_shift e2 (1 # 4) (Qabs hn)). exact Hq2.
        - assert (He20 : Qle 0 e2) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He2).
          apply (Qle_trans (Qminus (1 # 4) e2) (Qplus (Qminus (1 # 4) e2) e2) (1 # 4)).
          + apply (Qle_trans (Qminus (1 # 4) e2) (Qplus (Qminus (1 # 4) e2) 0)
                             (Qplus (Qminus (1 # 4) e2) e2)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus (1 # 4) e2) (Qminus (1 # 4) e2) 0 e2
                     (Qle_refl _) He20).
          + apply qeq_imp_qle. ring. }
      assert (Hhn14le : Qle (Qabs hn) (1 # 4)) by (apply Qlt_le_weak; exact Hhn14).
      assert (Hhn1 : Qle (Qabs hn) 1).
      { apply (Qle_trans _ (1 # 4) _); [exact Hhn14le | unfold Qle; simpl; lia]. }
      assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans e3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                             (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n).
          unfold rk, en.
          setoid_rewrite (real_mult_proj eps (real_const k) n).
          cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
        - apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)). exact Hq3.
        - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
          apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) e3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) 0)
                             (Qplus (Qminus (Qmult en k) e3) e3)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) e3) (Qminus (Qmult en k) e3) 0 e3
                     (Qle_refl _) He30).
          + apply qeq_imp_qle. ring. }
      assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* 域：|un| ≤ 1/2 *)
      assert (Hun12 : Qle (Qabs un) (1 # 2)).
      { apply (QleT'_to_Qle (Qabs un) (Qinv 2)). apply Hxb. }
      assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
      assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
      { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
      (* 投影恒等（A 侧） *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h wreal))))) n ==
                  Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
      { unfold yn, un, hn, wreal.
        rewrite (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))))) n).
        rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))) n).
        rewrite (real_opp_proj (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))) n).
        rewrite (real_plus_proj (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))) n).
        rewrite (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        rewrite (arctan_real_proj x (b3r_half_dom x Hxb) n).
        rewrite (real_plus_proj x h n).
        rewrite (HNinv n Hninv).
        rewrite (real_plus_proj real_one (real_mult x x) n).
        rewrite (real_mult_proj x x n).
        rewrite (b3r_one_proj n).
        apply Qabs_wd. ring. }
      (* B 侧投影 *)
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [real_zero real_const projT1]. ring. }
      (* 点主界 1：Cb·|hn|² ≤ en·|hn|·(1/4) *)
      assert (Hcbn : Qle (Qmult b3r_Cb (Qmult (Qabs hn) (Qabs hn)))
                         (Qmult (Qmult en (Qabs hn)) (1 # 4))).
      { apply (Qle_trans _ (Qmult b3r_Cb (Qmult (Qmult en k) (Qabs hn))) _).
        - (* |hn|·|hn| ≤ (en·k)·|hn|（右乘 |hn| ≥ 0），再左乘 Cb ≥ 0 *)
          apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                               (Qmult (Qmult en k) (Qabs hn)) b3r_Cb).
          + exact HCb0.
          + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
            * exact Hhn_kle.
            * exact Hhvn0.
        - (* Cb·((en·k)·|hn|) == en·|hn|·(Cb·k) ≤ en·|hn|·(1/4) *)
          apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult b3r_Cb k)) _).
          + apply qeq_imp_qle. ring.
          + apply (b3_qmult_le_l (Qmult b3r_Cb k) (1 # 4) (Qmult en (Qabs hn))).
            * exact Henhn0.
            * exact HCbK. }
      (* 点主界 2：(1/2)^{2(Sn)} ≤ eta（n ≥ Ng ⟹ 2(Sn) ≥ Ng） *)
      assert (Hdec2 : Qle (q_pow (1 # 2) (2 * Datatypes.S n)) eta).
      { apply (HNg ((2 * Datatypes.S n)%nat)). lia. }
      assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n)))
                           (q_pow (1 # 2) (2 * Datatypes.S n))).
      { apply (Qle_trans _ (Qmult 1 (q_pow (1 # 2) (2 * Datatypes.S n))) _).
        - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow (1 # 2) (2 * Datatypes.S n))).
          + exact Hhn1.
          + apply q_pow_nonneg. unfold Qle. simpl. lia.
        - apply qeq_imp_qle. ring. }
      (* 主点界：|D_n| ≤ en·|hn| + eta *)
      assert (Hm1 : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult b3r_Cb (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n))))).
      { unfold yn. apply (b3r_core n un hn Hun12 Hhn14le). }
      assert (Hm2 : Qle
        (Qplus (Qmult b3r_Cb (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n))))).
      { apply Qplus_le_compat. exact Hcbn. apply Qle_refl. }
      assert (Hm3 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow (1 # 2) (2 * Datatypes.S n)))).
      { apply Qplus_le_compat. apply Qle_refl. exact Hpow14. }
      assert (Hm4 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow (1 # 2) (2 * Datatypes.S n)))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)).
      { apply Qplus_le_compat. apply Qle_refl. exact Hdec2. }
      assert (Hm5 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
        - apply (b3_qmult_le_l (1 # 4) 1 (Qmult en (Qabs hn))).
          + exact Henhn0.
          + unfold Qle. simpl. lia.
        - apply qeq_imp_qle. ring. }
      assert (Hm6 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply Qplus_le_compat. exact Hm5. apply Qle_refl. }
      assert (Hmain : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply (Qle_trans _ (Qplus (Qmult b3r_Cb (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n)))) _).
        - exact Hm1.
        - apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow (1 # 2) (2 * Datatypes.S n)))) _).
          + exact Hm2.
          + apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
                 (q_pow (1 # 2) (2 * Datatypes.S n))) _).
            * exact Hm3.
            * apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta) _).
              -- exact Hm4.
              -- exact Hm6. }
      (* Hfin：eta < (en·|hn| + en') − |D_n| *)
      assert (Hfin : Qlt eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en')
                  (Qplus (Qmult en (Qabs hn)) eta))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
        - (* eta < (en|hn|+en') − (en|hn|+eta) == en' − 2eta，由 en' > eps1' == 2eta *)
          apply (proj2 (Qlt_minus_iff eta
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)))).
          assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en')
                               (Qplus (Qmult en (Qabs hn)) eta)) eta ==
                        Qminus en' (Qmult eta (1 + 1))) by ring.
          rewrite Heq.
          apply (proj1 (Qlt_minus_iff (Qmult eta (1 + 1)) en')).
          assert (HX : Qmult eta (1 + 1) == eps1') by (unfold eta; field).
          rewrite HX.
          apply QltT_to_Qlt. exact HN1'e.
        - apply (proj2 (Qle_minus_iff
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta))
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform)))).
          assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
          exact Hmain. }
      (* 投影桥（RHS − LHS）==（B − |D|） *)
      assert (Hrepl2 : Qeq
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h wreal))))) n))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                           (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                                       (real_mult h wreal))))) n)
                           (Qabs Dform) Hrepl). }
      apply Qlt_to_QltT.
      assert (Hqfinal : Qlt eta
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h wreal))))) n))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3r_half_dom x Hxb))
                              (real_mult h wreal))))) n))).
        - exact Hfin.
        - apply qeq_imp_qle. apply Qeq_sym. exact Hrepl2. }
      exact Hqfinal.

Qed.

(* ============================================================ *)
(* B3a Real 层 r 参数化主定理    *)
(* （|x| ≤ r < 1；b3rr_real_arctan_deriv_linear 收尾）；          *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b3_arctanp/sc2_b3_real_r.v *)
(* 20 Qed；零公理面、零承认件。                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* Part A：通用几何衰减：0 ≤ q < 1 ⟹ ∃N，m ≥ N ⟹ q^m ≤ e        *)
(* 路线：q^m·(1 + m(1−q)) ≤ 1（几何和 1−q^m ≥ m(1−q)q^{m−1}），  *)
(*   q^m ≤ 1/(1+m(1−q)) ≤ e（阿基米德取 m）。                     *)
(* ============================================================ *)

(* (1−q)·Σ_{j=0}^{m−1} q^j == 1 − q^m *)
Lemma b3rr_psumpow_geom : forall (q : Q) (m : nat),
  (1 - q) * b3r_psum m (fun j : nat => q_pow q j) == 1 - q_pow q m.
Proof.
  intros q m.
  induction m as [| m IH].
  - simpl. ring.
  - rewrite (b3r_psum_succ m (fun j : nat => q_pow q j)).
    rewrite (q_pow_succ q m).
    transitivity ((1 - q) * b3r_psum m (fun j : nat => q_pow q j) + (1 - q) * q_pow q m).
    + ring.
    + rewrite IH. ring.
Qed.

(* 0 ≤ q ≤ 1、j ≤ m ⟹ q^{m} ≤ q^{j}（幂对指数递减） *)
Lemma b3rr_pow_decr : forall (q : Q) (j m : nat),
  Qle 0 q -> Qle q 1 -> (j <= m)%nat ->
  Qle (q_pow q m) (q_pow q j).
Proof.
  intros q j m Hq0 Hq1 Hjm.
  destruct (Nat.le_exists_sub j m Hjm) as [d Hd].
  assert (Hm : m = (j + d)%nat) by lia.
  rewrite Hm.
  rewrite (atan_q_pow_add q j d).
  apply (Qle_trans _ (q_pow q j * 1) _).
  - apply (b3_qmult_le_l (q_pow q d) 1 (q_pow q j)).
    + apply q_pow_nonneg. exact Hq0.
    + apply (Qle_trans _ (q_pow 1 d) _).
      * apply q_pow_mono. exact Hq0. exact Hq1.
      * apply qeq_imp_qle. apply q_pow_one.
  - apply qeq_imp_qle. ring.
Qed.

(* 0 ≤ q ≤ 1 ⟹ m·q^{m−1} ≤ Σ_{j<m} q^j（每项 ≥ q^{m−1}） *)
Lemma b3rr_psum_low : forall (q : Q) (m : nat),
  Qle 0 q -> Qle q 1 ->
  Qle (Qmult (Z.of_nat m # 1) (q_pow q (m - 1)))
      (b3r_psum m (fun j : nat => q_pow q j)).
Proof.
  intros q m Hq0 Hq1.
  destruct m as [| m].
  - simpl. apply qeq_imp_qle. ring.
  - apply (Qle_trans _ (b3r_psum (Datatypes.S m) (fun _ : nat => q_pow q m)) _).
    + (* (S m)#1·q^{(S m)−1} ≤ psum(S m)(const q^m)：指数 (S m)−1 == m，psum-const 闭式 *)
      apply qeq_imp_qle.
      assert (Hsm : (Datatypes.S m - 1)%nat = m) by lia.
      rewrite Hsm.
      rewrite (b3r_psum_const (Datatypes.S m) (q_pow q m)).
      rewrite (b3_qn_succ m).
      ring.
    + apply b3r_psum_le. intros j Hj.
      apply (b3rr_pow_decr q j m Hq0 Hq1). lia.
Qed.

(* a ≤ b ⟹ 0 ≤ b − a *)
Lemma b3rr_sub_nonneg : forall (a b : Q), Qle a b -> Qle 0 (b - a).
Proof.
  intros a b Hab.
  apply (Qle_trans _ (Qplus b (Qopp a)) _).
  - apply (Qle_trans _ (Qplus a (Qopp a)) _).
    + apply qeq_imp_qle. ring.
    + apply (Qplus_le_compat a b (Qopp a) (Qopp a) Hab (Qle_refl _)).
  - apply qeq_imp_qle. ring.
Qed.

(* 0 ≤ q ≤ 1 ⟹ q^m·(1 + m·(1−q)) ≤ 1 *)
Lemma b3rr_pow_lin : forall (q : Q) (m : nat),
  Qle 0 q -> Qle q 1 ->
  Qle (Qmult (q_pow q m) (Qplus 1 (Qmult (Z.of_nat m # 1) (1 - q)))) 1.
Proof.
  intros q m Hq0 Hq1.
  destruct m as [| m].
  - (* m = 0 *)
    simpl. apply qeq_imp_qle. ring.
  - (* m = S m；A := q^{S m}，g := (S m)#1
       链：A(1+g(1−q)) == A + (1−q)gA ≤ A + (1−q)g·q^m ≤ A + (1−q)psum
           == A + 1 − A == 1 *)
    set (g := Z.of_nat (Datatypes.S m) # 1).
    set (A := q_pow q (Datatypes.S m)).
    assert (Hq1ge0 : Qle 0 (1 - q)).
    { apply (b3rr_sub_nonneg q 1). exact Hq1. }
    assert (Hg0 : Qle 0 g) by (unfold g; unfold Qle; simpl; lia).
    assert (HdecA : Qle A (q_pow q m)).
    { unfold A. apply (b3rr_pow_decr q m (Datatypes.S m) Hq0 Hq1). lia. }
    assert (Hmid1 : Qle (Qmult (1 - q) (Qmult g A))
                       (Qmult (1 - q) (Qmult g (q_pow q m)))).
    { apply (b3_qmult_le_l (Qmult g A) (Qmult g (q_pow q m)) (1 - q)).
      - exact Hq1ge0.
      - apply (b3_qmult_le_l A (q_pow q m) g). exact Hg0. exact HdecA. }
    assert (Hmid2 : Qle (Qmult (1 - q) (Qmult g (q_pow q m)))
                       (Qmult (1 - q) (b3r_psum (Datatypes.S m) (fun j : nat => q_pow q j)))).
    { apply (b3_qmult_le_l (Qmult g (q_pow q m))
                           (b3r_psum (Datatypes.S m) (fun j : nat => q_pow q j)) (1 - q)).
      - exact Hq1ge0.
      - unfold g.
        assert (Hexp : (Datatypes.S m - 1)%nat = m) by lia.
        rewrite <- (f_equal (q_pow q) Hexp).
        apply (b3rr_psum_low q (Datatypes.S m) Hq0 Hq1). }
    assert (Hgeom : Qmult (1 - q) (b3r_psum (Datatypes.S m) (fun j : nat => q_pow q j)) == 1 - A).
    { unfold A. apply (b3rr_psumpow_geom q (Datatypes.S m)). }
    apply (Qle_trans _ (Qplus A (Qmult (1 - q) (Qmult g A))) _).
    + apply qeq_imp_qle. unfold A, g. ring.
    + apply (Qle_trans _ (Qplus A (Qmult (1 - q) (Qmult g (q_pow q m)))) _).
      * apply Qplus_le_compat. apply Qle_refl. exact Hmid1.
      * apply (Qle_trans _ (Qplus A (Qmult (1 - q)
                       (b3r_psum (Datatypes.S m) (fun j : nat => q_pow q j)))) _).
        -- apply Qplus_le_compat. apply Qle_refl. exact Hmid2.
        -- apply (Qle_trans _ (Qplus A (1 - A)) _).
           ++ apply Qplus_le_compat. apply Qle_refl. apply qeq_imp_qle. exact Hgeom.
           ++ apply qeq_imp_qle. unfold A. ring.
Qed.

(* 通用几何衰减：0 ≤ q < 1 ⟹ ∃N，m ≥ N ⟹ q^m ≤ e *)
Lemma b3rr_qdecay : forall (q e : Q), Qle 0 q -> Qlt q 1 -> Qlt 0 e ->
  sigT (fun N : nat => forall m : nat, (N <= m)%nat -> Qle (q_pow q m) e).
Proof.
  intros q e Hq0 Hq1 He.
  assert (Hd0 : Qlt 0 (1 - q)).
  { apply (proj1 (Qlt_minus_iff q 1)). exact Hq1. }
  assert (Hdge0 : Qle 0 (1 - q)) by (apply Qlt_le_weak; exact Hd0).
  assert (Hq1le : Qle q 1) by (apply Qlt_le_weak; exact Hq1).
  assert (Hdnz : ~ 1 - q == 0) by (apply q_neq_of_lt; exact Hd0).
  assert (Henz : ~ e == 0) by (apply q_neq_of_lt; exact He).
  assert (Hep : Qlt 0 (Qmult e (1 - q))).
  { apply (Qmult_lt_0_compat e (1 - q)). exact He. exact Hd0. }
  assert (HepT : QltT 0 (Qinv (Qmult e (1 - q)))).
  { apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact Hep. }
  destruct (Qarchimedean (Qinv (Qmult e (1 - q)))) as [p Hp].
  exists (Pos.to_nat p).
  intros m Hm.
  (* m#1 ≥ p#1 *)
  assert (Hmp : Qle (Z.pos p # 1) (Z.of_nat m # 1)).
  { rewrite <- (positive_nat_Z p). apply (Qle_of_nat (Pos.to_nat p) m). exact Hm. }
  (* 1 + m(1−q) ≥ Qinv e *)
  assert (Hbig : Qle (Qinv e) (1 + (Z.of_nat m # 1) * (1 - q))).
  { apply (Qle_trans _ (Qmult (Z.of_nat m # 1) (1 - q)) _).
    - apply (Qle_trans _ (Qmult (Z.pos p # 1) (1 - q)) _).
      + (* (p#1)(1−q) > Qinv e：Hp 乘 (1−q)（Qinv 分解 + 消去） *)
        apply Qlt_le_weak.
        apply (Qle_lt_trans _ (Qmult (Qinv (Qmult e (1 - q))) (1 - q)) _).
        * apply qeq_imp_qle. field.
          split; [ exact Hdnz | exact Henz ].
        * apply (Qmult_lt_compat_r (Qinv (Qmult e (1 - q))) (Z.pos p # 1) (1 - q)).
          -- exact Hd0.
          -- exact Hp.
      + apply (Qmult_le_compat_r (Z.pos p # 1) (Z.of_nat m # 1) (1 - q)).
        * exact Hmp.
        * exact Hdge0.
    - apply (Qle_trans _ (Qplus (Qmult (Z.of_nat m # 1) (1 - q)) 1) _).
      + apply (Qle_plus_nonneg_r (Qmult (Z.of_nat m # 1) (1 - q)) 1). unfold Qle. simpl. lia.
      + apply qeq_imp_qle. ring.
  }
  assert (Hden0 : Qlt 0 (1 + (Z.of_nat m # 1) * (1 - q))).
  { apply (Qlt_le_trans 0 1 (1 + (Z.of_nat m # 1) * (1 - q))).
    - unfold Qlt. simpl. lia.
    - apply (Qle_plus_nonneg_r 1 (Qmult (Z.of_nat m # 1) (1 - q))).
      apply (Qmult_le_0_compat (Z.of_nat m # 1) (1 - q)).
      + unfold Qle. simpl. lia.
      + exact Hdge0. }
  assert (Hdennz : ~ 1 + (Z.of_nat m # 1) * (1 - q) == 0) by (apply q_neq_of_lt; exact Hden0).
  assert (Hinv0 : Qle 0 (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))).
  { apply (Qlt_le_weak 0 (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))).
    apply Qinv_lt_0_compat. exact Hden0. }
  assert (Hlin := b3rr_pow_lin q m Hq0 Hq1le).
  apply (Qle_trans _ (Qinv (1 + (Z.of_nat m # 1) * (1 - q))) _).
  - apply (Qle_trans _ (Qmult (Qmult (q_pow q m) (1 + (Z.of_nat m # 1) * (1 - q)))
                              (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))) _).
    + apply qeq_imp_qle.
      transitivity (Qmult (q_pow q m)
                          (Qmult (1 + (Z.of_nat m # 1) * (1 - q))
                                 (Qinv (1 + (Z.of_nat m # 1) * (1 - q))))).
      * rewrite (Qmult_inv_r (1 + (Z.of_nat m # 1) * (1 - q)) Hdennz). ring.
      * apply (Qmult_assoc (q_pow q m) (1 + (Z.of_nat m # 1) * (1 - q))
                           (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))).
    + apply (Qle_trans _ (Qmult 1 (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))) _).
      * apply (Qmult_le_compat_r (Qmult (q_pow q m) (1 + (Z.of_nat m # 1) * (1 - q))) 1
               (Qinv (1 + (Z.of_nat m # 1) * (1 - q)))).
        -- exact Hlin.
        -- exact Hinv0.
      * apply qeq_imp_qle. ring.
  - (* Qinv(1+m(1−q)) ≤ e：contravar + Qinv 对合 *)
    apply (Qle_trans _ (Qinv (Qinv e)) _).
    + apply (q_inv_le_contravar (1 + (Z.of_nat m # 1) * (1 - q)) (Qinv e)).
      * exact Hden0.
      * apply Qinv_lt_0_compat. exact He.
      * exact Hbig.
    + apply qeq_imp_qle.
      field.
      apply q_neq_of_lt. exact He.
Qed.







(* ============================================================ *)
(* Part B：域证书 + 通用 M 变差界 + r 逐点核心界                 *)
(* ============================================================ *)

(* 域证书：|x| ≤ r（逐点 QleT'）且 r ≤ 1 ⟹ |x| ≤ 1 *)
Lemma b3rr_dom_lt1 : forall (x : Real) (r : Q),
  (forall n : nat, QleT' (Qabs (projT1 x n)) r) ->
  QleT' r 1 ->
  forall n : nat, QleT' (Qabs (projT1 x n)) 1.
Proof.
  intros x r Hxr Hr1 n.
  apply (qleT'_trans (Qabs (projT1 x n)) r 1).
  - apply Hxr.
  - exact Hr1.
Qed.

(* 通用变差常量 C2(M) := 2·M·Qinv((1−M²)²) *)
Definition b3rr_C2 (M : Q) : Q :=
  Qmult (Z.of_nat 2 # 1) (Qmult M
    (Qinv ((1 - M * M) * (1 - M * M)))).

(* 0 ≤ M、M² < 1 ⟹ |S_n(y) − S_n(x) − (y−x)·b3_dsum n x| ≤ C2(M)·|y−x|² *)
Lemma b3rr_varM : forall (n : nat) (x y M : Q),
  Qle 0 M -> Qlt M 1 -> Qle (Qabs x) M -> Qle (Qabs y) M ->
  Qle (Qabs (arctan_partial n y - arctan_partial n x - (y - x) * b3_dsum n x))
      (Qmult (b3rr_C2 M) (Qmult (Qabs (y - x)) (Qabs (y - x)))).
Proof.
  intros n x y M HM0 HM1 Hx Hy.
  set (q := M * M).
  assert (Hq0 : Qle 0 q).
  { unfold q. apply (Qmult_le_0_compat M M). exact HM0. exact HM0. }
  assert (Hq1 : Qlt q 1).
  { unfold q.
    apply (Qle_lt_trans _ (M * 1) _).
    - apply (b3_qmult_le_l M 1 M).
      + exact HM0.
      + apply Qlt_le_weak. exact HM1.
    - apply (Qle_lt_trans _ M _).
      + apply qeq_imp_qle. ring.
      + exact HM1. }
  apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult M (b3_wsum n q)))
                                   (Qabs (y - x))) (Qabs (y - x))) _).
  - apply (Qle_trans _
      (Qmult (Qmult (Z.of_nat 2 # 1) (Qmult M (b3_wsum n q)))
             (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
    + apply (b3r_partial_var n x y M HM0 Hx Hy).
    + apply qeq_imp_qle. unfold q. ring.
  - apply (Qle_trans _
      (Qmult (Qmult (Z.of_nat 2 # 1)
              (Qmult M (Qinv ((1 - q) * (1 - q)))))
             (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
    + assert (Hw : Qle (b3_wsum n q) (Qinv ((1 - q) * (1 - q))))
        by (apply (b3_wsum_bound n q Hq0 Hq1)).
      assert (Hc0 : Qle 0 (Qmult (Z.of_nat 2 # 1) M))
        by (apply (Qmult_le_0_compat (Z.of_nat 2 # 1) M);
            [unfold Qle; simpl; lia | exact HM0]).
      assert (Hvv0 : Qle 0 (Qmult (Qabs (y - x)) (Qabs (y - x))))
        by (apply (Qmult_le_0_compat (Qabs (y - x)) (Qabs (y - x)));
            [apply Qabs_nonneg | apply Qabs_nonneg]).
      apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) M) (b3_wsum n q))
                                (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
      * apply qeq_imp_qle. ring.
      * apply (Qle_trans _ (Qmult (Qmult (Qmult (Z.of_nat 2 # 1) M)
                                         (Qinv ((1 - q) * (1 - q))))
                                  (Qmult (Qabs (y - x)) (Qabs (y - x)))) _).
        -- apply (Qmult_le_compat_r (Qmult (Qmult (Z.of_nat 2 # 1) M) (b3_wsum n q))
                   (Qmult (Qmult (Z.of_nat 2 # 1) M) (Qinv ((1 - q) * (1 - q))))
                   (Qmult (Qabs (y - x)) (Qabs (y - x)))).
           ++ apply (b3_qmult_le_l (b3_wsum n q) (Qinv ((1 - q) * (1 - q)))
                                    (Qmult (Z.of_nat 2 # 1) M)).
              ** exact Hc0.
              ** exact Hw.
           ++ exact Hvv0.
        -- apply qeq_imp_qle. unfold q. ring.
    + apply qeq_imp_qle. unfold b3rr_C2. unfold q. ring.
Qed.
(* ============================================================ *)
(* Part C1：(1/2) 算术 + C2 正性 + 通用 k 小性                   *)
(* ============================================================ *)

Lemma b3rr_half2_l : (1 # 2) * (Z.of_nat 2 # 1) == 1.
Proof. unfold Qeq. simpl. lia. Qed.

Lemma b3rr_half2_r : (Z.of_nat 2 # 1) * (1 # 2) == 1.
Proof. unfold Qeq. simpl. lia. Qed.

(* (2#1)·((1#2)·z) == z *)
Lemma b3rr_twice_half : forall (z : Q), (Z.of_nat 2 # 1) * ((1 # 2) * z) == z.
Proof.
  intros z.
  transitivity (Qmult (Qmult (Z.of_nat 2 # 1) (1 # 2)) z).
  - apply (Qmult_assoc (Z.of_nat 2 # 1) (1 # 2) z).
  - rewrite b3rr_half2_r. ring.
Qed.

(* (1#2)·((2#1)·z) == z *)
Lemma b3rr_half_double : forall (z : Q), (1 # 2) * ((Z.of_nat 2 # 1) * z) == z.
Proof.
  intros z.
  transitivity (Qmult (Qmult (1 # 2) (Z.of_nat 2 # 1)) z).
  - apply (Qmult_assoc (1 # 2) (Z.of_nat 2 # 1) z).
  - rewrite b3rr_half2_l. ring.
Qed.

(* r ≤ 1 ⟹ r ≤ (1+r)/2 *)
Lemma b3rr_r_le_half : forall (r : Q), Qle r 1 -> Qle r ((1 # 2) * (1 + r)).
Proof.
  intros r Hr1.
  apply (Qle_trans _ (Qmult (1 # 2) ((Z.of_nat 2 # 1) * r)) _).
  - (* r == (1#2)(2r) *)
    apply qeq_imp_qle. apply Qeq_sym. apply (b3rr_half_double r).
  - (* (1#2)(2r) ≤ (1#2)(1+r)：2r ≤ 1+r（r ≤ 1） *)
    apply (b3_qmult_le_l ((Z.of_nat 2 # 1) * r) (1 + r) (1 # 2)).
    + unfold Qle. simpl. lia.
    + assert (H2 : (Z.of_nat 2 # 1) == 1 + 1) by (unfold Qeq; simpl; lia).
      rewrite H2.
      assert (Hr2 : (1 + 1) * r == r + r) by ring.
      rewrite Hr2.
      apply (Qplus_le_compat r 1 r r Hr1 (Qle_refl r)).
Qed.

(* r + (1−r)/2 == (1+r)/2 *)
Lemma b3rr_rc_half : forall (r : Q), r + (1 # 2) * (1 - r) == (1 # 2) * (1 + r).
Proof.
  intros r.
  apply (Qmult_inj_l (r + (1 # 2) * (1 - r)) ((1 # 2) * (1 + r)) (Z.of_nat 2 # 1)).
  - unfold Qeq. simpl. lia.
  - transitivity (1 + r).
    + (* 2·(r + (1#2)(1−r)) == 2r + (1−r) == 1 + r *)
      transitivity ((Z.of_nat 2 # 1) * r + (Z.of_nat 2 # 1) * ((1 # 2) * (1 - r))).
      * ring.
      * rewrite (b3rr_twice_half (1 - r)). ring.
    + (* 2·((1#2)(1+r)) == 1 + r *)
      rewrite (b3rr_twice_half (1 + r)).
      reflexivity.
Qed.

(* 0 ≤ M、M < 1 ⟹ 0 ≤ C2(M) *)
Lemma b3rr_C2_0 : forall (M : Q), Qle 0 M -> Qlt M 1 -> Qle 0 (b3rr_C2 M).
Proof.
  intros M HM0 HM1.
  unfold b3rr_C2.
  apply (Qmult_le_0_compat (Z.of_nat 2 # 1)
          (Qmult M (Qinv ((1 - M * M) * (1 - M * M))))).
  - unfold Qle. simpl. lia.
  - apply (Qmult_le_0_compat M (Qinv ((1 - M * M) * (1 - M * M)))).
    + exact HM0.
    + apply (Qlt_le_weak 0 (Qinv ((1 - M * M) * (1 - M * M)))).
      apply Qinv_lt_0_compat.
      (* 0 < (1−M²)²：0 < 1 − M²（M < 1、M ≥ 0） *)
      apply (Qmult_lt_0_compat (1 - M * M) (1 - M * M)).
      * apply (proj1 (Qlt_minus_iff (M * M) 1)).
        apply (Qle_lt_trans _ (M * 1) _).
        -- apply (b3_qmult_le_l M 1 M).
           ++ exact HM0.
           ++ apply Qlt_le_weak. exact HM1.
        -- apply (Qle_lt_trans _ M _).
           ++ apply qeq_imp_qle. ring.
           ++ exact HM1.
      * apply (proj1 (Qlt_minus_iff (M * M) 1)).
        apply (Qle_lt_trans _ (M * 1) _).
        -- apply (b3_qmult_le_l M 1 M).
           ++ exact HM0.
           ++ apply Qlt_le_weak. exact HM1.
        -- apply (Qle_lt_trans _ M _).
           ++ apply qeq_imp_qle. ring.
           ++ exact HM1.
Qed.

(* 通用 k 小性：0 ≤ C ⟹ C·Qinv(4(C+1)) ≤ 1/4 *)
Lemma b3rr_CK : forall (C : Q), Qle 0 C ->
  Qle (C * Qinv (4 * (C + 1))) (1 # 4).
Proof.
  intros C HC0.
  set (d := 4 * (C + 1)).
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply (Qmult_lt_0_compat 4 (C + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (C + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (C + 1)).
        * apply qeq_imp_qle. ring.
        * apply Qplus_le_compat. exact HC0. apply Qle_refl. }
  assert (Hdnz : ~ d == 0) by (apply q_neq_of_lt; exact Hd0).
  assert (Hinv0 : Qle 0 (Qinv d)).
  { apply (Qlt_le_weak 0 (Qinv d)). apply Qinv_lt_0_compat. exact Hd0. }
  apply (Qle_trans _ (Qmult (C + 1) (Qinv d)) _).
  - apply (Qmult_le_compat_r C (C + 1) (Qinv d)).
    + apply (Qle_trans _ (C + 0) _).
      * apply qeq_imp_qle. ring.
      * apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia.
    + exact Hinv0.
  - assert (H44 : (1 # 4) * 4 == 1).
    { unfold Qeq. simpl. lia. }
    assert (Hmid : (1 # 4) * d == C + 1).
    { unfold d.
      transitivity (((1 # 4) * 4) * (C + 1)).
      - apply (Qmult_assoc (1 # 4) 4 (C + 1)).
      - rewrite H44. ring. }
    assert (Hdd : d * Qinv d == 1).
    { apply (Qmult_inv_r d Hdnz). }
    apply qeq_imp_qle.
    transitivity ((1 # 4) * (d * Qinv d)).
    + transitivity (((1 # 4) * d) * Qinv d).
      * rewrite Hmid. reflexivity.
      * apply Qeq_sym. apply (Qmult_assoc (1 # 4) d (Qinv d)).
    + rewrite Hdd. ring.
Qed.
(* ============================================================ *)
(* Part C2：r 参数化逐点核心界                                  *)
(* 0 ≤ r < 1、|u| ≤ r、|h| ≤ (1−r)/2 ⟹                          *)
(*   |S_n(u+h) − S_n(u) − h·Qinv(1+u²)|                          *)
(*   ≤ C2(M)·|h|² + |h|·r^{2(Sn)}，M := (1+r)/2                  *)
(* ============================================================ *)
Lemma b3rr_core_r : forall (n : nat) (u h r : Q),
  Qle 0 r -> Qlt r 1 -> Qle (Qabs u) r ->
  Qle (Qabs h) ((1 # 2) * (1 - r)) ->
  Qle (Qabs (arctan_partial n (u + h) - arctan_partial n u - h * Qinv (1 + u * u)))
      (Qplus (Qmult (b3rr_C2 ((1 # 2) * (1 + r))) (Qmult (Qabs h) (Qabs h)))
             (Qmult (Qabs h) (q_pow r (2 * Datatypes.S n)))).
Proof.
  intros n u h r Hr0 Hr1 Hu Hh.
  set (M := (1 # 2) * (1 + r)).
  (* 0 ≤ M < 1 *)
  assert (HM0 : Qle 0 M).
  { unfold M. apply (Qmult_le_0_compat (1 # 2) (1 + r)).
    - unfold Qle. simpl. lia.
    - apply (Qle_trans 0 1 (1 + r)).
      + unfold Qle. simpl. lia.
      + apply (Qle_plus_nonneg_r 1 r). exact Hr0. }
  assert (HM1le : Qle M 1).
  { unfold M.
    apply (Qle_trans _ ((1 # 2) * (Z.of_nat 2 # 1)) _).
    - apply (b3_qmult_le_l (1 + r) (Z.of_nat 2 # 1) (1 # 2)).
      + unfold Qle. simpl. lia.
      + apply (Qle_trans _ (1 + 1) _).
        * apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak. exact Hr1.
        * apply qeq_imp_qle. ring.
    - rewrite b3rr_half2_l. apply Qle_refl. }
  assert (HM1ne : ~ M == 1).
  { intro Hz. unfold M in Hz.
    assert (H2z : (1 + r) == 1 + 1).
    { apply (Qmult_inj_l (1 + r) (1 + 1) (Z.of_nat 2 # 1)).
      - unfold Qeq. simpl. lia.
      - assert (Ht : (Z.of_nat 2 # 1) * ((1 # 2) * (1 + r)) == 1 + r)
          by apply b3rr_twice_half.
        assert (Hz2 : (Z.of_nat 2 # 1) * ((1 # 2) * (1 + r)) == (Z.of_nat 2 # 1) * 1).
        { apply Qmult_comp.
          - apply Qeq_refl.
          - exact Hz. }
        rewrite Ht in Hz2.
        rewrite Hz2. unfold Qeq. simpl. lia. }
    apply (Qlt_irrefl r).
    apply (Qlt_le_trans r 1 r).
    - exact Hr1.
    - (* 1 ≤ r：r == 1（H2z：1+r == 1+1 两侧加 −1） *)
      assert (Hr1q : r == 1).
      { transitivity ((1 + r) + -1).
        - ring.
        - transitivity ((1 + 1) + -1).
          + apply (Qplus_comp (1 + r) (1 + 1) H2z (Qopp 1) (Qopp 1) (Qeq_refl (Qopp 1))).
          + ring. }
      apply qeq_imp_qle. apply Qeq_sym. exact Hr1q. }
  assert (HM1 : Qlt M 1).
  { destruct (Qle_lt_or_eq M 1 HM1le) as [Hlt | Heq].
    - exact Hlt.
    - exfalso. apply HM1ne. exact Heq. }
  (* |u| ≤ r ≤ M、|u+h| ≤ M *)
  assert (HuM : Qle (Qabs u) M).
  { apply (Qle_trans _ r _).
    - exact Hu.
    - apply (Qle_trans _ ((1 # 2) * (1 + r)) _).
      + apply (b3rr_r_le_half r). apply Qlt_le_weak. exact Hr1.
      + unfold M. apply Qle_refl. }
  assert (HuhM : Qle (Qabs (u + h)) M).
  { apply (Qle_trans _ (Qabs u + Qabs h) _).
    - apply Qabs_triangle.
    - apply (Qle_trans _ (r + (1 # 2) * (1 - r)) _).
      + apply Qplus_le_compat. exact Hu. exact Hh.
      + apply qeq_imp_qle. rewrite (b3rr_rc_half r). unfold M. reflexivity. }
  (* 插项分解 *)
  assert (Hdec : arctan_partial n (u + h) - arctan_partial n u - h * Qinv (1 + u * u) ==
        (arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u) +
        h * (b3_dsum n u - Qinv (1 + u * u))).
  { ring. }
  apply (Qle_trans _ (Qplus
      (Qabs (arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u))
      (Qabs (h * (b3_dsum n u - Qinv (1 + u * u))))) _).
  - apply (Qle_trans _ (Qabs
        ((arctan_partial n (u + h) - arctan_partial n u - h * b3_dsum n u) +
         h * (b3_dsum n u - Qinv (1 + u * u)))) _).
    + apply qeq_imp_qle. apply Qabs_wd. exact Hdec.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (Qplus
        (Qmult (b3rr_C2 M) (Qmult (Qabs h) (Qabs h)))
        (Qmult (Qabs h) (Qabs (b3_dsum n u - Qinv (1 + u * u))))) _).
    + apply Qplus_le_compat.
      * assert (Hd : (u + h) - u == h) by ring.
        apply (Qle_trans _ (Qmult (b3rr_C2 M) (Qmult (Qabs ((u + h) - u)) (Qabs ((u + h) - u)))) _).
        -- apply (Qle_trans _ (Qabs (arctan_partial n (u + h) - arctan_partial n u
                                      - (u + h - u) * b3_dsum n u)) _).
           ++ apply qeq_imp_qle. apply Qabs_wd. rewrite Hd. reflexivity.
           ++ apply (b3rr_varM n u (u + h) M HM0 HM1 HuM HuhM).
        -- apply qeq_imp_qle. rewrite Hd. reflexivity.
      * apply qeq_imp_qle.
        rewrite (Qabs_Qmult h (b3_dsum n u - Qinv (1 + u * u))).
        reflexivity.
    + apply (Qle_trans _ (Qplus
        (Qmult (b3rr_C2 M) (Qmult (Qabs h) (Qabs h)))
        (Qmult (Qabs h) (q_pow r (2 * Datatypes.S n)))) _).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (b3_qmult_le_l (Qabs (b3_dsum n u - Qinv (1 + u * u)))
                 (q_pow r (2 * Datatypes.S n)) (Qabs h)).
           ++ apply Qabs_nonneg.
           ++ (* |b3_dsum n u − w| ≤ |u|^{2(Sn)} ≤ r^{2(Sn)} *)
              apply (Qle_trans _ (q_pow (Qabs u) (2 * Datatypes.S n)) _).
              ** apply (b3_dsum_rem_le n u).
              ** apply q_pow_mono.
                 --- apply Qabs_nonneg.
                 --- exact Hu.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* Part C3：r 参数化主定理辅助件（M := (1+r)/2 界、r≤1 证书、  *)
(*   (1−r)/2 ≤ 1）                                               *)
(* ============================================================ *)

(* 0 ≤ r ⟹ 0 ≤ M := (1+r)/2 *)
Lemma b3rr_M0 : forall (r : Q), Qle 0 r -> Qle 0 ((1 # 2) * (1 + r)).
Proof.
  intros r Hr0.
  apply (Qmult_le_0_compat (1 # 2) (1 + r)).
  - unfold Qle. simpl. lia.
  - apply (Qle_trans 0 1 (1 + r)).
    + unfold Qle. simpl. lia.
    + apply (Qle_plus_nonneg_r 1 r). exact Hr0.
Qed.

(* r < 1 ⟹ M := (1+r)/2 < 1 *)
Lemma b3rr_M_lt1 : forall (r : Q), Qlt r 1 -> Qlt ((1 # 2) * (1 + r)) 1.
Proof.
  intros r Hr1.
  set (M := (1 # 2) * (1 + r)).
  assert (HM1le : Qle M 1).
  { unfold M.
    apply (Qle_trans _ ((1 # 2) * (Z.of_nat 2 # 1)) _).
    - apply (b3_qmult_le_l (1 + r) (Z.of_nat 2 # 1) (1 # 2)).
      + unfold Qle. simpl. lia.
      + apply (Qle_trans _ (1 + 1) _).
        * apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak. exact Hr1.
        * apply qeq_imp_qle. ring.
    - rewrite b3rr_half2_l. apply Qle_refl. }
  assert (HM1ne : ~ M == 1).
  { intro Hz. unfold M in Hz.
    assert (H2z : (1 + r) == 1 + 1).
    { apply (Qmult_inj_l (1 + r) (1 + 1) (Z.of_nat 2 # 1)).
      - unfold Qeq. simpl. lia.
      - assert (Ht : (Z.of_nat 2 # 1) * ((1 # 2) * (1 + r)) == 1 + r)
          by apply b3rr_twice_half.
        assert (Hz2 : (Z.of_nat 2 # 1) * ((1 # 2) * (1 + r)) == (Z.of_nat 2 # 1) * 1).
        { apply Qmult_comp.
          - apply Qeq_refl.
          - exact Hz. }
        rewrite Ht in Hz2.
        rewrite Hz2. unfold Qeq. simpl. lia. }
    apply (Qlt_irrefl r).
    apply (Qlt_le_trans r 1 r).
    - exact Hr1.
    - assert (Hr1q : r == 1).
      { transitivity ((1 + r) + -1).
        - ring.
        - transitivity ((1 + 1) + -1).
          + apply (Qplus_comp (1 + r) (1 + 1) H2z (Qopp 1) (Qopp 1) (Qeq_refl (Qopp 1))).
          + ring. }
      apply qeq_imp_qle. apply Qeq_sym. exact Hr1q. }
  destruct (Qle_lt_or_eq M 1 HM1le) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply HM1ne. exact Heq.
Qed.

(* |x_n| ≤ r、r < 1 ⟹ |x_n| ≤ 1（arctan x 域证书） *)
Lemma b3rr_dom_r1 : forall (x : Real) (r : Q),
  (forall n : nat, QleT' (Qabs (projT1 x n)) r) ->
  Qlt r 1 ->
  forall n : nat, QleT' (Qabs (projT1 x n)) 1.
Proof.
  intros x r Hxr Hr1 n.
  apply (b3rr_dom_lt1 x r Hxr).
  apply Qle_to_QleT'.
  apply Qlt_le_weak.
  exact Hr1.
Qed.

(* 0 ≤ r ⟹ (1−r)/2 ≤ 1/2·1 == 1/2 ≤ 1 *)
Lemma b3rr_1mr_half_le1 : forall (r : Q), Qle 0 r -> Qle ((1 # 2) * (1 - r)) 1.
Proof.
  intros r Hr0.
  apply (Qle_trans _ ((1 # 2) * 1) _).
  - apply (b3_qmult_le_l (1 - r) 1 (1 # 2)).
    + unfold Qle. simpl. lia.
    + apply (Qle_trans _ ((1 - r) + r) _).
      * apply (Qle_plus_nonneg_r (1 - r) r). exact Hr0.
      * apply qeq_imp_qle. ring.
  - apply (Qle_trans _ (1 # 2) _).
    + apply qeq_imp_qle. ring.
    + unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* Part D：r 参数化主定理 b3rr_real_arctan_deriv_linear          *)
(* 域 |x| ≤ r（0 ≤ r < 1，逐点 QleT' 前提）；δ := min((1−r)/2,  *)
(*   eps·k)（k := Qinv(4(Cr+1))，Cr := b3rr_C2((1+r)/2)）。       *)
(* 蓝图同构于 sc2_b3_real.v Part 8 real_arctan_deriv_linear 的     *)
(* 点值链（上游只读参考；(1/2)-底换 r，Cb 换 Cr）。              *)
(* ============================================================ *)
Lemma b3rr_real_arctan_deriv_linear :
  forall (r : Q) (Hr0 : Qle 0 r) (Hr1 : Qlt r 1),
  forall (x : Real),
  forall (Hxb : forall n : nat, QleT' (Qabs (projT1 x n)) r),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                 (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                           (b3r_one_sq_real_pos x)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros r Hr0 Hr1 x Hxb eps Heps.
  set (Cr := b3rr_C2 ((1 # 2) * (1 + r))).
  assert (HCr0 : Qle 0 Cr).
  { unfold Cr. apply (b3rr_C2_0 ((1 # 2) * (1 + r))).
    - apply (b3rr_M0 r). exact Hr0.
    - apply (b3rr_M_lt1 r). exact Hr1. }
  set (k := Qinv (4 * (Cr + 1))).
  assert (Hk_pos : Qlt 0 k).
  { unfold k. apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 4 (Cr + 1)).
    - unfold Qlt. simpl. lia.
    - apply (Qlt_le_trans 0 1 (Cr + 1)).
      + unfold Qlt. simpl. lia.
      + apply (Qle_trans 1 (0 + 1) (Cr + 1)).
        * apply qeq_imp_qle. ring.
        * apply Qplus_le_compat. exact HCr0. apply Qle_refl. }
  assert (HCrK : Qle (Cr * k) (1 # 4)).
  { unfold k. exact (b3rr_CK Cr HCr0). }
  assert (Hk0 : Qle 0 k) by (apply Qlt_le_weak; exact Hk_pos).
  set (rk := real_const k).
  assert (Hrk_pos : real_lt real_zero rk).
  { unfold rk. apply real_const_pos_f1. exact Hk_pos. }
  set (delta := real_min (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)).
  exists delta. split.
  - (* 0 < delta *)
    unfold delta, rk.
    apply real_min_pos.
    + apply real_const_pos_f1.
      apply (Qmult_lt_0_compat (1 # 2) (1 - r)).
      * unfold Qlt. simpl. lia.
      * apply (proj1 (Qlt_minus_iff r 1)). exact Hr1.
    + apply real_mult_positive. exact Heps. exact Hrk_pos.
  - intros h Hh Hxh eps' Heps'.
    left.
    destruct Heps as [eps1 [Heps1 [N1 HN1]]].
    destruct Heps' as [eps1' [Heps1' [N1' HN1']]].
    assert (Hh_l : real_lt (real_abs h) (real_const ((1 # 2) * (1 - r))))
      by (unfold delta in Hh; apply (real_min_lt_l h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    assert (Hh_r : real_lt (real_abs h) (real_mult eps rk))
      by (unfold delta in Hh; apply (real_min_lt_r h (real_const ((1 # 2) * (1 - r))) (real_mult eps rk)); exact Hh).
    destruct Hh_l as [e2 [He2 [N2 HN2]]].
    destruct Hh_r as [e3 [He3 [N3 HN3]]].
    destruct (real_inv_proj (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)) as [Ninv HNinv].
    assert (Hh2 : Qlt 0 (Qmult eps1' (Qinv 2))).
    { apply (Qmult_lt_0_compat eps1' (Qinv 2)).
      - apply QltT_to_Qlt. exact Heps1'.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (b3rr_qdecay r (Qmult eps1' (Qinv 2)) Hr0 Hr1 Hh2) as [Ng HNg].
    set (eta := Qmult eps1' (Qinv 2)).
    assert (Heta_pos : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT. exact Hh2. }
    exists eta. split.
    + exact Heta_pos.
    + exists (Nat.max (Nat.max (Nat.max N1 N1') (Nat.max N2 N3)) (Nat.max Ninv Ng)).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (Hn1 : (N1 <= n)%nat) by lia.
      assert (Hn1' : (N1' <= n)%nat) by lia.
      assert (Hn2 : (N2 <= n)%nat) by lia.
      assert (Hn3 : (N3 <= n)%nat) by lia.
      assert (Hninv : (Ninv <= n)%nat) by lia.
      assert (Hng : (Ng <= n)%nat) by lia.
      set (un := projT1 x n). set (hn := projT1 h n).
      set (en := projT1 eps n). set (en' := projT1 eps' n).
      set (yn := un + hn).
      set (Dform := arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)).
      set (wreal := real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)).
      (* 正性：en ≥ 0、en' > eps1' *)
      assert (HN1e : QltT eps1 en).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) en).
        - apply QltT_to_Qlt. exact (HN1 n (NatLe_lift _ _ Hn1)).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en. ring. }
      assert (Hen0 : Qle 0 en).
      { apply Qlt_le_weak. apply (Qlt_trans 0 eps1 en).
        - apply QltT_to_Qlt. exact Heps1.
        - apply QltT_to_Qlt. exact HN1e. }
      assert (HN1'e : QltT eps1' en').
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans eps1' (Qminus (projT1 eps' n) (projT1 real_zero n)) en').
        - apply QltT_to_Qlt. exact (HN1' n (NatLe_lift _ _ Hn1')).
        - apply qeq_imp_qle. cbn [real_zero real_const projT1]. unfold en'. ring. }
      (* 见证→点界：|hn| ≤ (1−r)/2、|hn| ≤ en·k *)
      assert (Hq2 : Qlt e2 (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
      { apply (Qlt_le_trans e2 (Qminus (projT1 (real_const ((1 # 2) * (1 - r))) n) (projT1 (real_abs h) n))
                             (Qminus ((1 # 2) * (1 - r)) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN2 n (NatLe_lift _ _ Hn2)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n). cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_half : Qlt (Qabs hn) ((1 # 2) * (1 - r))).
      { apply (Qlt_le_trans (Qabs hn) (Qminus ((1 # 2) * (1 - r)) e2) ((1 # 2) * (1 - r))).
        - apply (q_lt_minus_shift e2 ((1 # 2) * (1 - r)) (Qabs hn)). exact Hq2.
        - assert (He20 : Qle 0 e2) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He2).
          apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                           (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)
                           ((1 # 2) * (1 - r))).
          + apply (Qle_trans (Qminus ((1 # 2) * (1 - r)) e2)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) 0)
                             (Qplus (Qminus ((1 # 2) * (1 - r)) e2) e2)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus ((1 # 2) * (1 - r)) e2)
                                     (Qminus ((1 # 2) * (1 - r)) e2) 0 e2
                                     (Qle_refl _) He20).
          + apply qeq_imp_qle. ring. }
      assert (Hhn_half_le : Qle (Qabs hn) ((1 # 2) * (1 - r))) by (apply Qlt_le_weak; exact Hhn_half).
      assert (Hhn1 : Qle (Qabs hn) 1).
      { apply (Qle_trans _ ((1 # 2) * (1 - r)) _).
        - exact Hhn_half_le.
        - apply (b3rr_1mr_half_le1 r). exact Hr0. }
      assert (Hq3 : Qlt e3 (Qminus (Qmult en k) (Qabs hn))).
      { apply (Qlt_le_trans e3 (Qminus (projT1 (real_mult eps rk) n) (projT1 (real_abs h) n))
                             (Qminus (Qmult en k) (Qabs hn))).
        - apply QltT_to_Qlt. apply (HN3 n (NatLe_lift _ _ Hn3)).
        - apply qeq_imp_qle.
          rewrite (real_abs_proj h n).
          unfold rk, en.
          setoid_rewrite (real_mult_proj eps (real_const k) n).
          cbn [real_zero real_const projT1]. reflexivity. }
      assert (Hhn_k : Qlt (Qabs hn) (Qmult en k)).
      { apply (Qlt_le_trans (Qabs hn) (Qminus (Qmult en k) e3) (Qmult en k)).
        - apply (q_lt_minus_shift e3 (Qmult en k) (Qabs hn)). exact Hq3.
        - assert (He30 : Qle 0 e3) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact He3).
          apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) e3)
                           (Qmult en k)).
          + apply (Qle_trans (Qminus (Qmult en k) e3) (Qplus (Qminus (Qmult en k) e3) 0)
                             (Qplus (Qminus (Qmult en k) e3) e3)).
            * apply qeq_imp_qle. ring.
            * apply (Qplus_le_compat (Qminus (Qmult en k) e3) (Qminus (Qmult en k) e3) 0 e3
                     (Qle_refl _) He30).
          + apply qeq_imp_qle. ring. }
      assert (Hhn_kle : Qle (Qabs hn) (Qmult en k)) by (apply Qlt_le_weak; exact Hhn_k).
      (* 域：|un| ≤ r *)
      assert (Hun_r : Qle (Qabs un) r).
      { apply (QleT'_to_Qle (Qabs un) r). apply Hxb. }
      assert (Hhvn0 : Qle 0 (Qabs hn)) by apply Qabs_nonneg.
      assert (Henhn0 : Qle 0 (Qmult en (Qabs hn))).
      { apply (Qmult_le_0_compat en (Qabs hn)). exact Hen0. exact Hhvn0. }
      (* 投影恒等（A 侧） *)
      assert (Hrepl : projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n ==
                  Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un))).
      { unfold yn, un, hn, wreal.
        rewrite (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))))) n).
        rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))))) n).
        rewrite (real_opp_proj (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)))) n).
        rewrite (real_plus_proj (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x))) n).
        rewrite (real_mult_proj h (real_inv_pos (real_plus real_one (real_mult x x))
                                                         (b3r_one_sq_real_pos x)) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        rewrite (arctan_real_proj x (b3rr_dom_r1 x r Hxb Hr1) n).
        rewrite (real_plus_proj x h n).
        rewrite (HNinv n Hninv).
        rewrite (real_plus_proj real_one (real_mult x x) n).
        rewrite (real_mult_proj x x n).
        rewrite (b3r_one_proj n).
        apply Qabs_wd. ring. }
      (* B 侧投影 *)
      assert (HB : projT1 (real_plus (real_mult eps (real_abs h)) eps') n == en * Qabs hn + en').
      { unfold en, en', hn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        cbn [real_zero real_const projT1]. ring. }
      (* 点主界 1：Cr·|hn|² ≤ en·|hn|·(1/4) *)
      assert (Hcbn : Qle (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
                         (Qmult (Qmult en (Qabs hn)) (1 # 4))).
      { apply (Qle_trans _ (Qmult Cr (Qmult (Qmult en k) (Qabs hn))) _).
        - (* |hn|·|hn| ≤ (en·k)·|hn|（右乘 |hn| ≥ 0），再左乘 Cr ≥ 0 *)
          apply (b3_qmult_le_l (Qmult (Qabs hn) (Qabs hn))
                               (Qmult (Qmult en k) (Qabs hn)) Cr).
          + exact HCr0.
          + apply (Qmult_le_compat_r (Qabs hn) (Qmult en k) (Qabs hn)).
            * exact Hhn_kle.
            * exact Hhvn0.
        - (* Cr·((en·k)·|hn|) == en·|hn|·(Cr·k) ≤ en·|hn|·(1/4) *)
          apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) (Qmult Cr k)) _).
          + apply qeq_imp_qle. ring.
          + apply (b3_qmult_le_l (Qmult Cr k) (1 # 4) (Qmult en (Qabs hn))).
            * exact Henhn0.
            * exact HCrK. }
      (* 点主界 2：r^{2(Sn)} ≤ eta（n ≥ Ng ⟹ 2(Sn) ≥ Ng） *)
      assert (Hdec2 : Qle (q_pow r (2 * Datatypes.S n)) eta).
      { apply (HNg ((2 * Datatypes.S n)%nat)). lia. }
      assert (Hpow14 : Qle (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))
                           (q_pow r (2 * Datatypes.S n))).
      { apply (Qle_trans _ (Qmult 1 (q_pow r (2 * Datatypes.S n))) _).
        - apply (Qmult_le_compat_r (Qabs hn) 1 (q_pow r (2 * Datatypes.S n))).
          + exact Hhn1.
          + apply q_pow_nonneg. exact Hr0.
        - apply qeq_imp_qle. ring. }
      (* 主点界：|D_n| ≤ en·|hn| + eta *)
      assert (Hm1 : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
      { unfold yn. apply (b3rr_core_r n un hn r Hr0 Hr1 Hun_r Hhn_half_le). }
      assert (Hm2 : Qle
        (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))).
      { apply Qplus_le_compat. exact Hcbn. apply Qle_refl. }
      assert (Hm3 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n))))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow r (2 * Datatypes.S n)))).
      { apply Qplus_le_compat. apply Qle_refl. exact Hpow14. }
      assert (Hm4 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (q_pow r (2 * Datatypes.S n)))
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)).
      { apply Qplus_le_compat. apply Qle_refl. exact Hdec2. }
      assert (Hm5 : Qle (Qmult (Qmult en (Qabs hn)) (1 # 4)) (Qmult en (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qmult en (Qabs hn)) 1) _).
        - apply (b3_qmult_le_l (1 # 4) 1 (Qmult en (Qabs hn))).
          + exact Henhn0.
          + unfold Qle. simpl. lia.
        - apply qeq_imp_qle. ring. }
      assert (Hm6 : Qle
        (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta)
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply Qplus_le_compat. exact Hm5. apply Qle_refl. }
      assert (Hmain : Qle
        (Qabs (arctan_partial n yn - arctan_partial n un - hn * Qinv (1 + un * un)))
        (Qplus (Qmult en (Qabs hn)) eta)).
      { apply (Qle_trans _ (Qplus (Qmult Cr (Qmult (Qabs hn) (Qabs hn)))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
        - exact Hm1.
        - apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
               (Qmult (Qabs hn) (q_pow r (2 * Datatypes.S n)))) _).
          + exact Hm2.
          + apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4))
                 (q_pow r (2 * Datatypes.S n))) _).
            * exact Hm3.
            * apply (Qle_trans _ (Qplus (Qmult (Qmult en (Qabs hn)) (1 # 4)) eta) _).
              -- exact Hm4.
              -- exact Hm6. }
      (* Hfin：eta < (en·|hn| + en') − |D_n| *)
      assert (Hfin : Qlt eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en')
                  (Qplus (Qmult en (Qabs hn)) eta))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
        - (* eta < (en|hn|+en') − (en|hn|+eta) == en' − 2eta，由 en' > eps1' == 2eta *)
          apply (proj2 (Qlt_minus_iff eta
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)))).
          assert (Heq : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en')
                               (Qplus (Qmult en (Qabs hn)) eta)) eta ==
                        Qminus en' (Qmult eta (1 + 1))) by ring.
          rewrite Heq.
          apply (proj1 (Qlt_minus_iff (Qmult eta (1 + 1)) en')).
          assert (HX : Qmult eta (1 + 1) == eps1') by (unfold eta; field).
          rewrite HX.
          apply QltT_to_Qlt. exact HN1'e.
        - apply (proj2 (Qle_minus_iff
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta))
              (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform)))).
          assert (Heq2 : Qminus (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
                                (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qplus (Qmult en (Qabs hn)) eta)) ==
                          Qminus (Qplus (Qmult en (Qabs hn)) eta) (Qabs Dform)) by ring.
          rewrite Heq2.
          apply (proj1 (Qle_minus_iff (Qabs Dform) (Qplus (Qmult en (Qabs hn)) eta))).
          exact Hmain. }
      (* 投影桥（RHS − LHS）==（B − |D|） *)
      assert (Hrepl2 : Qeq
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))).
      { apply (Qminus_comp (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                           (Qplus (Qmult en (Qabs hn)) en') HB
                           (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                           (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                                       (real_mult h wreal))))) n)
                           (Qabs Dform) Hrepl). }
      apply Qlt_to_QltT.
      assert (Hqfinal : Qlt eta
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))).
      { apply (Qlt_le_trans eta
          (Qminus (Qplus (Qmult en (Qabs hn)) en') (Qabs Dform))
          (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                  (projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                  (real_opp (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r Hxb Hr1))
                              (real_mult h wreal))))) n))).
        - exact Hfin.
        - apply qeq_imp_qle. apply Qeq_sym. exact Hrepl2. }
      exact Hqfinal.

Qed.

(* ============================================================ *)
(* B4 链式 infra（p2 完整 + p3 前件）+ B5-B E/Hsc 桥 *)
(* b4_chain_lipschitz 未纳入（排除项）；零公理面。                    *)
(* ============================================================ *)


(* ================= 实层 Q-eq 自动化（无 inv/abs 的环恒等） =================
   real_plus/mult/opp/const 逐点：projT1 引理穿透任意实参数（变量或
   不透明实原子），real_zero/real_one 直接 cbn，simpl 后 Q ring/field。
   不 destruct 上下文 Real 变量（避免误伤 let/alias）。勿用于含
   inv/abs 的目标（inv 逐点不成立；abs 的 projT1 保持为原子）。 *)
Ltac b4_qring :=
  apply real_eq_of_zero_diff; intro n;
  repeat (first [ rewrite real_plus_proj | rewrite real_opp_proj
                | rewrite real_mult_proj | rewrite real_const_proj ]);
  cbn [projT1 real_zero real_one];
  simpl; try ring; try field.

(* ================= 烟测：tactic 有效性与 Q field ================= *)
Lemma p2_smoke_qfield : forall a b c : Q, a * (b + c) == a * b + a * c.
Proof. intros. field. Qed.

Lemma p2_smoke1 : forall (x y z : Real),
  real_eq (real_plus (real_mult x y) (real_mult x z))
          (real_mult x (real_plus y z)).
Proof. intros. b4_qring. Qed.

Lemma p2_smoke2 : forall (c d : Q),
  real_eq (real_plus (real_const c) (real_const d)) (real_const (c + d)).
Proof. intros. b4_qring. Qed.

(* ================= lift 序列代数 ================= *)
(* real_one 逐点 == 1（烟测） *)
Lemma p2_one_proj : forall n : nat, projT1 real_one n == 1.
Proof.
  intro n.
  (* real_one（L5353）定义为常量 1 序列：cbn 直接归约 *)
  cbn [projT1 real_one]. reflexivity.
Qed.

(* real_const 层 Qeq 提升：c == d ⟹ real_const c == real_const d *)
Lemma b4_const_eq : forall (c d : Q), c == d ->
  real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd eps Heps.
  exists O. intros n Hn.
  cbn [projT1 real_const].
  assert (H0 : c - d == 0) by (rewrite Hcd; ring).
  assert (Hz : Qabs (c - d) == 0).
  { apply (Qeq_trans _ (Qabs 0) _).
    - apply (Qabs_wd (c - d) 0 H0).
    - apply Qabs_pos. apply Qle_refl. }
  unfold QltT, Qlt_bool.
  assert (Hcmp : Qcompare (Qabs (c - d)) eps = Qcompare 0 eps).
  { exact (Qcompare_comp (Qabs (c - d)) 0 Hz eps eps (Qeq_refl eps)). }
  rewrite Hcmp.
  exact Heps.
Qed.

(* real_plus (real_const c) real_one == real_const (c + 1)（逐点） *)
Lemma b4_const_plus_one : forall (c : Q),
  real_eq (real_plus (real_const c) real_one) (real_const (c + 1)).
Proof.
  intro c.
  apply real_eq_of_zero_diff. intro n.
  rewrite !real_plus_proj, !real_const_proj.
  rewrite (p2_one_proj n).
  ring.
Qed.

(* lift 后继： (S k)#1 == k#1 + 1 *)
Lemma b4_lift_succ : forall (k : nat),
  real_eq (real_const (Z.of_nat (Datatypes.S k) # 1))
          (real_plus (real_const (Z.of_nat k # 1)) real_one).
Proof.
  intro k.
  apply (real_eq_trans _ (real_const ((Z.of_nat k # 1) + 1)) _).
  - apply b4_const_eq.
    unfold Qeq. simpl. lia.
  - apply (real_eq_sym _ _ (b4_const_plus_one (Z.of_nat k # 1))).
Qed.

(* lift 正性：n ≥ 1 ⟹ 0 < n#1 *)
Lemma b4_lift_pos : forall (n : nat), (1 <= n)%nat ->
  real_lt real_zero (real_const (Z.of_nat n # 1)).
Proof.
  intros n Hn.
  apply real_const_pos.
  apply Qlt_to_QltT.
  unfold Qlt. simpl.
  lia.
Qed.

(* ================= 常数列表和：Σ_{l}(c) == length(l)#1 · c ================= *)
Lemma b4_sum_const : forall (X : Type) (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l)
          (real_mult (real_const (Z.of_nat (length l) # 1)) c).
Proof.
  intros X c l.
  induction l as [| w rest IH]; simpl.
  - (* 空和 == 0 == 0#1·c *)
    destruct c as [uc Hc].
    apply real_eq_of_zero_diff. intro n.
    simpl.
    change (Z.of_nat 0) with 0%Z.
    ring.
  - (* c + Σrest == (length rest + 1)#1 · c *)
    apply (real_eq_trans _ (real_plus c (real_mult (real_const (Z.of_nat (length rest) # 1)) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c
               (real_list_sum X (fun _ : X => c) rest) c
               (real_mult (real_const (Z.of_nat (length rest) # 1)) c)).
      * apply real_eq_refl.
      * exact IH.
    + (* c + lift·c == (lift + 1)·c（ring）再 == (S(length rest))#1·c（lift_succ） *)
      apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat (length rest) # 1)) real_one) c) _).
      * b4_qring.
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus (real_const (Z.of_nat (length rest) # 1)) real_one) c
                 (real_const (Z.of_nat (Datatypes.S (length rest)) # 1)) c).
        -- apply real_eq_sym. exact (b4_lift_succ (length rest)).
        -- apply real_eq_refl.
Qed.

(* ================= 三角不等式（list 层，逐 eps 预算） =================
   |Σg| ≤ Σ|g| + Σe（e w > 0 逐点，real_abs_triangle_le_eps 步进） *)
Lemma b4_tri_sum : forall (X : Type) (g : X -> Real) (e : X -> Real) (l : list X),
  (forall w : X, real_lt real_zero (e w)) ->
  real_le (real_abs (real_list_sum X g l))
          (real_plus (real_list_sum X (fun w => real_abs (g w)) l)
                     (real_list_sum X e l)).
Proof.
  intros X g e l He.
  induction l as [| w rest IH]; simpl.
  - (* |0| ≤ 0 + 0 *)
    apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero
                                   (real_plus real_zero real_zero)).
    + apply real_abs_zero_req.
    + apply (RealSetoid.real_eq_le real_zero (real_plus real_zero real_zero)).
      apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - (* |h + T| ≤ (|h| + Σ|g|rest) + (e w + Σe rest) *)
    assert (Htri : real_le (real_abs (real_plus (g w) (real_list_sum X g rest)))
                           (real_plus (real_plus (real_abs (g w))
                                                 (real_abs (real_list_sum X g rest)))
                                      (e w))).
    { apply (real_abs_triangle_le_eps (g w) (real_list_sum X g rest) (e w)).
      exact (He w). }
    (* IH 加法兼容：(|h| + |T|) ≤ (|h| + (Σ|g|rest + Σe rest)) *)
    assert (Hih : real_le (real_plus (real_abs (g w)) (real_abs (real_list_sum X g rest)))
                          (real_plus (real_abs (g w))
                                     (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                                (real_list_sum X e rest)))).
    { apply (real_le_plus_compat (real_abs (g w)) (real_abs (g w))
                                 (real_abs (real_list_sum X g rest))
                                 (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                            (real_list_sum X e rest))).
      - apply real_le_refl.
      - exact IH. }
    assert (Hih2 : real_le (real_plus (real_plus (real_abs (g w))
                                                 (real_abs (real_list_sum X g rest)))
                                      (e w))
                           (real_plus (real_plus (real_abs (g w))
                                                (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                                           (real_list_sum X e rest)))
                                      (e w))).
    { apply (real_le_plus_compat
               (real_plus (real_abs (g w)) (real_abs (real_list_sum X g rest)))
               (real_plus (real_abs (g w))
                          (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                     (real_list_sum X e rest)))
               (e w) (e w)).
      - exact Hih.
      - apply real_le_refl. }
    apply (real_le_trans
             (real_abs (real_plus (g w) (real_list_sum X g rest)))
             (real_plus (real_plus (real_abs (g w))
                                   (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                              (real_list_sum X e rest)))
                        (e w))
             (real_plus (real_plus (real_abs (g w))
                                   (real_list_sum X (fun w0 => real_abs (g w0)) rest))
                        (real_plus (e w) (real_list_sum X e rest)))).
    + (* |g w + T| ≤ ((|g w| + |T|) + e w) ≤ ((|g w| + (Σ|g|+Σe)) + e w) *)
      apply (real_le_trans
               (real_abs (real_plus (g w) (real_list_sum X g rest)))
               (real_plus (real_plus (real_abs (g w)) (real_abs (real_list_sum X g rest))) (e w))
               (real_plus (real_plus (real_abs (g w))
                                     (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                                (real_list_sum X e rest)))
                          (e w))).
      * exact Htri.
      * exact Hih2.
    + (* middle == goal RHS（ring 换形） *)
      apply (RealSetoid.real_le_id_r
               (real_plus (real_plus (real_abs (g w))
                                     (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                                (real_list_sum X e rest)))
                          (e w))
               (real_plus (real_plus (real_abs (g w))
                                     (real_plus (real_list_sum X (fun w0 => real_abs (g w0)) rest)
                                                (real_list_sum X e rest)))
                          (e w))
               (real_plus (real_plus (real_abs (g w))
                                     (real_list_sum X (fun w0 => real_abs (g w0)) rest))
                          (real_plus (e w) (real_list_sum X e rest)))).
      * b4_qring.
      * apply real_le_refl.
Qed.

(* ================= 端点差序：a < b ⟹ 0 < b − a ================= *)
Lemma b4_pos_diff : forall a b : Real, real_lt a b ->
  real_lt real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  destruct Hab as [sep [Hsep [N HN]]].
  unfold real_lt.
  exists sep.
  split.
  - exact Hsep.
  - exists N.
    intros n Hn.
    apply Qlt_to_QltT.
    setoid_rewrite (real_plus_proj b (real_opp a) n).
    setoid_rewrite (real_opp_proj a n).
    cbn [projT1 real_zero].
    assert (Hq : projT1 b n + - projT1 a n - 0 == projT1 b n - projT1 a n) by ring.
    setoid_rewrite Hq.
    apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* ================= 反向绝对差（对称） =================
   |x − y| == |y − x| *)
Lemma b4_abs_minus_sym : forall x y : Real,
  real_eq (real_abs (real_plus x (real_opp y)))
          (real_abs (real_plus y (real_opp x))).
Proof.
  intros x y.
  apply real_eq_of_zero_diff. intro n.
  repeat setoid_rewrite real_abs_proj.
  rewrite !real_plus_proj, !real_opp_proj.
  assert (H : projT1 y n + - projT1 x n == - (projT1 x n + - projT1 y n)) by ring.
  rewrite H.
  rewrite (Qabs_opp (projT1 x n + - projT1 y n)).
  ring.
Qed.

(* ================= 可延展性下的点值识别 =================
   f 保持 real_eq ⟹ f x − f y == 0 当 x == y（用于端点衔接） *)
Lemma b4_f_eq_zero : forall (f : Real -> Real) (x y : Real),
  (forall u v : Real, real_eq u v -> real_eq (f u) (f v)) ->
  real_eq x y ->
  real_eq (real_plus (f x) (real_opp (f y))) real_zero.
Proof.
  intros f x y Hext Hxy.
  apply (real_eq_trans _ (real_plus (f y) (real_opp (f y))) _).
  - apply (RealSetoid.real_eq_plus_compat (f x) (real_opp (f y)) (f y) (real_opp (f y))).
    + exact (Hext x y Hxy).
    + apply real_eq_refl.
  - apply real_plus_opp.
Qed.

(* f 可延展 + x==y ⟹ |f x − f y| == 0 *)
Lemma b4_f_abs_eq_zero : forall (f : Real -> Real) (x y : Real),
  (forall u v : Real, real_eq u v -> real_eq (f u) (f v)) ->
  real_eq x y ->
  real_eq (real_abs (real_plus (f x) (real_opp (f y)))) real_zero.
Proof.
  intros f x y Hext Hxy.
  apply (real_eq_trans _ (real_abs real_zero) _).
  - apply real_abs_eq_compat. exact (b4_f_eq_zero f x y Hext Hxy).
  - apply real_abs_zero_req.
Qed.

(* ================= 均匀模假设下的单步"点值≈0"桥 =================
   （Tier1 末尾：|f b − f a| == |f g_N − f a| 由 f b == f g_N） *)
(* ================= eps 预算：lift·(c·inv(lift)) == c ================= *)
Lemma b4_lift_inv_cancel : forall (N : nat) (HN : real_lt real_zero (real_const (Z.of_nat N # 1)))
  (c : Real),
  real_eq (real_mult (real_const (Z.of_nat N # 1))
                     (real_mult c (real_inv_pos (real_const (Z.of_nat N # 1)) HN)))
          c.
Proof.
  intros N HN c.
  apply (real_eq_trans _ (real_mult c (real_mult (real_const (Z.of_nat N # 1))
                                                (real_inv_pos (real_const (Z.of_nat N # 1)) HN))) _).
  - b4_qring.
  - apply (real_eq_trans _ (real_mult c real_one) _).
    + apply (RealSetoid.real_eq_mult_compat c
               (real_mult (real_const (Z.of_nat N # 1))
                          (real_inv_pos (real_const (Z.of_nat N # 1)) HN))
               c real_one).
      * apply real_eq_refl.
      * apply (real_inv_pos_correct (real_const (Z.of_nat N # 1)) HN).
    + apply real_mult_one.
Qed.

(* 逐点 eps > 0：0 < (1/4)·eps（eps>0） *)
Lemma b4_quarter_pos : forall (eps : Real), real_lt real_zero eps ->
  real_lt real_zero (real_mult (real_const (1 / 4)) eps).
Proof.
  intros eps Heps.
  apply real_mult_positive.
  - apply real_const_pos.
    apply Qlt_to_QltT.
    unfold Qlt. simpl. lia.
  - exact Heps.
Qed.

(* ================= nat 递归大和（链式论证用，避开 seq/app 组合） =================
   b4_nsum d N := Σ_{k<N} d k *)
Fixpoint b4_nsum (d : nat -> Real) (N : nat) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S m => real_plus (b4_nsum d m) (d m)
  end.

(* Σ 常数 == N#1 · c *)
Lemma b4_nsum_const : forall (c : Real) (N : nat),
  real_eq (b4_nsum (fun _ : nat => c) N)
          (real_mult (real_const (Z.of_nat N # 1)) c).
Proof.
  intros c N.
  induction N as [| N IH]; simpl.
  - (* 0 == 0#1·c *)
    destruct c as [uc Hc].
    apply real_eq_of_zero_diff. intro n.
    simpl.
    change (Z.of_nat 0) with 0%Z.
    ring.
  - (* Σ_N c + c == (N+1)#1·c *)
    apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat N # 1)) c) c) _).
    + apply (RealSetoid.real_eq_plus_compat (b4_nsum (fun _ : nat => c) N) c
               (real_mult (real_const (Z.of_nat N # 1)) c) c).
      * exact IH.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat N # 1)) real_one) c) _).
      * b4_qring.
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus (real_const (Z.of_nat N # 1)) real_one) c
                 (real_const (Z.of_nat (Datatypes.S N) # 1)) c).
        -- apply real_eq_sym. exact (b4_lift_succ N).
        -- apply real_eq_refl.
Qed.

(* Σ(逐点 ≤) ≤：b4_nsum 版 *)
Lemma b4_nsum_le : forall (d e : nat -> Real) (N : nat),
  (forall k : nat, (k < N)%nat -> real_le (d k) (e k)) ->
  real_le (b4_nsum d N) (b4_nsum e N).
Proof.
  intros d e N Hle.
  induction N as [| N IH]; simpl.
  - apply real_le_refl.
  - apply (real_le_plus_compat (b4_nsum d N) (b4_nsum e N) (d N) (e N)).
    + apply IH.
      intros k Hk. apply Hle. lia.
    + apply Hle. lia.
Qed.

(* |Σg| ≤ Σ|g| + Σe（逐 eps 预算，nat 版；e k > 0） *)
Lemma b4_nsum_tri : forall (g e : nat -> Real) (N : nat),
  (forall k : nat, (k < N)%nat -> real_lt real_zero (e k)) ->
  real_le (real_abs (b4_nsum g N))
          (real_plus (b4_nsum (fun k => real_abs (g k)) N) (b4_nsum e N)).
Proof.
  intros g e N He.
  induction N as [| N IH]; simpl.
  - (* |0| ≤ 0 + 0 *)
    apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero
                                   (real_plus real_zero real_zero)).
    + apply real_abs_zero_req.
    + apply (RealSetoid.real_eq_le real_zero (real_plus real_zero real_zero)).
      apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - (* |T + g N| ≤ ((Σ|g|N + ΣeN) + |g N|) + e N，再 ring 到目标 *)
    assert (Htri : real_le (real_abs (real_plus (b4_nsum g N) (g N)))
                           (real_plus (real_plus (real_abs (b4_nsum g N))
                                                 (real_abs (g N)))
                                      (e N))).
    { apply (real_abs_triangle_le_eps (b4_nsum g N) (g N) (e N)).
      apply He. lia. }
    assert (Hih : real_le (real_plus (real_abs (b4_nsum g N)) (real_abs (g N)))
                          (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                                (b4_nsum e N))
                                     (real_abs (g N)))).
    { apply (real_le_plus_compat (real_abs (b4_nsum g N))
                                 (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                            (b4_nsum e N))
                                 (real_abs (g N)) (real_abs (g N))).
      - apply IH.
        intros k Hk. apply He. lia.
      - apply real_le_refl. }
    (* 目标（simpl 后）：|T+gN| ≤ (Σ|g|N + |gN|) + (ΣeN + eN) *)
    apply (real_le_trans
             (real_abs (real_plus (b4_nsum g N) (g N)))
             (real_plus (real_plus (real_abs (b4_nsum g N)) (real_abs (g N))) (e N))
             (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                   (real_abs (g N)))
                        (real_plus (b4_nsum e N) (e N)))).
    + exact Htri.
    + (* ((|T|+|gN|)+eN) ≤ 目标：先经 ((Σ|g|+Σe)+|gN|)+eN *)
      apply (real_le_trans
               (real_plus (real_plus (real_abs (b4_nsum g N)) (real_abs (g N))) (e N))
               (real_plus (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                                (b4_nsum e N))
                                     (real_abs (g N)))
                          (e N))
               (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                     (real_abs (g N)))
                          (real_plus (b4_nsum e N) (e N)))).
      * apply (real_le_plus_compat
                 (real_plus (real_abs (b4_nsum g N)) (real_abs (g N)))
                 (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                       (b4_nsum e N))
                            (real_abs (g N)))
                 (e N) (e N)).
        -- exact Hih.
        -- apply real_le_refl.
      * apply (RealSetoid.real_le_id_r
                 (real_plus (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                                  (b4_nsum e N))
                                       (real_abs (g N)))
                            (e N))
                 (real_plus (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                                  (b4_nsum e N))
                                       (real_abs (g N)))
                            (e N))
                 (real_plus (real_plus (b4_nsum (fun k => real_abs (g k)) N)
                                       (real_abs (g N)))
                            (real_plus (b4_nsum e N) (e N)))).
        -- b4_qring.
        -- apply real_le_refl.
Qed.

(* 望远镜：Σ_{k<N} (f(g(S k)) − f(g k)) == f(g N) − f(g 0) *)
Lemma b4_nsum_telescope : forall (f : Real -> Real) (g : nat -> Real) (N : nat),
  real_eq (b4_nsum (fun k => real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))) N)
          (real_plus (f (g N)) (real_opp (f (g 0%nat)))).
Proof.
  intros f g N.
  induction N as [| N IH]; simpl.
  - (* 0 == f(g 0) − f(g 0) *)
    apply (real_eq_sym _ _ (real_plus_opp (f (g 0%nat)))).
  - (* Σ_N + (f(g(S N)) − f(g N)) == f(g(S N)) − f(g 0) *)
    apply (real_eq_trans _ (real_plus (real_plus (f (g N)) (real_opp (f (g 0%nat))))
                                      (real_plus (f (g (Datatypes.S N))) (real_opp (f (g N))))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (b4_nsum (fun k : nat => real_plus (f (g (Datatypes.S k))) (real_opp (f (g k)))) N)
               (real_plus (f (g (Datatypes.S N))) (real_opp (f (g N))))
               (real_plus (f (g N)) (real_opp (f (g 0%nat))))
               (real_plus (f (g (Datatypes.S N))) (real_opp (f (g N))))).
      * exact IH.
      * apply real_eq_refl.
    + b4_qring.
Qed.

(* ================= 网格 ================= *)
Fixpoint b4_grid (a η : Real) (k : nat) : Real :=
  match k with
  | O => a
  | Datatypes.S m => real_plus (b4_grid a η m) η
  end.

(* 右分配： (A+B)·x == A·x + B·x *)
Lemma b4_mult_plus_r : forall (A B x : Real),
  real_eq (real_mult (real_plus A B) x)
          (real_plus (real_mult A x) (real_mult B x)).
Proof.
  intros A B x.
  b4_qring.
Qed.

(* (0#1)·x == 0 *)
Lemma b4_lift0_mult_zero : forall (x : Real),
  real_eq (real_mult (real_const (Z.of_nat 0 # 1)) x) real_zero.
Proof.
  intro x.
  apply real_eq_of_zero_diff. intro n.
  rewrite real_mult_proj.
  cbn [projT1 real_const real_zero].
  change (Z.of_nat 0) with 0%Z.
  ring.
Qed.

(* 网格点展开：b4_grid a η k == a + k#1·η *)
Lemma b4_grid_sum : forall (a η : Real) (k : nat),
  real_eq (b4_grid a η k)
          (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η)).
Proof.
  intros a η k.
  induction k as [| k IH]; simpl.
  - (* a == a + 0·η *)
    apply (real_eq_trans _ (real_plus a real_zero) _).
    + apply (real_eq_sym _ _ (real_plus_zero a)).
    + apply (RealSetoid.real_eq_plus_compat a real_zero a
               (real_mult (real_const (Z.of_nat 0 # 1)) η)).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (b4_lift0_mult_zero η).
  - (* (a + k#1·η) + η == a + (S k)#1·η *)
    apply (real_eq_trans _ (real_plus (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η)) η) _).
    + apply (RealSetoid.real_eq_plus_compat (b4_grid a η k) η
               (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η)) η).
      * exact IH.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_plus a (real_mult (real_plus (real_const (Z.of_nat k # 1)) real_one) η)) _).
      * apply (real_eq_trans _ (real_plus a (real_plus (real_mult (real_const (Z.of_nat k # 1)) η) η)) _).
        -- apply real_eq_sym. apply (real_plus_assoc a (real_mult (real_const (Z.of_nat k # 1)) η) η).
        -- apply (RealSetoid.real_eq_plus_compat a
                   (real_plus (real_mult (real_const (Z.of_nat k # 1)) η) η)
                   a
                   (real_mult (real_plus (real_const (Z.of_nat k # 1)) real_one) η)).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat k # 1)) η)
                                                (real_mult real_one η)) _).
              ** apply (RealSetoid.real_eq_plus_compat
                         (real_mult (real_const (Z.of_nat k # 1)) η)
                         η
                         (real_mult (real_const (Z.of_nat k # 1)) η)
                         (real_mult real_one η)).
                 --- apply real_eq_refl.
                 --- apply real_eq_sym.
                     apply (real_eq_trans _ (real_mult η real_one) _).
                     ++++ apply real_mult_comm.
                     ++++ apply real_mult_one.
              ** apply real_eq_sym. exact (b4_mult_plus_r (real_const (Z.of_nat k # 1)) real_one η).
      * apply (RealSetoid.real_eq_plus_compat a
                 (real_mult (real_plus (real_const (Z.of_nat k # 1)) real_one) η)
                 a
                 (real_mult (real_const (Z.of_nat (Datatypes.S k) # 1)) η)).
        -- apply real_eq_refl.
        -- apply (RealSetoid.real_eq_mult_compat
                   (real_plus (real_const (Z.of_nat k # 1)) real_one) η
                   (real_const (Z.of_nat (Datatypes.S k) # 1)) η).
           ++ apply real_eq_sym. exact (b4_lift_succ k).
           ++ apply real_eq_refl.
Qed.

(* ================= lift 层序（k ≤ N ⟹ k#1 ≤ N#1；0 ≤ k#1） ================= *)
Lemma b4_lift_le : forall (k N : nat), (k <= N)%nat ->
  real_le (real_const (Z.of_nat k # 1)) (real_const (Z.of_nat N # 1)).
Proof.
  intros k N Hkn.
  destruct (Nat.compare k N) eqn:E.
  - (* Eq：k == N *)
    apply (proj1 (Nat.compare_eq_iff k N)) in E.
    subst N.
    apply real_le_refl.
  - (* Lt：k < N *)
    apply (RealSetoid.real_lt_le_iff_req
             (real_const (Z.of_nat k # 1)) (real_const (Z.of_nat N # 1))).
    left.
    apply real_const_lt.
    assert (Hklt : (k < N)%nat) by (apply (proj1 (Nat.compare_lt_iff k N)); exact E).
    unfold Qlt. simpl.
    lia.
  - (* Gt：k > N 与 k ≤ N 矛盾 *)
    exfalso.
    apply (proj1 (Nat.compare_gt_iff k N)) in E.
    lia.
Qed.

Lemma b4_lift_nonneg : forall (k : nat),
  real_le real_zero (real_const (Z.of_nat k # 1)).
Proof.
  intro k.
  destruct k as [| k'].
  - apply (RealSetoid.real_eq_le real_zero (real_const (Z.of_nat 0 # 1))).
    b4_qring.
  - apply (RealSetoid.real_lt_le_iff_req real_zero (real_const (Z.of_nat (Datatypes.S k') # 1))).
    left. apply b4_lift_pos. lia.
Qed.

(* ================= 网格点区间含于 [a,b] ================= *)
Lemma b4_grid_ge_a : forall (a η : Real) (k : nat),
  real_le real_zero η ->
  real_le a (b4_grid a η k).
Proof.
  intros a η k Hη0.
  apply (RealSetoid.real_le_id_r a (real_plus a
            (real_mult (real_const (Z.of_nat k # 1)) η))
            (b4_grid a η k)).
  - apply real_eq_sym. exact (b4_grid_sum a η k).
  - apply (RealSetoid.real_le_id_l a (real_plus a real_zero)
            (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η))).
    + apply (real_eq_sym _ _ (real_plus_zero a)).
    + apply (real_le_plus_compat a a real_zero
              (real_mult (real_const (Z.of_nat k # 1)) η)).
      * apply real_le_refl.
      * apply (real_le_trans real_zero (real_mult real_zero η)
                             (real_mult (real_const (Z.of_nat k # 1)) η)).
        -- apply (RealSetoid.real_eq_le real_zero (real_mult real_zero η)).
           apply real_eq_sym.
           apply (real_eq_trans _ (real_mult η real_zero) _).
           ++ apply real_mult_comm.
           ++ apply real_mult_zero.
        -- apply (real_le_mult_compat_weak real_zero
                   (real_const (Z.of_nat k # 1)) η).
           ++ exact Hη0.
           ++ exact (b4_lift_nonneg k).
Qed.

Lemma b4_grid_le_b : forall (a b η : Real) (N k : nat),
  real_le real_zero η ->
  real_eq (real_plus a (real_mult (real_const (Z.of_nat N # 1)) η)) b ->
  (k <= N)%nat ->
  real_le (b4_grid a η k) b.
Proof.
  intros a b η N k Hη0 HNb Hkn.
  apply (real_le_trans (b4_grid a η k)
         (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η))
         b).
  - apply (RealSetoid.real_eq_le (b4_grid a η k)
             (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η))).
    exact (b4_grid_sum a η k).
  - apply (real_le_trans (real_plus a (real_mult (real_const (Z.of_nat k # 1)) η))
           (real_plus a (real_mult (real_const (Z.of_nat N # 1)) η))
           b).
    + apply (real_le_plus_compat a a
               (real_mult (real_const (Z.of_nat k # 1)) η)
               (real_mult (real_const (Z.of_nat N # 1)) η)).
      * apply real_le_refl.
      * apply (real_le_mult_compat_weak (real_const (Z.of_nat k # 1))
                 (real_const (Z.of_nat N # 1)) η).
        -- exact Hη0.
        -- exact (b4_lift_le k N Hkn).
    + apply (RealSetoid.real_eq_le
               (real_plus a (real_mult (real_const (Z.of_nat N # 1)) η)) b).
      exact HNb.
Qed.

(* ================= inv 代数件 ================= *)
Lemma b4_inv_cancel : forall (x d : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x (real_mult d (real_inv_pos x Hx))) d.
Proof.
  intros x d Hx.
  apply (real_eq_trans _ (real_mult d (real_mult x (real_inv_pos x Hx))) _).
  - b4_qring.
  - apply (real_eq_trans _ (real_mult d real_one) _).
    + apply (RealSetoid.real_eq_mult_compat d
               (real_mult x (real_inv_pos x Hx)) d real_one).
      * apply real_eq_refl.
      * apply (real_inv_pos_correct x Hx).
    + apply real_mult_one.
Qed.

Lemma b4_inv_left_one : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult (real_inv_pos x Hx) x) real_one.
Proof.
  intros x Hx.
  apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx)) _).
  - apply real_mult_comm.
  - exact (real_inv_pos_correct x Hx).
Qed.

Lemma b4_one_mult : forall (x : Real), real_eq (real_mult real_one x) x.
Proof.
  intros x.
  apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* ================= arch 步长 =================
   d > 0、δ > 0 ⟹ ∃N≥1: η := d·inv(N#1) 满足 0<η、|η| < δ、N#1·η == d *)
Lemma b4_arch_step :
  forall (d delta : Real),
  real_lt real_zero d -> real_lt real_zero delta ->
  sigT (fun N : nat => sigT (fun (HNpos : real_lt real_zero (real_const (Z.of_nat N # 1))) =>
    And (real_lt real_zero (real_mult d (real_inv_pos (real_const (Z.of_nat N # 1)) HNpos)))
        (And (real_lt (real_abs (real_mult d (real_inv_pos (real_const (Z.of_nat N # 1)) HNpos))) delta)
             (real_eq (real_mult (real_const (Z.of_nat N # 1))
                                 (real_mult d (real_inv_pos (real_const (Z.of_nat N # 1)) HNpos)))
                      d)))).
Proof.
  intros d delta Hd Hdelta.
  destruct (real_arch (real_mult d (real_inv_pos delta Hdelta))) as [N [HN2 HNbig]].
  assert (HNpos : real_lt real_zero (real_const (Z.of_nat N # 1))).
  { apply b4_lift_pos. lia. }
  exists N. exists HNpos.
  pose (invN := real_inv_pos (real_const (Z.of_nat N # 1)) HNpos).
  pose (eta := real_mult d invN).
  assert (Heta_pos : real_lt real_zero eta).
  { unfold eta.
    apply real_mult_positive.
    - exact Hd.
    - unfold invN. exact (real_inv_pos_pos (real_const (Z.of_nat N # 1)) HNpos). }
  split.
  - (* 0 < η *)
    exact Heta_pos.
  - split.
    + (* |η| < δ *)
      assert (Hdlt0 : real_lt d (real_mult delta (real_const (Z.of_nat N # 1)))).
      { assert (Hbig2 : real_lt (real_mult delta (real_mult d (real_inv_pos delta Hdelta)))
                                (real_mult delta (real_const (Z.of_nat N # 1)))).
        { apply (real_mult_lt_compat_l (real_mult d (real_inv_pos delta Hdelta))
                                       (real_const (Z.of_nat N # 1)) delta).
          - exact HNbig.
          - exact Hdelta. }
        apply (RealSetoid.real_lt_id_l d
                 (real_mult delta (real_mult d (real_inv_pos delta Hdelta)))
                 (real_mult delta (real_const (Z.of_nat N # 1)))).
        - apply real_eq_sym. exact (b4_inv_cancel delta d Hdelta).
        - exact Hbig2. }
      assert (Hdlt : real_lt d (real_mult (real_const (Z.of_nat N # 1)) delta)).
      { apply (RealSetoid.real_lt_id_r d
                 (real_mult delta (real_const (Z.of_nat N # 1)))
                 (real_mult (real_const (Z.of_nat N # 1)) delta)).
        - apply real_mult_comm.
        - exact Hdlt0. }
      assert (Hm : real_lt (real_mult invN d)
                           (real_mult invN (real_mult (real_const (Z.of_nat N # 1)) delta))).
      { apply (real_mult_lt_compat_l d (real_mult (real_const (Z.of_nat N # 1)) delta) invN).
        - exact Hdlt.
        - unfold invN. exact (real_inv_pos_pos (real_const (Z.of_nat N # 1)) HNpos). }
      assert (Heq2 : real_eq (real_mult invN (real_mult (real_const (Z.of_nat N # 1)) delta)) delta).
      { apply (real_eq_trans _ (real_mult (real_mult invN (real_const (Z.of_nat N # 1))) delta) _).
        - apply real_mult_assoc.
        - apply (real_eq_trans _ (real_mult real_one delta) _).
          + apply (RealSetoid.real_eq_mult_compat
                     (real_mult invN (real_const (Z.of_nat N # 1))) delta real_one delta).
            * unfold invN. apply b4_inv_left_one.
            * apply real_eq_refl.
          + apply b4_one_mult. }
      assert (Hlt_eta : real_lt (real_mult invN d) delta).
      { apply (RealSetoid.real_lt_id_r (real_mult invN d)
                 (real_mult invN (real_mult (real_const (Z.of_nat N # 1)) delta))
                 delta).
        - exact Heq2.
        - exact Hm. }
      assert (Hlt_eta2 : real_lt eta delta).
      { unfold eta.
        apply (RealSetoid.real_lt_id_l (real_mult d invN) (real_mult invN d) delta).
        - apply real_mult_comm.
        - exact Hlt_eta. }
      apply (RealSetoid.real_lt_id_l (real_abs eta) eta delta).
      * apply real_abs_pos_req. exact Heta_pos.
      * exact Hlt_eta2.
    + (* N#1·η == d *)
      unfold eta, invN.
      exact (b4_inv_cancel (real_const (Z.of_nat N # 1)) d HNpos).
Qed.

(* ================= (1/2)·eps < eps（eps > 0） ================= *)
Lemma b4_half_eps_lt : forall (eps : Real), real_lt real_zero eps ->
  real_lt (real_mult (real_const (1 / 2)) eps) eps.
Proof.
  intros eps Heps.
  assert (Hm : real_lt (real_mult eps (real_const (1 / 2)))
                      (real_mult eps real_one)).
  { apply (real_mult_lt_compat_l (real_const (1 / 2)) real_one eps).
    - apply real_const_lt. unfold Qlt. simpl. lia.
    - exact Heps. }
  apply (RealSetoid.real_lt_id_r (real_mult (real_const (1 / 2)) eps)
                                 (real_mult eps real_one) eps).
  - apply (real_mult_one eps).
  - apply (RealSetoid.real_lt_id_l (real_mult (real_const (1 / 2)) eps)
                                   (real_mult eps (real_const (1 / 2)))
                                   (real_mult eps real_one)).
    + apply real_mult_comm.
    + exact Hm.
Qed.

(* ================= Tier1 主引理：均匀模链式 ================= *)

Definition cw_unit (x : Real) : Set :=
  forall n : nat, QleT' (Qabs (projT1 x n)) 1.

(* ---- E(x) := sin(arctan x) − x·cos(arctan x)（x ∈ cw_unit） ---- *)
Definition real_E (x : Real) (Hx : cw_unit x) : Real :=
  real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
            (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))).

(* ---- E(1)（θ := arctan(1)，域证书 atan1_pt_bound 现成） ---- *)
Definition real_E_one : Real := real_E (real_const 1) atan1_pt_bound.

(* ---- E(1) 的定义性展开：E(1) ≡ sin θ − (1·cos θ)（θ := arctan_one_real） ---- *)
Lemma real_E_one_unfold :
  real_eq real_E_one
          (real_plus (cauchy_real_sin arctan_one_real)
                     (real_opp (real_mult (real_const 1) (cauchy_real_cos arctan_one_real)))).
Proof.
  unfold real_E_one, real_E, arctan_one_real.
  apply real_eq_refl.
Qed.

(* ---- 差为零桥：real_eq (a + (−b)) 0 ⟹ real_eq a b ---- *)
Lemma real_eq_minus_zero : forall (a b : Real),
  real_eq (real_plus a (real_opp b)) real_zero -> real_eq a b.
Proof.
  intros a b H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  apply (qltT_eq_compat_l (Qabs (projT1 (real_plus a (real_opp b)) n - projT1 real_zero n))
                          (Qabs (projT1 a n - projT1 b n)) eps).
  - apply (Qabs_wd (projT1 (real_plus a (real_opp b)) n - projT1 real_zero n)
                   (projT1 a n - projT1 b n)).
    rewrite (real_plus_proj a (real_opp b) n).
    rewrite (real_opp_proj b n).
    replace (projT1 real_zero n) with 0 by (unfold real_zero; reflexivity).
    ring.
  - exact HN.
Qed.

(* ---- 1·x == x（real_const 1 作乘数；real_mult_one 是 x·real_one 版） ---- *)
Lemma b5b_const_one_mult : forall (x : Real), real_eq (real_mult (real_const 1) x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

(* ---- b5b_hsc_main（task 4）：E(1) == 0 ⟹ sin θ == cos θ ---- *)
Lemma b5b_hsc_main : real_eq real_E_one real_zero ->
  real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real).
Proof.
  intros HE1.
  (* E(1) == sin θ − (1·cos θ)；E(1) == 0 ⟹ sin θ == 1·cos θ *)
  assert (Hsincos1 : real_eq (cauchy_real_sin arctan_one_real)
                             (real_mult (real_const 1) (cauchy_real_cos arctan_one_real))).
  { apply real_eq_minus_zero.
    apply (real_eq_trans _ real_E_one _).
    - apply real_eq_sym. exact real_E_one_unfold.
    - exact HE1. }
  (* 1·cos θ == cos θ *)
  apply (real_eq_trans _ (real_mult (real_const 1) (cauchy_real_cos arctan_one_real)) _).
  - exact Hsincos1.
  - apply b5b_const_one_mult.
Qed.

(* ============================================================ *)
(* 迭代 210：B4 Tier1 链式主引理 b4_chain_lipschitz                *)
(* 来源：sc2_b4_chain p3；前置件已在上游根模块；零公理面            *)
(* ============================================================ *)

Lemma b4_chain_lipschitz :
  forall (f : Real -> Real) (a b M eps : Real)
    (Hab : real_lt a b) (Heps : real_lt real_zero eps)
    (Hext : forall x y : Real, real_eq x y -> real_eq (f x) (f y))
    (Hmod : sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (x : Real), real_le a x -> real_le x b ->
        forall (h : Real), real_lt (real_abs h) delta ->
        forall (Hxl : real_le a (real_plus x h)) (Hxr : real_le (real_plus x h) b),
        forall (eps1 : Real), real_lt real_zero eps1 ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult M (real_abs h)) eps1)))),
  real_le (real_abs (real_plus (f b) (real_opp (f a))))
          (real_plus (real_mult M (real_abs (real_plus b (real_opp a)))) eps).
Proof.
  intros f a b M eps Hab Heps Hext Hmod.
  destruct Hmod as [delta [Hdelta Hmodd]].
  pose (d := real_plus b (real_opp a)).
  assert (Hd : real_lt real_zero d).
  { unfold d. apply b4_pos_diff. exact Hab. }
  destruct (b4_arch_step d delta Hd Hdelta) as [N [HNpos [Heta_pos [Heta_delta HNeq]]]].
  pose (invN := real_inv_pos (real_const (Z.of_nat N # 1)) HNpos).
  pose (eta := real_mult d invN).
  assert (Heta0 : real_le real_zero eta).
  { apply (RealSetoid.real_lt_le_iff_req real_zero eta). left. exact Heta_pos. }
  (* N#1·η == d（HNeq）；a + N#1·η == b *)
  assert (HNb : real_eq (real_plus a (real_mult (real_const (Z.of_nat N # 1)) eta)) b).
  { apply (real_eq_trans _ (real_plus a d) _).
    - apply (RealSetoid.real_eq_plus_compat a
               (real_mult (real_const (Z.of_nat N # 1)) eta) a d).
      + apply real_eq_refl.
      + exact HNeq.
    - unfold d. b4_qring. }
  (* 预算：epsA := c·invN，c := (1/4)·eps；Σ_k epsA == c *)
  pose (c := real_mult (real_const (1 / 4)) eps).
  pose (epsA := real_mult c invN).
  assert (Hc_pos : real_lt real_zero c).
  { unfold c. apply b4_quarter_pos. exact Heps. }
  assert (HepsA_pos : real_lt real_zero epsA).
  { unfold epsA. apply real_mult_positive.
    - exact Hc_pos.
    - unfold invN. exact (real_inv_pos_pos (real_const (Z.of_nat N # 1)) HNpos). }
  assert (HsumE : real_eq (real_mult (real_const (Z.of_nat N # 1)) epsA) c).
  { unfold epsA.
    exact (b4_lift_inv_cancel N HNpos c). }
  (* 逐点步进界 *)
  assert (Hstep : forall k : nat, (k < N)%nat ->
    real_le (real_abs (real_plus (f (b4_grid a eta (Datatypes.S k)))
                                 (real_opp (f (b4_grid a eta k)))))
            (real_plus (real_mult M (real_abs eta)) epsA)).
  { intros k Hk.
    assert (Hk1 : (Datatypes.S k <= N)%nat) by lia.
    exact (Hmodd (b4_grid a eta k)
                 (b4_grid_ge_a a eta k Heta0)
                 (b4_grid_le_b a b eta N k Heta0 HNb (Nat.lt_le_incl k N Hk))
                 eta Heta_delta
                 (b4_grid_ge_a a eta (Datatypes.S k) Heta0)
                 (b4_grid_le_b a b eta N (Datatypes.S k) Heta0 HNb Hk1)
                 epsA HepsA_pos). }
  (* 望远镜与和式界 *)
  pose (gincr := fun k : nat => real_plus (f (b4_grid a eta (Datatypes.S k))) (real_opp (f (b4_grid a eta k)))).
  pose (econst := fun k : nat => real_plus (real_mult M (real_abs eta)) epsA).
  assert (Htel : real_eq (b4_nsum gincr N)
                         (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat))))).
  { apply (b4_nsum_telescope f (b4_grid a eta) N). }
  assert (Htri : real_le (real_abs (b4_nsum gincr N))
                         (real_plus (b4_nsum (fun k => real_abs (gincr k)) N)
                                    (b4_nsum (fun _ => epsA) N))).
  { apply (b4_nsum_tri gincr (fun _ : nat => epsA) N).
    intros k Hk. exact HepsA_pos. }
  assert (Hle1 : real_le (b4_nsum (fun k => real_abs (gincr k)) N)
                         (b4_nsum econst N)).
  { apply b4_nsum_le. intros k Hk. unfold gincr, econst. exact (Hstep k Hk). }
  assert (HsumC : real_eq (b4_nsum econst N)
                          (real_plus (real_mult M d) c)).
  { unfold econst.
    apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1))
                                      (real_plus (real_mult M (real_abs eta)) epsA)) _).
    - apply (b4_nsum_const (real_plus (real_mult M (real_abs eta)) epsA) N).
    - apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat N # 1))
                                                   (real_mult M (real_abs eta)))
                                        (real_mult (real_const (Z.of_nat N # 1)) epsA)) _).
      + b4_qring.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_const (Z.of_nat N # 1)) (real_mult M (real_abs eta)))
                 (real_mult (real_const (Z.of_nat N # 1)) epsA)
                 (real_mult M d) c).
        * apply (real_eq_trans _ (real_mult M (real_mult (real_const (Z.of_nat N # 1)) (real_abs eta))) _).
          -- b4_qring.
          -- apply (RealSetoid.real_eq_mult_compat M
                     (real_mult (real_const (Z.of_nat N # 1)) (real_abs eta))
                     M d).
             ++ apply real_eq_refl.
             ++ apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1)) eta) _).
                ** apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat N # 1))
                           (real_abs eta) (real_const (Z.of_nat N # 1)) eta).
                   --- apply real_eq_refl.
                   --- apply real_abs_pos_req. exact Heta_pos.
                ** exact HNeq.
        * exact HsumE. }
  (* |f(g_N) − f a| ≤ ((M·d + c) + c) *)
  assert (Hmain_le : real_le (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
                             (real_plus (real_plus (real_mult M d) c) c)).
  { apply (real_le_trans
             (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
             (real_plus (b4_nsum (fun k => real_abs (gincr k)) N)
                        (b4_nsum (fun _ => epsA) N))
             (real_plus (real_plus (real_mult M d) c) c)).
    - apply (RealSetoid.real_le_id_l
               (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
               (real_abs (b4_nsum gincr N))
               (real_plus (b4_nsum (fun k => real_abs (gincr k)) N)
                          (b4_nsum (fun _ => epsA) N))).
      + apply real_abs_eq_compat. apply real_eq_sym. exact Htel.
      + exact Htri.
    - apply (real_le_trans
               (real_plus (b4_nsum (fun k => real_abs (gincr k)) N)
                          (b4_nsum (fun _ => epsA) N))
               (real_plus (b4_nsum econst N)
                          (b4_nsum (fun _ => epsA) N))
               (real_plus (real_plus (real_mult M d) c) c)).
      + apply (real_le_plus_compat
                 (b4_nsum (fun k => real_abs (gincr k)) N)
                 (b4_nsum econst N)
                 (b4_nsum (fun _ => epsA) N)
                 (b4_nsum (fun _ => epsA) N)).
        * exact Hle1.
        * apply real_le_refl.
      + apply (RealSetoid.real_eq_le
                 (real_plus (b4_nsum econst N) (b4_nsum (fun _ : nat => epsA) N))
                 (real_plus (real_plus (real_mult M d) c) c)).
        * apply (RealSetoid.real_eq_plus_compat (b4_nsum econst N)
                   (b4_nsum (fun _ : nat => epsA) N)
                   (real_plus (real_mult M d) c) c).
          -- exact HsumC.
          -- apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1)) epsA) _).
             ++ exact (b4_nsum_const epsA N).
             ++ exact HsumE. }
  (* |f b − f a| == |f(g_N) − f a|（Hext：g_N == b） *)
  assert (HgridN_b : real_eq (b4_grid a eta N) b).
  { apply (real_eq_trans _ (real_plus a (real_mult (real_const (Z.of_nat N # 1)) eta)) _).
    - apply (b4_grid_sum a eta N).
    - exact HNb. }
  assert (Habs_eq : real_eq (real_abs (real_plus (f b) (real_opp (f a))))
                            (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))).
  { apply real_abs_eq_compat.
    apply (RealSetoid.real_eq_plus_compat (f b) (real_opp (f a))
               (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))).
    - apply (Hext b (b4_grid a eta N)). apply real_eq_sym. exact HgridN_b.
    - apply (RealSetoid.real_eq_opp_compat (f a) (f (b4_grid a eta 0%nat))).
      apply (Hext a (b4_grid a eta 0%nat)).
      simpl. apply real_eq_refl. }
  (* 汇合：≤ (M·d + c) + c == M·d + (1/2)eps ≤ M·d + eps，再 |b−a| == d *)
  assert (Hcc : real_eq (real_plus (real_plus (real_mult M d) c) c)
                        (real_plus (real_mult M d) (real_mult (real_const (1 / 2)) eps))).
  { unfold c. b4_qring. }
  assert (Hhalf : real_le (real_mult (real_const (1 / 2)) eps) eps).
  { apply (RealSetoid.real_lt_le_iff_req (real_mult (real_const (1 / 2)) eps) eps).
    left. exact (b4_half_eps_lt eps Heps). }
  assert (Habs_d : real_eq (real_mult M (real_abs (real_plus b (real_opp a))))
                           (real_mult M d)).
  { apply (RealSetoid.real_eq_mult_compat M (real_abs (real_plus b (real_opp a))) M d).
    - apply real_eq_refl.
    - apply real_abs_pos_req. exact Hd. }
  apply (real_le_trans (real_abs (real_plus (f b) (real_opp (f a))))
                       (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
                       (real_plus (real_mult M (real_abs (real_plus b (real_opp a)))) eps)).
  - apply (RealSetoid.real_eq_le (real_abs (real_plus (f b) (real_opp (f a))))
                                 (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))).
    exact Habs_eq.
  - apply (real_le_trans (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
                         (real_plus (real_mult M d) eps)
                         (real_plus (real_mult M (real_abs (real_plus b (real_opp a)))) eps)).
    + apply (real_le_trans (real_abs (real_plus (f (b4_grid a eta N)) (real_opp (f (b4_grid a eta 0%nat)))))
                           (real_plus (real_plus (real_mult M d) c) c)
                           (real_plus (real_mult M d) eps)).
      * exact Hmain_le.
      * apply (real_le_trans
                 (real_plus (real_plus (real_mult M d) c) c)
                 (real_plus (real_mult M d) (real_mult (real_const (1 / 2)) eps))
                 (real_plus (real_mult M d) eps)).
        -- apply (RealSetoid.real_eq_le
                   (real_plus (real_plus (real_mult M d) c) c)
                   (real_plus (real_mult M d) (real_mult (real_const (1 / 2)) eps))).
           exact Hcc.
        -- apply (real_le_plus_compat (real_mult M d) (real_mult M d)
                                     (real_mult (real_const (1 / 2)) eps) eps).
           ++ apply real_le_refl.
           ++ exact Hhalf.
    + apply (RealSetoid.real_eq_le (real_plus (real_mult M d) eps)
                                   (real_plus (real_mult M (real_abs (real_plus b (real_opp a)))) eps)).
      apply (RealSetoid.real_eq_plus_compat (real_mult M d) eps
                 (real_mult M (real_abs (real_plus b (real_opp a)))) eps).
      * apply real_eq_sym. exact Habs_d.
      * apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 迭代 210：B5-B 端点批 01-04（atan 连续/E 端点，19 Qed）          *)
(* 来源：sc2_b5b_endpoint；00_core 已在 209 根                       *)
(* ============================================================ *)

Lemma b5b_ap_tail0 : forall (a : Q) (n : nat), QleT' (Qabs a) 1 ->
  Qle (Qabs (arctan_partial n a - arctan_partial 0 a)) (1 / 3).
Proof.
  intros a n Ha.
  apply (Qle_trans _ (1 / (Z.of_nat (2 * 0 + 3) # 1)) _).
  - apply atan_tail_bound_le; [exact Ha | lia].
  - apply qeq_le.
    replace (2 * 0 + 3)%nat with 3%nat by lia.
    unfold Qdiv. field.
Qed.

(* ---- 2. |S_n a| ≤ 2（|a| ≤ 1，∀n）：三角 + 尾 1/3 + |a| ≤ 1 ---- *)
Lemma b5b_ap_abs_le2 : forall (a : Q) (n : nat), QleT' (Qabs a) 1 ->
  Qle (Qabs (arctan_partial n a)) 2.
Proof.
  intros a n Ha.
  assert (Htri : Qle (Qabs (arctan_partial n a))
                     (Qplus (Qabs (arctan_partial n a - arctan_partial 0 a))
                            (Qabs (arctan_partial 0 a)))).
  { apply (Qle_trans _ (Qabs ((arctan_partial n a - arctan_partial 0 a) +
                              arctan_partial 0 a)) _).
    - apply qeq_le.
      apply (Qabs_wd (arctan_partial n a)
                     ((arctan_partial n a - arctan_partial 0 a) + arctan_partial 0 a)).
      ring.
    - apply Qabs_triangle. }
  apply (Qle_trans _ (1 / 3 + 1) _).
  - apply (Qle_trans _ (Qplus (Qabs (arctan_partial n a - arctan_partial 0 a))
                              (Qabs (arctan_partial 0 a))) _).
    + exact Htri.
    + apply (Qle_trans _ (1 / 3 + Qabs (arctan_partial 0 a)) _).
      * apply Qplus_le_compat.
        -- apply b5b_ap_tail0. exact Ha.
        -- apply Qle_refl.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- (* |S_0 a| == |a| ≤ 1 *)
           apply (Qle_trans _ (Qabs a) _).
           ++ apply qeq_le.
              apply (Qabs_wd (arctan_partial 0 a) a).
              change (arctan_term 0 a == a).
              unfold arctan_term.
              replace (2 * 0 + 1)%nat with 1%nat by lia.
              unfold Qdiv. cbn [q_pow].
              change (Qinv (Z.of_nat 1 # 1)) with 1.
              simpl. ring.
           ++ apply QleT'_to_Qle. exact Ha.
  - apply (Qlt_le_weak (1 / 3 + 1) 2).
    unfold Qlt. compute. reflexivity.
Qed.

(* ---- 3. 固定指标分裂：n ≥ M ⟹ |S_n a − S_n b| ≤ T + (M+1)|a−b| + T，
          T := 1/(2M+3)（|a|,|b| ≤ 1） ---- *)
Lemma b5b_ap_split : forall (M n : nat) (a b : Q), NatLe M n ->
  QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
  Qle (Qabs (arctan_partial n a - arctan_partial n b))
      (Qplus (Qplus (1 / (Z.of_nat (2 * M + 3) # 1))
                    (Qmult (Z.of_nat (Datatypes.S M) # 1) (Qabs (a - b))))
             (1 / (Z.of_nat (2 * M + 3) # 1))).
Proof.
  intros M n a b HMn Ha Hb.
  assert (Hmn : (M <= n)%nat) by (exact (NatLe_drop M n HMn)).
  (* 两次三角：|S_n a − S_n b| ≤ |S_n a − S_M a| + |S_M a − S_M b| + |S_M b − S_n b| *)
  apply (Qle_trans _ (Qplus (Qabs (arctan_partial n a - arctan_partial M a))
                            (Qabs (arctan_partial M a - arctan_partial n b))) _).
  - apply (Qle_trans _ (Qabs ((arctan_partial n a - arctan_partial M a) +
                              (arctan_partial M a - arctan_partial n b))) _).
    + apply qeq_le.
      apply (Qabs_wd (arctan_partial n a - arctan_partial n b)
                     ((arctan_partial n a - arctan_partial M a) +
                      (arctan_partial M a - arctan_partial n b))).
      ring.
    + apply Qabs_triangle.
  - apply (Qle_trans _ (Qplus (Qabs (arctan_partial n a - arctan_partial M a))
                              (Qplus (Qabs (arctan_partial M a - arctan_partial M b))
                                     (Qabs (arctan_partial M b - arctan_partial n b)))) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (Qle_trans _ (Qabs ((arctan_partial M a - arctan_partial M b) +
                                  (arctan_partial M b - arctan_partial n b))) _).
        -- apply qeq_le.
           apply (Qabs_wd (arctan_partial M a - arctan_partial n b)
                          ((arctan_partial M a - arctan_partial M b) +
                           (arctan_partial M b - arctan_partial n b))).
           ring.
        -- apply Qabs_triangle.
    + apply (Qle_trans _ (Qplus (1 / (Z.of_nat (2 * M + 3) # 1))
                                (Qplus (Qmult (Z.of_nat (Datatypes.S M) # 1) (Qabs (a - b)))
                                       (1 / (Z.of_nat (2 * M + 3) # 1)))) _).
      * apply Qplus_le_compat.
        -- (* 尾 1：|S_n a − S_M a| ≤ T *)
           apply atan_tail_bound_le; [exact Ha | exact Hmn].
        -- apply Qplus_le_compat.
           ++ (* 中段：|S_M a − S_M b| ≤ (M+1)|a−b| *)
              apply arctan_partial_lipschitz; [exact Ha | exact Hb].
           ++ (* 尾 2：|S_M b − S_n b| ≤ T（先换绝对值方向再尾界） *)
              apply (Qle_trans _ (Qabs (arctan_partial n b - arctan_partial M b)) _).
              ** apply qeq_le.
                 apply (Qeq_trans _ (Qabs (- (arctan_partial n b - arctan_partial M b))) _).
                 2: apply (Qabs_opp (arctan_partial n b - arctan_partial M b)).
                 apply (Qabs_wd (arctan_partial M b - arctan_partial n b)
                                (- (arctan_partial n b - arctan_partial M b))).
                 ring.
              ** apply atan_tail_bound_le; [exact Hb | exact Hmn].
      * apply qeq_le. ring.
Qed.

Lemma b5b_sin_family_lip : forall (a b B C : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs a) B -> QleT' (Qabs b) B ->
  (forall j : nat, QleT' (exp_series j B) C) ->
  Qle (Qabs (sin_partial n a - sin_partial n b))
      (Qmult (Qabs (a - b)) C).
Proof.
  intros a b B C n HBT Ha Hb HC.
  apply (Qle_trans _ (Qmult (Qabs (a - b)) (sc_cos_series n B)) _).
  - apply (sc_sin_partial_lipschitz a b B n HBT Ha Hb).
  - apply (Qmult_le_compat_nonneg (Qabs (a - b)) (Qabs (a - b))
                                  (sc_cos_series n B) C).
    + split; [apply Qabs_nonneg | apply Qle_refl].
    + split.
      * apply sc_cos_series_nonneg. exact HBT.
      * apply (Qle_trans _ (exp_series (2 * n) B) _).
        -- apply sc_cos_series_le_exp. exact HBT.
        -- exact (QleT'_to_Qle (exp_series (2 * n)%nat B) C (HC (2 * n)%nat)).
Qed.

(* ---- ①' cos 部分和族均匀 Lipschitz（n = 0 分支 + S 形） ---- *)
Lemma b5b_cos_family_lip : forall (a b B C : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs a) B -> QleT' (Qabs b) B ->
  Qle 0 C ->
  (forall j : nat, QleT' (exp_series j B) C) ->
  Qle (Qabs (cos_partial n a - cos_partial n b))
      (Qmult (Qabs (a - b)) C).
Proof.
  intros a b B C n HBT Ha Hb HC0 HC.
  destruct n as [| m].
  - (* n = 0：两侧 == 1，差 0 ≤ |a−b|·C *)
    apply (Qle_trans _ 0 _).
    + apply qeq_le.
      assert (H1 : cos_partial 0 a == 1) by apply sc_cos_partial_zero_const.
      assert (H2 : cos_partial 0 b == 1) by apply sc_cos_partial_zero_const.
      rewrite H1, H2.
      assert (Hd : 1 - 1 == 0) by ring.
      rewrite Hd. reflexivity.
    + apply (Qmult_le_0_compat (Qabs (a - b)) C); [apply Qabs_nonneg | exact HC0].
  - apply (Qle_trans _ (Qmult (Qabs (a - b)) (sc_sin_deriv_series m B)) _).
    + apply (sc_cos_partial_lipschitz_succ a b B m HBT Ha Hb).
    + apply (Qmult_le_compat_nonneg (Qabs (a - b)) (Qabs (a - b))
                                    (sc_sin_deriv_series m B) C).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- apply sc_sin_deriv_series_nonneg. exact HBT.
        -- apply (Qle_trans _ (exp_series (Datatypes.S (2 * m)) B) _).
           ++ apply sc_sin_deriv_series_le_exp. exact HBT.
           ++ exact (QleT'_to_Qle (exp_series (Datatypes.S (2 * m)) B) C (HC (Datatypes.S (2 * m)))).
Qed.

(* ---- ② arch 界（B := 2）：C₂ ≥ 1、∀j exp_series j 2 ≤ C₂ ---- *)
Lemma b5b_arch2 : sigT (fun C : Q => And (QleT' 1 C)
                                          (forall j : nat, QleT' (exp_series j 2) C)).
Proof.
  apply exp_series_arch.
  apply Qle_to_QleT'. change (Qle 0 2). unfold Qle. simpl. lia.
Qed.

(* ---- ③ arctan 一致收敛核心：∃M d0, n ≥ M ∧ |a−b| ≤ d0 ⟹ |S_n a − S_n b| < eps ---- *)
Lemma b5b_ap_uniform : forall (eps : Q), Qlt 0 eps ->
  sigT (fun M : nat => sigT (fun d0 : Q => And (QltT 0 d0)
    (forall (n : nat) (a b : Q), NatLe M n -> QleT' (Qabs a) 1 -> QleT' (Qabs b) 1 ->
       Qle (Qabs (a - b)) d0 ->
       Qlt (Qabs (arctan_partial n a - arctan_partial n b)) eps))).
Proof.
  intros eps Heps.
  (* T := 1/(2M+3) < eps/8：q_arch_inv (eps/8)，取 M := N *)
  assert (H8 : Qlt 0 (eps / 8)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (Qinv 8)).
    - exact Heps.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  destruct (q_arch_inv (eps / 8) H8) as [N HN].
  set (M := N).
  (* d0 := (eps/4)/(M+1)（field 友好：分母独立） *)
  set (d0 := (eps / 4) / (Z.of_nat (Datatypes.S M) # 1)).
  exists M. exists d0.
  split.
  - (* 0 < d0 *)
    assert (H4 : Qlt 0 (eps / 4)).
    { unfold Qdiv. apply (Qmult_lt_0_compat eps (Qinv 4)).
      - exact Heps.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    unfold d0. unfold Qdiv.
    apply Qlt_to_QltT. apply (Qmult_lt_0_compat (Qmult eps (Qinv 4)) (Qinv (Z.of_nat (Datatypes.S M) # 1))).
    + unfold Qdiv in H4. exact H4.
    + apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
  - intros n a b HMn Ha Hb Hab.
    set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
    set (mid := Qmult (Z.of_nat (Datatypes.S M) # 1) (Qabs (a - b))).
    assert (Hmn : (M <= n)%nat) by (exact (NatLe_drop M n HMn)).
    (* |S_n a − S_n b| ≤ T + mid + T *)
    assert (Hsplit : Qle (Qabs (arctan_partial n a - arctan_partial n b))
                         (Qplus (Qplus T mid) T)).
    { unfold T, mid. apply b5b_ap_split. exact HMn. exact Ha. exact Hb. }
    (* 2T < eps/4：T < eps/8 经 atan_inv_chain + HN *)
    assert (H1 : Qlt T (eps / 8)).
    { unfold T. apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1)) _).
      - unfold M. apply atan_inv_chain. lia.
      - exact HN. }
    assert (H2T : Qlt (Qplus T T) (eps / 4)).
    { apply (Qlt_le_trans _ (eps / 8 + eps / 8) _).
      - apply Qplus_lt_compat; exact H1.
      - apply qeq_le. field.
        all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia). }
    (* 消去：d0 := (eps/4)/(M+1) ⟹ (M+1)·d0 == eps/4 *)
    assert (Hcancel : Qmult (Z.of_nat (Datatypes.S M) # 1) d0 == eps / 4).
    { unfold d0. unfold Qdiv. field.
      all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia). }
    (* mid ≤ eps/4 *)
    assert (Hmid : Qle mid (eps / 4)).
    { unfold mid.
      apply (Qle_trans _ (Qmult (Z.of_nat (Datatypes.S M) # 1) d0) _).
      - (* (M+1)·|a−b| ≤ (M+1)·d0 *)
        apply (Qle_trans _ (Qmult (Qabs (a - b)) (Z.of_nat (Datatypes.S M) # 1)) _).
        + apply qeq_le. ring.
        + apply (Qle_trans _ (Qmult d0 (Z.of_nat (Datatypes.S M) # 1)) _).
          * apply (Qmult_le_compat_r (Qabs (a - b)) d0 (Z.of_nat (Datatypes.S M) # 1)).
            -- exact Hab.
            -- unfold Qle. simpl. lia.
          * apply qeq_le. ring.
      - apply qeq_le. exact Hcancel. }
    (* 链：≤ (T+mid)+T == (T+T)+mid ≤ eps/4 + eps/4 < eps *)
    apply (Qle_lt_trans _ (Qplus (Qplus T T) mid) _).
    + apply (Qle_trans _ (Qplus (Qplus T mid) T) _).
      * exact Hsplit.
      * apply qeq_le. ring.
    + apply (Qlt_le_trans _ (Qplus (eps / 4) (eps / 4)) _).
      * apply (Qplus_lt_le_compat (Qplus T T) (eps / 4) mid (eps / 4)).
        -- exact H2T.
        -- exact Hmid.
      * (* eps/4 + eps/4 ≤ eps：差 == eps/2 ≥ 0（Qle_minus_iff 移项） *)
        apply (proj2 (Qle_minus_iff (Qplus (Qdiv eps 4) (Qdiv eps 4)) eps)).
        apply (Qle_trans _ (Qdiv eps 2) _).
        -- apply (Qlt_le_weak 0 (Qdiv eps 2)). apply QltT_to_Qlt. apply (q_half_pos eps (Qlt_to_QltT 0 eps Heps)).
        -- apply qeq_le. field.
Qed.

Lemma b5b_delta_pos : forall (d0 : Q), Qlt 0 d0 ->
  real_lt real_zero (real_const d0).
Proof.
  intros d0 Hd0.
  exists (d0 / 2).
  split.
  { apply (q_half_pos d0). exact (Qlt_to_QltT 0 d0 Hd0). }
  { exists O. intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ d0 _).
    { apply q_half_lt_self. exact Hd0. }
    { apply qeq_le.
      rewrite (real_const_proj d0 n).
      replace (projT1 real_zero n) with 0 by (unfold real_zero; reflexivity).
      ring. } }
Qed.

(* ---- 主引理：arctan 在单位域内逐点连续 ---- *)
Lemma b5b_arctan_cont_unit : forall (x : Real) (Hx : cw_unit x) (epsQ : Q),
  QltT 0 epsQ ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : cw_unit (real_plus x h)),
      real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                   (real_opp (cauchy_real_arctan x Hx))))
              (real_const epsQ))).
Proof.
  intros x Hx epsQ Heps.
  assert (Hepsq : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact Heps).
  assert (Hhalf : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply (q_half_pos epsQ); exact Heps).
  destruct (b5b_ap_uniform (epsQ / 2) Hhalf) as [M [d0 [Hd0 Hcore]]].
  exists (real_const d0).
  split.
  { apply (b5b_delta_pos d0 (QltT_to_Qlt 0 d0 Hd0)). }
  { intros h Hh Hxh.
    left.
    destruct Hh as [eps2 [Heps2 [N2 HN2]]].
    exists (epsQ / 2).
    split.
    { apply Qlt_to_QltT. exact Hhalf. }
    { exists (Nat.max M N2).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (HnM : (M <= n)%nat) by lia.
      assert (HnN2 : (N2 <= n)%nat) by lia.
      (* ① RHS 逐点化：proj (const epsQ) n == epsQ；real_abs/plus/opp/arctan proj 展开 *)
      apply (qltT_eq_compat_r
               (projT1 (real_const epsQ) n -
                projT1 (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                            (real_opp (cauchy_real_arctan x Hx)))) n)
               (epsQ - Qabs (arctan_partial n (projT1 (real_plus x h) n) -
                             arctan_partial n (projT1 x n)))
               (epsQ / 2)).
      { rewrite (real_const_proj epsQ n).
        rewrite (real_abs_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                          (real_opp (cauchy_real_arctan x Hx))) n).
        rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                (real_opp (cauchy_real_arctan x Hx)) n).
        rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
        rewrite (arctan_real_proj (real_plus x h) Hxh n).
        rewrite (arctan_real_proj x Hx n).
        reflexivity. }
      (* ② |proj h n| ≤ d0：HN2（eps2 < d0 − |h_n|）⟹ |h_n| < d0 *)
      assert (Hhn : Qle (Qabs (projT1 h n)) d0).
      { apply Qlt_le_weak.
        apply (Qlt_le_trans _ (Qminus d0 eps2) _).
        { apply (q_lt_minus_shift eps2 d0 (Qabs (projT1 h n))).
          apply (Qlt_le_trans eps2
                              (Qminus (projT1 (real_const d0) n) (projT1 (real_abs h) n))
                              (Qminus d0 (Qabs (projT1 h n)))).
          { apply QltT_to_Qlt. exact (HN2 n (NatLe_lift _ _ HnN2)). }
          { apply qeq_le.
            rewrite (real_const_proj d0 n).
            rewrite (real_abs_proj h n).
            ring. } }
        { apply (proj2 (Qle_minus_iff (Qminus d0 eps2) d0)).
          apply (Qle_trans _ eps2 _).
          { apply (Qlt_le_weak 0 eps2). apply QltT_to_Qlt. exact Heps2. }
          { apply qeq_le. ring. } } }
      (* ③ 核心界（n ≥ M、域、|Δ| ≤ d0）施于原始 proj 项 *)
      assert (Hcore_n : Qlt (Qabs (arctan_partial n (projT1 (real_plus x h) n) -
                                  arctan_partial n (projT1 x n))) (epsQ / 2)).
      { apply (Hcore n (projT1 (real_plus x h) n) (projT1 x n)
                      (NatLe_lift _ _ HnM) (Hxh n) (Hx n)).
        apply (Qle_trans _ (Qabs (projT1 h n)) _).
        { apply qeq_le.
          apply (Qabs_wd (projT1 (real_plus x h) n - projT1 x n) (projT1 h n)).
          rewrite (real_plus_proj x h n).
          ring. }
        { exact Hhn. } }
      (* ④ 结论：epsQ/2 < epsQ − Dn ⟺ Dn < epsQ/2（q_lt_minus_shift） *)
      apply Qlt_to_QltT.
      apply (q_lt_minus_shift (Qabs (arctan_partial n (projT1 (real_plus x h) n) -
                                  arctan_partial n (projT1 x n))) epsQ (epsQ / 2)).
      apply (Qlt_le_trans _ (epsQ / 2) _).
      { exact Hcore_n. }
      { apply qeq_le. field.
        all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia). } } }
Qed.

Lemma b5b_apT2 : forall (a : Q) (n : nat), QleT' (Qabs a) 1 ->
  QleT' (Qabs (arctan_partial n a)) 2.
Proof.
  intros a n Ha.
  apply Qle_to_QleT'.
  apply b5b_ap_abs_le2. exact Ha.
Qed.

(* sin 族 Lipschitz（B := 2，常数 c，|a|,|b| ≤ 2） *)
Lemma b5b_sin_lip2 : forall (n : nat) (a b c : Q),
  (forall j : nat, QleT' (exp_series j 2) c) ->
  QleT' (Qabs a) 2 -> QleT' (Qabs b) 2 ->
  Qle (Qabs (sin_partial n a - sin_partial n b)) (Qmult (Qabs (a - b)) c).
Proof.
  intros n a b c HC Ha Hb.
  apply (b5b_sin_family_lip a b 2 c n).
  - apply Qle_to_QleT'. change (Qle 0 2). unfold Qle. simpl. lia.
  - exact Ha.
  - exact Hb.
  - exact HC.
Qed.

(* cos 族 Lipschitz（B := 2，常数 c，|a|,|b| ≤ 2） *)
Lemma b5b_cos_lip2 : forall (n : nat) (a b c : Q),
  (forall j : nat, QleT' (exp_series j 2) c) ->
  Qle 0 c ->
  QleT' (Qabs a) 2 -> QleT' (Qabs b) 2 ->
  Qle (Qabs (cos_partial n a - cos_partial n b)) (Qmult (Qabs (a - b)) c).
Proof.
  intros n a b c HC Hc0 Ha Hb.
  apply (b5b_cos_family_lip a b 2 c n).
  - apply Qle_to_QleT'. change (Qle 0 2). unfold Qle. simpl. lia.
  - exact Ha.
  - exact Hb.
  - exact Hc0.
  - exact HC.
Qed.

(* |cos_partial n a| ≤ 2c + 1（|a| ≤ 2；|cos_partial n 0| == 1 经 sc_cos_partial_one） *)
Lemma b5b_cos_val2 : forall (n : nat) (a c : Q),
  (forall j : nat, QleT' (exp_series j 2) c) ->
  Qle 0 c ->
  QleT' (Qabs a) 2 ->
  Qle (Qabs (cos_partial n a)) (Qplus (Qmult 2 c) 1).
Proof.
  intros n a c HC Hc0 Ha.
  apply (Qle_trans _ (Qplus (Qabs (cos_partial n a - cos_partial n 0))
                            (Qabs (cos_partial n 0))) _).
  - apply (Qle_trans _ (Qabs ((cos_partial n a - cos_partial n 0) + cos_partial n 0)) _).
    + apply qeq_le.
      apply (Qabs_wd (cos_partial n a)
                     ((cos_partial n a - cos_partial n 0) + cos_partial n 0)).
      ring.
    + apply Qabs_triangle.
  - apply Qplus_le_compat.
    + apply (Qle_trans _ (Qmult (Qabs (a - 0)) c) _).
      * apply (b5b_cos_lip2 n a 0 c HC Hc0 Ha).
        apply Qle_to_QleT'. change (Qle (Qabs 0) 2). unfold Qle, Qabs. simpl. lia.
      * apply (Qle_trans _ (Qmult 2 c) _).
        -- apply (Qmult_le_compat_r (Qabs (a - 0)) 2 c).
           ++ apply (Qle_trans _ (Qabs a) _).
              ** apply qeq_le. apply (Qabs_wd (a - 0) a). ring.
              ** apply QleT'_to_Qle. exact Ha.
           ++ exact Hc0.
        -- apply qeq_le. ring.
    + (* |cos_partial n 0| ≤ 1 *)
      apply (Qle_trans _ 1 _).
      * apply qeq_le.
        apply (Qabs_wd (cos_partial n 0) 1).
        apply sc_cos_partial_one.
      * change (Qle 1 1). apply Qle_refl.
Qed.

(* |1−g| ≤ 1 的 QleT' 形态（0 ≤ g ≤ 1） *)
Lemma b5b_unitQ : forall (g : Q), Qle 0 g -> Qle g 1 ->
  QleT' (Qabs (1 - g)) 1.
Proof.
  intros g Hg0 Hg1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (1 - g) _).
  - apply qeq_imp_qle.
    apply (Qabs_pos (1 - g)).
    apply (proj1 (Qle_minus_iff g 1)). exact Hg1.
  - apply (proj2 (Qle_minus_iff (1 - g) 1)).
    apply (Qle_trans _ g _).
    + exact Hg0.
    + apply qeq_le. ring.
Qed.

(* 单位常数域证书：0 ≤ g ≤ 1 ⟹ cw_unit (real_const (1 − g)) *)
Lemma b5b_unit_const : forall (g : Q), Qle 0 g -> Qle g 1 ->
  cw_unit (real_const (1 - g)).
Proof.
  intros g Hg0 Hg1 n.
  apply Qle_to_QleT'.
  rewrite (real_const_proj (1 - g) n).
  apply (Qle_trans _ (1 - g) _).
  - apply qeq_imp_qle.
    apply (Qabs_pos (1 - g)).
    apply (proj1 (Qle_minus_iff g 1)). exact Hg1.
  - apply (proj2 (Qle_minus_iff (1 - g) 1)).
    apply (Qle_trans _ g _).
    + exact Hg0.
    + apply qeq_le. ring.
Qed.

(* |(1−g)−1| ≤ g（0 ≤ g） *)
Lemma b5b_abs_oneminusg : forall (g : Q), Qle 0 g ->
  Qle (Qabs ((1 - g) - 1)) g.
Proof.
  intros g Hg0.
  apply qeq_imp_qle.
  apply (Qeq_trans _ (Qabs (- g)) _).
  - apply (Qabs_wd ((1 - g) - 1) (- g)). ring.
  - apply (Qeq_trans _ (Qabs g) _).
    + apply Qabs_opp.
    + apply (Qabs_pos g Hg0).
Qed.

(* |g·x| == g·|x|（0 ≤ g） *)
Lemma b5b_abs_gmult : forall (g x : Q), Qle 0 g -> Qabs (g * x) == g * Qabs x.
Proof.
  intros g x Hg0.
  rewrite Qabs_Qmult.
  rewrite (Qabs_pos g Hg0).
  reflexivity.
Qed.

(* ============ B：E_n 点态与主 gap ============ *)

(* E_n(t) := sin_partial n (S_n t) − t·cos_partial n (S_n t) *)
Definition b5b_En (n : nat) (t : Q) : Q :=
  sin_partial n (arctan_partial n t) - t * cos_partial n (arctan_partial n t).

(* proj (real_E y Hy) n == b5b_En n (proj y n) *)
Lemma b5b_En_proj : forall (y : Real) (Hy : cw_unit y) (n : nat),
  projT1 (real_E y Hy) n == b5b_En n (projT1 y n).
Proof.
  intros y Hy n.
  unfold real_E, b5b_En.
  rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan y Hy))
                          (real_opp (real_mult y (cauchy_real_cos (cauchy_real_arctan y Hy)))) n).
  rewrite (real_opp_proj (real_mult y (cauchy_real_cos (cauchy_real_arctan y Hy))) n).
  rewrite (real_mult_proj y (cauchy_real_cos (cauchy_real_arctan y Hy)) n).
  rewrite (real_sin_proj (cauchy_real_arctan y Hy) n).
  rewrite (real_cos_proj (cauchy_real_arctan y Hy) n).
  rewrite (arctan_real_proj y Hy n).
  ring.
Qed.


(* 纯 ring 恒等（顶层无 set-abbrev，ring 可靠） *)
Lemma b5b_ring_assoc_q : forall (a b c : Q), Qplus (Qplus a b) c == Qplus a (Qplus b c).
Proof. intros. ring. Qed.

Lemma b5b_ring_Ediff : forall (sA sB cA cB g : Q),
  sA - (1 - g) * cA - (sB - 1 * cB) == (sA - sB) + ((cB - cA) + (g * cA)).
Proof. intros. ring. Qed.


Lemma b5b_ring_close : forall (c g T G W : Q),
  Qplus (Qmult c (Qplus T (Qplus (Qmult G g) T)))
        (Qplus (Qmult c (Qplus T (Qplus (Qmult G g) T))) (Qmult g W)) ==
  Qplus (Qmult (Qmult 4 c) T)
        (Qmult g (Qplus (Qmult (Qmult 2 c) G) W)).
Proof. intros. ring. Qed.

(* ---- 主 gap：|E_n(1−g) − E_n(1)| ≤ 4c·T + g·(2c(S M) + 2c + 1)，T := 1/(2M+3) ---- *)
Lemma b5b_E_gap : forall (n M : nat) (g c : Q),
  Qle 0 c ->
  (forall j : nat, QleT' (exp_series j 2) c) ->
  Qle 0 g -> Qle g 1 ->
  NatLe M n ->
  Qle (Qabs (b5b_En n (1 - g) - b5b_En n 1))
      (Qplus (Qmult (Qmult 4 c) (1 / (Z.of_nat (2 * M + 3) # 1)))
             (Qmult g (Qplus (Qmult (Qmult 2 c) (Z.of_nat (Datatypes.S M) # 1))
                             (Qplus (Qmult 2 c) 1)))).
Proof.
  intros n M g c Hc0 HC Hg0 Hg1 HMn.
  set (A := arctan_partial n (1 - g)).
  set (B := arctan_partial n 1).
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (G := Z.of_nat (Datatypes.S M) # 1).
  set (W := Qplus (Qmult 2 c) 1).
  set (U := Qplus T (Qplus (Qmult G g) T)).
  set (cU := Qmult c U).
  assert (Hdom : QleT' (Qabs (1 - g)) 1) by (apply (b5b_unitQ g Hg0 Hg1)).
  assert (Hdom1 : QleT' (Qabs 1) 1).
  { apply Qle_to_QleT'. change (Qle (Qabs 1) 1). unfold Qle, Qabs. simpl. lia. }
  assert (HAn : QleT' (Qabs A) 2).
  { unfold A. apply (b5b_apT2 (1 - g) n). exact Hdom. }
  assert (HBn : QleT' (Qabs B) 2).
  { unfold B. apply (b5b_apT2 1 n). exact Hdom1. }
  (* 分裂界：Ab := |A−B| ≤ T + G·|Δ| + T *)
  assert (Hsplit : Qle (Qabs (A - B))
                       (Qplus T (Qplus (Qmult G (Qabs ((1 - g) - 1))) T))).
  { apply (Qle_trans _ (Qplus (Qplus T (Qmult G (Qabs ((1 - g) - 1)))) T) _).
    - unfold A, B, T, G.
      apply (b5b_ap_split M n (1 - g) 1 HMn Hdom Hdom1).
    - apply qeq_le. exact (b5b_ring_assoc_q T (Qmult G (Qabs ((1 - g) - 1))) T). }
  assert (Hgl : Qle (Qmult G (Qabs ((1 - g) - 1))) (Qmult G g)).
  { apply (sc_qmult_le_l (Qabs ((1 - g) - 1)) g G).
    - apply b5b_abs_oneminusg. exact Hg0.
    - unfold G. unfold Qle. simpl. lia. }
  assert (HabU : Qle (Qabs (A - B)) U).
  { apply (Qle_trans _ (Qplus T (Qplus (Qmult G (Qabs ((1 - g) - 1))) T)) _).
    - exact Hsplit.
    - unfold U. apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qplus_le_compat.
        * exact Hgl.
        * apply Qle_refl. }
  (* 三角 1：|En diff| ≤ |sinA−sinB| + (|cosA−cosB| + g·|cosA|) *)
  assert (Htri1 : Qle (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                      (Qplus (Qabs (sin_partial n A - sin_partial n B))
                             (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                    (Qmult g (Qabs (cos_partial n A)))))).
  { unfold b5b_En.
    apply (Qle_trans _ (Qabs ((sin_partial n A - sin_partial n B) +
                              ((cos_partial n B - cos_partial n A) + (g * cos_partial n A)))) _).
    - apply qeq_le.
      apply (Qabs_wd (sin_partial n A - (1 - g) * cos_partial n A -
                      (sin_partial n B - 1 * cos_partial n B))
                     ((sin_partial n A - sin_partial n B) +
                      ((cos_partial n B - cos_partial n A) + (g * cos_partial n A)))).
      exact (b5b_ring_Ediff (sin_partial n A) (sin_partial n B)
                            (cos_partial n A) (cos_partial n B) g).
    - apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                                (Qabs ((cos_partial n B - cos_partial n A) + (g * cos_partial n A)))) _).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply (Qle_trans _ (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                    (Qabs (g * cos_partial n A))) _).
          -- apply Qabs_triangle.
          -- apply Qplus_le_compat.
             ++ apply Qle_refl.
             ++ apply qeq_le. apply (b5b_abs_gmult g (cos_partial n A) Hg0). }
  (* 片界 *)
  assert (Hs : Qle (Qabs (sin_partial n A - sin_partial n B)) (Qmult (Qabs (A - B)) c)).
  { apply (b5b_sin_lip2 n A B c HC HAn HBn). }
  assert (Hco : Qle (Qabs (cos_partial n A - cos_partial n B)) (Qmult (Qabs (A - B)) c)).
  { apply (b5b_cos_lip2 n A B c HC Hc0 HAn HBn). }
  assert (Hval : Qle (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1)).
  { apply (b5b_cos_val2 n A c HC Hc0 HAn). }
  assert (Hgv : Qle (Qmult g (Qabs (cos_partial n A))) (Qmult g W)).
  { unfold W. apply (sc_qmult_le_l (Qabs (cos_partial n A)) (Qplus (Qmult 2 c) 1) g).
    - exact Hval.
    - exact Hg0. }
  (* |cosB−cosA| ≤ |A−B|·c（换向桥） *)
  assert (Hco2 : Qle (Qabs (cos_partial n B - cos_partial n A)) (Qmult (Qabs (A - B)) c)).
  { apply (Qle_trans _ (Qabs (cos_partial n A - cos_partial n B)) _).
    - apply qeq_le. apply Qeq_sym. apply (q_abs_minus_sym (cos_partial n A) (cos_partial n B)).
    - exact Hco. }
  (* 汇总 S1 *)
  assert (HS1 : Qle (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                    (Qplus (Qmult (Qabs (A - B)) c)
                           (Qplus (Qmult (Qabs (A - B)) c) (Qmult g W)))).
  { apply (Qle_trans _ (Qplus (Qabs (sin_partial n A - sin_partial n B))
                              (Qplus (Qabs (cos_partial n B - cos_partial n A))
                                     (Qmult g (Qabs (cos_partial n A))))) _).
    - exact Htri1.
    - apply Qplus_le_compat.
      + exact Hs.
      + apply Qplus_le_compat.
        * exact Hco2.
        * exact Hgv. }
  (* Ab·c ≤ cU *)
  assert (HcAb : Qle (Qmult (Qabs (A - B)) c) cU).
  { apply (Qle_trans _ (Qmult c (Qabs (A - B))) _).
    - apply qeq_le. exact (Qmult_comm (Qabs (A - B)) c).
    - unfold cU.
      apply (sc_qmult_le_l (Qabs (A - B)) U c).
      + exact HabU.
      + exact Hc0. }
  (* S1 ≤ cU + (cU + gW) *)
  assert (HS2 : Qle (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                    (Qplus cU (Qplus cU (Qmult g W)))).
  { apply (Qle_trans _ (Qplus (Qmult (Qabs (A - B)) c)
                              (Qplus (Qmult (Qabs (A - B)) c) (Qmult g W))) _).
    - exact HS1.
    - apply Qplus_le_compat.
      + exact HcAb.
      + apply Qplus_le_compat.
        * exact HcAb.
        * apply Qle_refl. }
  (* 结论：cU + (cU + gW) ≤ Tgt *)
  apply (Qle_trans _ (Qplus cU (Qplus cU (Qmult g W))) _).
  - exact HS2.
  - apply qeq_le.
    unfold cU, U, W, G, T.
    exact (b5b_ring_close c g T G W).
Qed.

(* ============================================================ *)
(* B5-A 微分代数基座            *)
(* （E/S 构造、Q 层基础、sin/cos 复合误差分解代数；11 Qed）；     *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_ode.v；  *)
(* 注：沙箱内 Qeq setoid Instance 重复块（ode.v L20-33）与根     *)
(* L67509-67520 同名，按拼接规格剥除，由根实例供能 setoid 重写。 *)
(* ============================================================ *)

(* ---- QltT 在第二参数 Qeq 上的传输（QltT 不透明不可 setoid 重写；
       用 b4_const_eq 同款 Qcompare_comp 模式） ---- *)
Lemma b5a_QltT_eq_r : forall (a x y : Q), x == y -> QltT a y -> QltT a x.
Proof.
  intros a x y Hxy Hy.
  unfold QltT, Qlt_bool in *.
  assert (Hcmp : Qcompare a x = Qcompare a y).
  { apply (Qcompare_comp a a (Qeq_refl a) x y Hxy). }
  rewrite Hcmp.
  exact Hy.
Qed.

(* Q 层：1/2 < 1 + u²（∀u；Qsquare_nonneg 正性 + 数值比较） *)
Lemma b5a_q_half_lt_one_plus_sq : forall (u : Q), Qlt (1 / 2) (1 + u * u).
Proof.
  intro u.
  apply (Qlt_le_trans (1 / 2) 1 (1 + u * u)).
  - unfold Qlt. simpl. lia.
  - apply (Qle_trans _ (1 + 0) _).
    + apply qeq_le. ring.
    + apply (Qplus_le_compat 1 1 0 (u * u)).
      * apply Qle_refl.
      * apply (Qsquare_nonneg u).
Qed.

(* Q 层 QltT 形态 *)
Lemma b5a_q_half_lt_one_plus_sq_T : forall (u : Q), QltT (1 / 2) (1 + u * u).
Proof. intro u. apply Qlt_to_QltT. apply b5a_q_half_lt_one_plus_sq. Qed.

(* 0 < 1 + x·x（margin 1/2，∀n 点态：1/2 < 1 ≤ 1 + x_n²）——
   arctan' 导数项 inv_pos(1+x²) 的正性见证（无前提，闭项） *)
Lemma b5a_one_plus_sq_pos : forall (x : Real),
  real_lt real_zero (real_plus real_one (real_mult x x)).
Proof.
  intro x.
  unfold real_lt.
  exists (1 / 2)%Q.
  split.
  - (* QltT 0 (1/2) *)
    apply Qlt_to_QltT.
    unfold Qlt. simpl. lia.
  - exists 0%nat.
    intros n Hn.
    (* 目标：QltT (1/2) ((real_plus real_one (real_mult x x))_n − real_zero_n) *)
    assert (Hq : projT1 (real_plus real_one (real_mult x x)) n - projT1 real_zero n ==
                 1 + (projT1 x n * projT1 x n)).
    { setoid_rewrite (real_plus_proj real_one (real_mult x x) n).
      setoid_rewrite (real_mult_proj x x n).
      cbn [projT1 real_one projT1 real_zero].
      ring. }
    apply (b5a_QltT_eq_r (1 / 2)
                         (projT1 (real_plus real_one (real_mult x x)) n - projT1 real_zero n)
                         (1 + (projT1 x n * projT1 x n)) Hq).
    apply b5a_q_half_lt_one_plus_sq_T.
Qed.

(* ============================================================ *)
(* 批 1：未落地件 Section Variable 类型声明（B3 / B4 的规格）    *)
(* 全部引理将置于此 Section 内；End 时自动泛化为 forall 参数。    *)
(* ============================================================ *)
Section B5A_Ode.

(* ---- arctan'（B3 形态；扰动点证书由调用方提供 ——
        exp/log 模板：|x|<1 前提以逐点 |x_n| ≤ 1 见证承载；
        域 [0,1) 覆盖由 B3 保证。导数项 = h·inv_pos(1+x²)。） ---- *)
Variable real_arctan_deriv :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                        (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ---- B4 主链式件：均匀模（δ₀ 与 x 无关）⟹ Lipschitz 界 ---- *)
Variable real_deriv_bound_lipschitz :
  forall (f : Real -> Real) (a b : Real) (M : Real),
  (forall (x : Real), real_le a x -> real_le x b ->
    forall (eps : Real), real_lt real_zero eps ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (h : Real), real_lt (real_abs h) delta ->
        forall (eps' : Real), real_lt real_zero eps' ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult M (real_abs h)) eps')))) ->
  forall (eps_final : Real), real_lt real_zero eps_final ->
  real_le (real_abs (real_plus (f b) (real_opp (f a))))
          (real_plus (real_mult M (real_abs (real_plus b (real_opp a)))) eps_final).

(* ---- B4 M→0 情形：均匀零模 ⟹ f a == f b ---- *)
Variable real_deriv_zero_const :
  forall (f : Real -> Real) (a b : Real),
  (forall (x : Real), real_le a x -> real_le x b ->
    forall (eps : Real), real_lt real_zero eps ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (h : Real), real_lt (real_abs h) delta ->
        forall (eps' : Real), real_lt real_zero eps' ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x)))) eps'))) ->
  real_eq (f a) (f b).

(* ============================================================ *)
(* 批 1：E / S / J 构造（Real 层函数组合起点）                   *)
(* E 含 arctan ⟹ 需逐点 |x_n| ≤ 1 证书：E(x,Hx)。                *)
(* S := exp((1/2)·log(1+x²)) == (1+x²)^{1/2}（exp∘log，全域，   *)
(*     正性见证 b5a_one_plus_sq_pos 闭项给出）→ 无输入证书。      *)
(* ============================================================ *)

(* E(x) := sin(arctan x) − x·cos(arctan x)（certified） *)
Definition b5a_E (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real :=
  real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
            (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x Hx)))).

(* S(x) := exp((1/2)·log(1+x²))（全域总函数） *)
Definition b5a_S (x : Real) : Real :=
  cauchy_real_exp (real_mult (real_const (1 / 2))
                             (real_log (real_plus real_one (real_mult x x))
                                       (b5a_one_plus_sq_pos x))).

(* 引理骨架：E 在 [0,1) 有理点 == 0 的声明目标（批 4 证）：
Lemma b5a_closure_E_zero_on_unit : ... *)

End B5A_Ode.

(* ============================================================ *)
(* 批 2：item-1 sin∘arctan 复合可微 —— 误差分解（real_eq 代数锚）*)
(* D := sin(arctan(x+h)) − sinA − cosA·d·h                       *)
(*    == sinA·(cos v − 1) + cosA·(sin v − v) + cosA·(v − d·h)    *)
(* 其中 A := arctan x、v := arctan(x+h) − arctan x、              *)
(*      d := inv(1+x²)、sinA := sin A、cosA := cos A。            *)
(* 后续批 3 的 eps-delta 界：三件套 cos v−1（0 点线性化）≈ −v²/2、 *)
(* sin v−v ≈ v³/6、v−dh（arctan' 误差）各 ≤ eps 份额。            *)
(* ============================================================ *)

(* ---- Q 层 sin/cos 部分和参数 Qeq 全等（B2 沙箱件未并入根，自建） ---- *)
Lemma b5a_sin_term_wd : forall (j : nat) (x y : Q), x == y -> sin_term j x == sin_term j y.
Proof.
  intros j x y Hxy.
  unfold sin_term, Qdiv.
  apply Qmult_comp.
  - apply Qeq_refl.
  - apply Qmult_comp.
    + apply (q_pow_wd x y (Datatypes.S (2 * j)) Hxy).
    + apply Qeq_refl.
Qed.

Lemma b5a_cos_term_wd : forall (j : nat) (x y : Q), x == y -> cos_term j x == cos_term j y.
Proof.
  intros j x y Hxy.
  unfold cos_term, Qdiv.
  apply Qmult_comp.
  - apply Qeq_refl.
  - apply Qmult_comp.
    + apply (q_pow_wd x y (2 * j) Hxy).
    + apply Qeq_refl.
Qed.

Lemma b5a_sin_partial_wd : forall (n : nat) (x y : Q), x == y ->
  sin_partial n x == sin_partial n y.
Proof.
  intros n x y Hxy.
  induction n as [| n IH]; simpl.
  - apply (b5a_sin_term_wd 0 x y Hxy).
  - apply Qplus_comp.
    + exact IH.
    + apply (b5a_sin_term_wd (Datatypes.S n) x y Hxy).
Qed.

Lemma b5a_cos_partial_wd : forall (n : nat) (x y : Q), x == y ->
  cos_partial n x == cos_partial n y.
Proof.
  intros n x y Hxy.
  induction n as [| n IH]; simpl.
  - apply (b5a_cos_term_wd 0 x y Hxy).
  - apply Qplus_comp.
    + exact IH.
    + apply (b5a_cos_term_wd (Datatypes.S n) x y Hxy).
Qed.

(* sin/cos 在"逐点精确相等"参数上的外延（real_eq 参数 ⟹ real_eq 值）——
   eps-delta 复合代数第一步：sin(arctan(x+h)) == sin(A+v) 类换形 *)
Lemma b5a_sin_wd_exact : forall (u v : Real),
  (forall n : nat, projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_sin u) (cauchy_real_sin v).
Proof.
  intros u v Heq.
  apply real_eq_of_zero_diff. intro n.
  rewrite (real_sin_proj u n).
  rewrite (real_sin_proj v n).
  assert (H : sin_partial n (projT1 u n) == sin_partial n (projT1 v n)).
  { apply (b5a_sin_partial_wd n (projT1 u n) (projT1 v n) (Heq n)). }
  rewrite H. ring.
Qed.

Lemma b5a_cos_wd_exact : forall (u v : Real),
  (forall n : nat, projT1 u n == projT1 v n) ->
  real_eq (cauchy_real_cos u) (cauchy_real_cos v).
Proof.
  intros u v Heq.
  apply real_eq_of_zero_diff. intro n.
  rewrite (real_cos_proj u n).
  rewrite (real_cos_proj v n).
  assert (H : cos_partial n (projT1 u n) == cos_partial n (projT1 v n)).
  { apply (b5a_cos_partial_wd n (projT1 u n) (projT1 v n) (Heq n)). }
  rewrite H. ring.
Qed.

(* ---- 复合件命名（item-1 对象） ---- *)
Definition b5a_atan_d (x : Real) : Real :=
  real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x).

Definition b5a_comp_err_sin (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  real_plus (cauchy_real_sin (cauchy_real_arctan (real_plus x h) Hxh))
    (real_opp (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
                         (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                    (real_mult (b5a_atan_d x) h)))).

(* D == sinA·(cos v − 1) + cosA·(sin v − v) + cosA·(v − d·h) *)
Lemma b5a_sin_atan_err_decomp :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (b5a_comp_err_sin x Hx h Hxh)
    (real_plus
       (real_plus
          (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                     (real_plus (cauchy_real_cos
                                   (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                              (real_opp (cauchy_real_arctan x Hx))))
                                (real_opp real_one)))
          (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                     (real_plus (cauchy_real_sin
                                   (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                              (real_opp (cauchy_real_arctan x Hx))))
                                (real_opp (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                     (real_opp (cauchy_real_arctan x Hx)))))))
       (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                  (real_plus (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                        (real_opp (cauchy_real_arctan x Hx)))
                             (real_opp (real_mult (b5a_atan_d x) h))))).
Proof.
  intros x Hx h Hxh.
  set (A := cauchy_real_arctan x Hx).
  set (Ah := cauchy_real_arctan (real_plus x h) Hxh).
  set (v := real_plus Ah (real_opp A)).
  (* 1) sin(Ah) == sin(A+v)：逐点精确（A_n + (Ah_n − A_n) == Ah_n） *)
  assert (Hw : real_eq (cauchy_real_sin Ah) (cauchy_real_sin (real_plus A v))).
  { apply b5a_sin_wd_exact. intro n.
    unfold v.
    rewrite (real_plus_proj A (real_plus Ah (real_opp A)) n).
    rewrite (real_plus_proj Ah (real_opp A) n).
    rewrite (real_opp_proj A n).
    ring. }
  (* 2) 目标改写链：D == [sin(A+v) + opp(...)] == [sinA·cosv + cosA·sinv + opp(...)] == T *)
  apply (real_eq_trans (b5a_comp_err_sin x Hx h Hxh)
         (real_plus (cauchy_real_sin (real_plus A v))
                    (real_opp (real_plus (cauchy_real_sin A)
                                         (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h)))))).
  - (* D == sin(A+v)+opp(...)：unfold + plus-compat（sin Ah == sin(A+v)） *)
    unfold b5a_comp_err_sin.
    apply (RealSetoid.real_eq_plus_compat
             (cauchy_real_sin (cauchy_real_arctan (real_plus x h) Hxh))
             (real_opp (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
                                  (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                             (real_mult (b5a_atan_d x) h))))
             (cauchy_real_sin (real_plus A v))
             (real_opp (real_plus (cauchy_real_sin A)
                                  (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h))))).
    + exact Hw.
    + apply (RealSetoid.real_eq_opp_compat
               (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
                          (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                     (real_mult (b5a_atan_d x) h)))
               (real_plus (cauchy_real_sin A)
                          (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h)))).
      apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_sin (cauchy_real_arctan x Hx))
               (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                          (real_mult (b5a_atan_d x) h))
               (cauchy_real_sin A)
               (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h))).
      * unfold A. apply real_eq_refl.
      * apply (RealSetoid.real_eq_mult_compat
                 (cauchy_real_cos (cauchy_real_arctan x Hx))
                 (real_mult (b5a_atan_d x) h)
                 (cauchy_real_cos A)
                 (real_mult (b5a_atan_d x) h)).
        -- unfold A. apply real_eq_refl.
        -- apply real_eq_refl.
  - (* sin(A+v)+opp(...) == T：rs_add_sin 展开 + ring *)
    apply (real_eq_trans
      (real_plus (cauchy_real_sin (real_plus A v))
                 (real_opp (real_plus (cauchy_real_sin A)
                                      (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h)))))
      (real_plus (real_plus (real_mult (cauchy_real_sin A) (cauchy_real_cos v))
                            (real_mult (cauchy_real_cos A) (cauchy_real_sin v)))
                 (real_opp (real_plus (cauchy_real_sin A)
                                      (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h)))))
      (real_plus
         (real_plus
            (real_mult (cauchy_real_sin A)
                       (real_plus (cauchy_real_cos v) (real_opp real_one)))
            (real_mult (cauchy_real_cos A)
                       (real_plus (cauchy_real_sin v) (real_opp v))))
         (real_mult (cauchy_real_cos A)
                    (real_plus v (real_opp (real_mult (b5a_atan_d x) h)))))).
    + apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_sin (real_plus A v))
               (real_opp (real_plus (cauchy_real_sin A)
                                    (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h))))
               (real_plus (real_mult (cauchy_real_sin A) (cauchy_real_cos v))
                          (real_mult (cauchy_real_cos A) (cauchy_real_sin v)))
               (real_opp (real_plus (cauchy_real_sin A)
                                    (real_mult (cauchy_real_cos A) (real_mult (b5a_atan_d x) h))))).
      * apply (rs_add_sin A v).
      * apply real_eq_refl.
    + (* ring 证毕：逐点 Q-ring（sinA/cosA/cosv/sinv/v/d·h 为原子） *)
      apply real_eq_of_zero_diff. intro n.
      repeat (first [ rewrite real_plus_proj | rewrite real_opp_proj
                    | rewrite real_mult_proj | rewrite real_const_proj ]).
      cbn [projT1 real_one projT1 real_zero].
      ring.
Qed.

(* ---- cos∘arctan 复合误差（G := cos∘arctan，G' = −sinA·d）---- *)
Definition b5a_comp_err_cos (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1) : Real :=
  real_plus (cauchy_real_cos (cauchy_real_arctan (real_plus x h) Hxh))
    (real_opp (real_plus (cauchy_real_cos (cauchy_real_arctan x Hx))
                         (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                              (real_mult (b5a_atan_d x) h))))).

(* D_cos == cosA·(cos v − 1) − sinA·(sin v − v) − sinA·(v − d·h) *)
Lemma b5a_cos_atan_err_decomp :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
    (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  real_eq (b5a_comp_err_cos x Hx h Hxh)
    (real_plus
       (real_plus
          (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                     (real_plus (cauchy_real_cos
                                   (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                              (real_opp (cauchy_real_arctan x Hx))))
                                (real_opp real_one)))
          (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                               (real_plus (cauchy_real_sin
                                             (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                        (real_opp (cauchy_real_arctan x Hx))))
                                          (real_opp (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                               (real_opp (cauchy_real_arctan x Hx))))))))
       (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                            (real_plus (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                  (real_opp (cauchy_real_arctan x Hx)))
                                       (real_opp (real_mult (b5a_atan_d x) h)))))).
Proof.
  intros x Hx h Hxh.
  set (A := cauchy_real_arctan x Hx).
  set (Ah := cauchy_real_arctan (real_plus x h) Hxh).
  set (v := real_plus Ah (real_opp A)).
  assert (Hw : real_eq (cauchy_real_cos Ah) (cauchy_real_cos (real_plus A v))).
  { apply b5a_cos_wd_exact. intro n.
    unfold v.
    rewrite (real_plus_proj A (real_plus Ah (real_opp A)) n).
    rewrite (real_plus_proj Ah (real_opp A) n).
    rewrite (real_opp_proj A n).
    ring. }
  apply (real_eq_trans (b5a_comp_err_cos x Hx h Hxh)
         (real_plus (cauchy_real_cos (real_plus A v))
                    (real_opp (real_plus (cauchy_real_cos A)
                                         (real_opp (real_mult (cauchy_real_sin A)
                                                              (real_mult (b5a_atan_d x) h))))))).
  - unfold b5a_comp_err_cos.
    apply (RealSetoid.real_eq_plus_compat
             (cauchy_real_cos (cauchy_real_arctan (real_plus x h) Hxh))
             (real_opp (real_plus (cauchy_real_cos (cauchy_real_arctan x Hx))
                                  (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                       (real_mult (b5a_atan_d x) h)))))
             (cauchy_real_cos (real_plus A v))
             (real_opp (real_plus (cauchy_real_cos A)
                                  (real_opp (real_mult (cauchy_real_sin A)
                                                       (real_mult (b5a_atan_d x) h)))))).
    + exact Hw.
    + apply (RealSetoid.real_eq_opp_compat
               (real_plus (cauchy_real_cos (cauchy_real_arctan x Hx))
                          (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                               (real_mult (b5a_atan_d x) h))))
               (real_plus (cauchy_real_cos A)
                          (real_opp (real_mult (cauchy_real_sin A)
                                               (real_mult (b5a_atan_d x) h))))).
      apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_cos (cauchy_real_arctan x Hx))
               (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                    (real_mult (b5a_atan_d x) h)))
               (cauchy_real_cos A)
               (real_opp (real_mult (cauchy_real_sin A)
                                    (real_mult (b5a_atan_d x) h)))).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_opp_compat
                 (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                            (real_mult (b5a_atan_d x) h))
                 (real_mult (cauchy_real_sin A)
                            (real_mult (b5a_atan_d x) h))).
        apply (RealSetoid.real_eq_mult_compat
                 (cauchy_real_sin (cauchy_real_arctan x Hx))
                 (real_mult (b5a_atan_d x) h)
                 (cauchy_real_sin A)
                 (real_mult (b5a_atan_d x) h)).
        -- apply real_eq_refl.
        -- apply real_eq_refl.
  - apply (real_eq_trans
      (real_plus (cauchy_real_cos (real_plus A v))
                 (real_opp (real_plus (cauchy_real_cos A)
                                      (real_opp (real_mult (cauchy_real_sin A)
                                                           (real_mult (b5a_atan_d x) h))))))
      (real_plus (real_plus (real_mult (cauchy_real_cos A) (cauchy_real_cos v))
                            (real_opp (real_mult (cauchy_real_sin A) (cauchy_real_sin v))))
                 (real_opp (real_plus (cauchy_real_cos A)
                                      (real_opp (real_mult (cauchy_real_sin A)
                                                           (real_mult (b5a_atan_d x) h))))))
      (real_plus
         (real_plus
            (real_mult (cauchy_real_cos A)
                       (real_plus (cauchy_real_cos v) (real_opp real_one)))
            (real_opp (real_mult (cauchy_real_sin A)
                                 (real_plus (cauchy_real_sin v) (real_opp v)))))
         (real_opp (real_mult (cauchy_real_sin A)
                              (real_plus v (real_opp (real_mult (b5a_atan_d x) h))))))).
    + apply (RealSetoid.real_eq_plus_compat
               (cauchy_real_cos (real_plus A v))
               (real_opp (real_plus (cauchy_real_cos A)
                                    (real_opp (real_mult (cauchy_real_sin A)
                                                         (real_mult (b5a_atan_d x) h)))))
               (real_plus (real_mult (cauchy_real_cos A) (cauchy_real_cos v))
                          (real_opp (real_mult (cauchy_real_sin A) (cauchy_real_sin v))))
               (real_opp (real_plus (cauchy_real_cos A)
                                    (real_opp (real_mult (cauchy_real_sin A)
                                                         (real_mult (b5a_atan_d x) h)))))).
      * apply (rs_add_cos A v).
      * apply real_eq_refl.
    + apply real_eq_of_zero_diff. intro n.
      repeat (first [ rewrite real_plus_proj | rewrite real_opp_proj
                    | rewrite real_mult_proj | rewrite real_const_proj ]).
      cbn [projT1 real_one projT1 real_zero].
      ring.
Qed.

(* ============================================================ *)
(* B5-A 续做                    *)
(* （单位域证书/提升件/S 正性/E(0)==0/item-2 代数核心；26 Qed）； *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_cont.v  *)
(* ============================================================ *)

(* ============================================================ *)
(* Part 0：Q 层小工具 + 常值正性见证                             *)
(* ============================================================ *)

Lemma b5c_half_pos : QltT 0 (1 / 2).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* real_const (1/2) > 0 的 Real 见证（reusable） *)
Definition b5c_half_rpos : real_lt real_zero (real_const (1 / 2)) :=
  real_const_pos (1 / 2) b5c_half_pos.

Lemma b5c_quarter_pos : QltT 0 (1 / 4).
Proof. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* ============================================================ *)
(* Part A：单位域证书（有理点 [0,1] 的 cw_unit 证书）             *)
(* ============================================================ *)

(* Q 层：0 ≤ q ≤ 1 ⟹ |q| ≤ 1（QleT'） *)
Lemma b5c_qleT_unit : forall (q : Q), Qle 0 q -> Qle q 1 ->
  QleT' (Qabs q) 1.
Proof.
  intros q Hq0 Hq1.
  apply Qle_to_QleT'.
  apply (Qle_trans _ q _).
  - apply qeq_imp_qle. apply (Qabs_pos q Hq0).
  - exact Hq1.
Qed.

(* 0 ≤ q ≤ 1 ⟹ cw_unit (real_const q) *)
Lemma b5c_const_unit : forall (q : Q), Qle 0 q -> Qle q 1 ->
  forall n : nat, QleT' (Qabs (projT1 (real_const q) n)) 1.
Proof.
  intros q Hq0 Hq1 n.
  apply Qle_to_QleT'.
  rewrite (real_const_proj q n).
  apply (Qle_trans _ q _).
  - apply qeq_imp_qle. apply (Qabs_pos q Hq0).
  - exact Hq1.
Qed.

(* 常数证书：real_const 0 的单位证书（E(0)/J(0) 用） *)
Definition b5c_unit_zero : forall n : nat,
  QleT' (Qabs (projT1 (real_const 0) n)) 1 :=
  b5c_const_unit 0 (Qle_refl 0) (Qle_0_1).

(* ============================================================ *)
(* Part B：d(x) := inv_pos(1+x²) 的 Real 层界                    *)
(* ============================================================ *)

(* 1/2 < 1 + x²（Real 层；见证 1/4，∀x 闭项——inv 反单调输入） *)
Lemma b5c_one_sq_half_lt : forall (x : Real),
  real_lt (real_const (1 / 2)) (real_plus real_one (real_mult x x)).
Proof.
  intro x.
  unfold real_lt.
  exists (1 / 4)%Q.
  split.
  - exact b5c_quarter_pos.
  - exists 0%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hq : projT1 (real_plus real_one (real_mult x x)) n
                   - projT1 (real_const (1 / 2)) n ==
                 (1 / 2) + (projT1 x n * projT1 x n)).
    { setoid_rewrite (real_plus_proj real_one (real_mult x x) n).
      setoid_rewrite (real_mult_proj x x n).
      rewrite (real_const_proj (1 / 2) n).
      cbn [projT1 real_one].
      field. }
    setoid_rewrite Hq.
    apply (Qlt_le_trans (1 / 4) (1 / 2) ((1 / 2) + (projT1 x n * projT1 x n))).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans _ ((1 / 2) + 0) _).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat (1 / 2) (1 / 2) 0 (projT1 x n * projT1 x n)).
        -- apply Qle_refl.
        -- apply (Qsquare_nonneg (projT1 x n)).
Qed.

(* 0 < d(x) *)
Lemma b5c_d_pos : forall (x : Real),
  real_lt real_zero (b5a_atan_d x).
Proof.
  intro x.
  unfold b5a_atan_d.
  apply real_inv_pos_pos.
Qed.

(* inv(1/2) == real_const 2（real_inv_proj：∃N 全 n≥N 逐点 Qinv(1/2) == 2） *)
Lemma b5c_inv_half_two :
  real_eq (real_inv_pos (real_const (1 / 2)) b5c_half_rpos) (real_const 2).
Proof.
  intros eps Heps.
  destruct (real_inv_proj (real_const (1 / 2)) b5c_half_rpos) as [Ni HNi].
  exists Ni.
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hproj : projT1 (real_inv_pos (real_const (1 / 2)) b5c_half_rpos) n == Qinv (1 / 2)).
  { apply NatLe_drop in Hn.
    transitivity (Qinv (projT1 (real_const (1 / 2)) n)).
    - exact (HNi n Hn).
    - apply (Qinv_comp (projT1 (real_const (1 / 2)) n) (1 / 2)).
      rewrite (real_const_proj (1 / 2) n).
      reflexivity. }
  setoid_rewrite Hproj.
  rewrite (real_const_proj 2 n).
  assert (Hq2 : Qinv (1 / 2) == 2) by field.
  rewrite Hq2.
  rewrite (Qabs_pos 0).
  - apply QltT_to_Qlt. exact Heps.
  - apply Qle_refl.
Qed.

(* d(x) < 2：inv 反单调（1/2 < 1+x² ⟹ inv(1+x²) < inv(1/2) == 2） *)
Lemma b5c_d_lt_two : forall (x : Real),
  real_lt (b5a_atan_d x) (real_const 2).
Proof.
  intro x.
  unfold b5a_atan_d.
  apply (RealSetoid.real_lt_id_r (real_inv_pos (real_plus real_one (real_mult x x))
                                    (b5a_one_plus_sq_pos x))
                      (real_inv_pos (real_const (1 / 2)) b5c_half_rpos)
                      (real_const 2)).
  - exact b5c_inv_half_two.
  - apply (real_inv_pos_lt_contra (real_const (1 / 2))
                                  (real_plus real_one (real_mult x x))).
    exact (b5c_one_sq_half_lt x).
Qed.

(* |d(x)| == d(x)（0 < d） *)
Lemma b5c_d_abs : forall (x : Real),
  real_eq (real_abs (b5a_atan_d x)) (b5a_atan_d x).
Proof.
  intro x.
  apply real_abs_pos_req.
  exact (b5c_d_pos x).
Qed.

(* ============================================================ *)
(* Part C：逐点界提升件（§5.1 提升件清单）                       *)
(*  |a·w| ≤ M·|w| + sh（输入：逐点 ∀n QleT' |a_n| ≤ M，M > 0）   *)
(*  证明：real_lt 见证（sh 的分离 sh0 作 eps0，逐点差值 ≥ sh_n > sh0）*)
(* ============================================================ *)

Lemma b5c_abs_mult_le : forall (a w : Real) (M : Q),
  QltT 0 M ->
  (forall n : nat, QleT' (Qabs (projT1 a n)) M) ->
  forall (sh : Real), real_lt real_zero sh ->
  real_le (real_abs (real_mult a w))
          (real_plus (real_mult (real_const M) (real_abs w)) sh).
Proof.
  intros a w M HM Ha sh Hsh.
  destruct Hsh as [sh0 [Hsh0 [Nsh HshN]]].
  apply (RealSetoid.real_lt_le_iff_req (real_abs (real_mult a w))
                                       (real_plus (real_mult (real_const M) (real_abs w)) sh)).
  left.
  unfold real_lt.
  exists sh0.
  split.
  - exact Hsh0.
  - exists Nsh.
    intros n Hn.
    assert (HX : projT1 (real_abs (real_mult a w)) n ==
                 Qabs (projT1 a n * projT1 w n)).
    { setoid_rewrite (real_abs_proj (real_mult a w) n).
      setoid_rewrite (real_mult_proj a w n).
      reflexivity. }
    assert (HY : projT1 (real_plus (real_mult (real_const M) (real_abs w)) sh) n ==
                 M * Qabs (projT1 w n) + projT1 sh n).
    { setoid_rewrite (real_plus_proj (real_mult (real_const M) (real_abs w)) sh n).
      setoid_rewrite (real_mult_proj (real_const M) (real_abs w) n).
      setoid_rewrite (real_abs_proj w n).
      rewrite (real_const_proj M n).
      reflexivity. }
    set (Yn := M * Qabs (projT1 w n) + projT1 sh n).
    set (Xn := Qabs (projT1 a n * projT1 w n)).
    (* 目标（投影改写后）：QltT sh0 (Yn − Xn) *)
    apply (qltT_eq_compat_r (projT1 (real_plus (real_mult (real_const M) (real_abs w)) sh) n
                              - projT1 (real_abs (real_mult a w)) n)
                            (Yn - Xn) sh0).
    { setoid_rewrite HY. setoid_rewrite HX. reflexivity. }
    (* 现在：QltT sh0 (Yn − Xn)；改证 Qlt sh0 (Yn − Xn) *)
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    (* |a_n·w_n| ≤ M·|w_n| *)
    assert (Hle : Qle (Qabs (projT1 a n * projT1 w n)) (M * Qabs (projT1 w n))).
    { rewrite (Qabs_Qmult (projT1 a n) (projT1 w n)).
      apply (Qmult_le_compat_r (Qabs (projT1 a n)) M (Qabs (projT1 w n))).
      - apply QleT'_to_Qle. exact (Ha n).
      - apply Qabs_nonneg. }
    assert (Hdiff0 : Qle 0 (M * Qabs (projT1 w n) - Qabs (projT1 a n * projT1 w n))).
    { apply (proj1 (Qle_minus_iff (Qabs (projT1 a n * projT1 w n)) (M * Qabs (projT1 w n)))).
      exact Hle. }
    assert (Hshn : Qlt sh0 (projT1 sh n)).
    { apply (Qlt_le_trans sh0 (projT1 sh n - projT1 real_zero n) (projT1 sh n)).
      - apply QltT_to_Qlt. exact (HshN n Hn).
      - rewrite Hz.
        assert (Hz0 : projT1 sh n - 0 == projT1 sh n) by ring.
        rewrite Hz0. apply Qle_refl. }
    (* sh_n ≤ Yn − Xn *)
    assert (Hle2 : Qle (projT1 sh n) (Yn - Xn)).
    { unfold Yn, Xn.
      apply (Qle_trans (projT1 sh n)
                       (projT1 sh n + (M * Qabs (projT1 w n) - Qabs (projT1 a n * projT1 w n)))
                       (M * Qabs (projT1 w n) + projT1 sh n - Qabs (projT1 a n * projT1 w n))).
      - apply (Qle_trans (projT1 sh n) (projT1 sh n + 0)
                         (projT1 sh n + (M * Qabs (projT1 w n) - Qabs (projT1 a n * projT1 w n)))).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat (projT1 sh n) (projT1 sh n) 0
                                 (M * Qabs (projT1 w n) - Qabs (projT1 a n * projT1 w n))).
          * apply Qle_refl.
          * exact Hdiff0.
      - apply qeq_le. ring. }
    apply (Qlt_le_trans sh0 (projT1 sh n) (Yn - Xn)).
    + exact Hshn.
    + exact Hle2.
Qed.

(* |w| ≤ W̄（real_le）⟹ |a·w| ≤ M·W̄ + sh（M > 0，逐点 |a_n| ≤ M） *)
Lemma b5c_abs_mult_le_wbar : forall (a w Wbar : Real) (M : Q),
  QltT 0 M ->
  (forall n : nat, QleT' (Qabs (projT1 a n)) M) ->
  real_le (real_abs w) Wbar ->
  forall (sh : Real), real_lt real_zero sh ->
  real_le (real_abs (real_mult a w))
          (real_plus (real_mult (real_const M) Wbar) sh).
Proof.
  intros a w Wbar M HM Ha Hw sh Hsh.
  apply (real_le_trans (real_abs (real_mult a w))
                       (real_plus (real_mult (real_const M) (real_abs w)) sh)
                       (real_plus (real_mult (real_const M) Wbar) sh)).
  - exact (b5c_abs_mult_le a w M HM Ha sh Hsh).
  - apply (real_le_plus_compat (real_mult (real_const M) (real_abs w))
                               (real_mult (real_const M) Wbar) sh sh).
    + apply (RealSetoid.real_le_id_l (real_mult (real_const M) (real_abs w))
                                     (real_mult (real_abs w) (real_const M))
                                     (real_mult (real_const M) Wbar)).
      * apply real_mult_comm.
      * apply (RealSetoid.real_le_id_r (real_mult (real_abs w) (real_const M))
                                       (real_mult Wbar (real_const M))
                                       (real_mult (real_const M) Wbar)).
        -- apply real_mult_comm.
        -- apply (real_le_mult_compat_weak (real_abs w) Wbar (real_const M)).
           ++ apply (RealSetoid.real_lt_le_iff_req real_zero (real_const M)). left.
              apply real_const_pos. exact HM.
           ++ exact Hw.
    + apply real_le_refl.
Qed.

(* ============================================================ *)
(* Part D：S 正性 / J 构造 / E(0) == 0 / J(0) == 0               *)
(* ============================================================ *)

(* S(x) := exp((1/2)·log(1+x²)) > 0（exp 全域正性） *)
Lemma b5c_S_pos : forall (x : Real),
  real_lt real_zero (b5a_S x).
Proof.
  intro x.
  unfold b5a_S.
  apply cauchy_real_exp_pos.
Qed.

(* J := E·S^{-1} *)
Definition b5c_J (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real :=
  real_mult (b5a_E x Hx) (real_inv_pos (b5a_S x) (b5c_S_pos x)).

(* arctan_term k 0 == 0 *)
Lemma b5c_arctan_term_zero : forall (k : nat), arctan_term k 0 == 0.
Proof.
  intro k.
  unfold arctan_term.
  unfold Qdiv.
  assert (Hpow : q_pow 0 (2 * k + 1) == 0).
  { rewrite (Nat.add_1_r (2 * k)). rewrite (q_pow_succ 0 (2 * k)). ring. }
  rewrite Hpow.
  ring.
Qed.

(* arctan_partial n 0 == 0 *)
Lemma b5c_arctan_partial_zero : forall (n : nat), arctan_partial n 0 == 0.
Proof.
  intro n.
  induction n as [| m IH]; simpl.
  - apply b5c_arctan_term_zero.
  - rewrite IH. rewrite (Qplus_0_l (arctan_term (Datatypes.S m) 0)).
    exact (b5c_arctan_term_zero (Datatypes.S m)).
Qed.

(* 逐点：proj (arctan (real_const 0)) n == 0 *)
Lemma b5c_arctan_term_wd : forall (k : nat) (x y : Q), x == y ->
  arctan_term k x == arctan_term k y.
Proof.
  intros k x y Hxy.
  unfold arctan_term, Qdiv.
  apply Qmult_comp.
  - apply Qeq_refl.
  - apply Qmult_comp.
    + apply (q_pow_wd x y (2 * k + 1) Hxy).
    + apply Qeq_refl.
Qed.

Lemma b5c_arctan_partial_wd : forall (n : nat) (x y : Q), x == y ->
  arctan_partial n x == arctan_partial n y.
Proof.
  intros n x y Hxy.
  induction n as [| m IH]; simpl.
  - apply (b5c_arctan_term_wd 0 x y Hxy).
  - apply Qplus_comp.
    + exact IH.
    + apply (b5c_arctan_term_wd (Datatypes.S m) x y Hxy).
Qed.

Lemma b5c_arctan_const0_proj : forall (H0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 1)
  (n : nat),
  projT1 (cauchy_real_arctan (real_const 0) H0) n == 0.
Proof.
  intros H0 n.
  rewrite (arctan_real_proj (real_const 0) H0 n).
  apply (Qeq_trans _ (arctan_partial n 0) _).
  - apply (b5c_arctan_partial_wd n (projT1 (real_const 0) n) 0).
    rewrite (real_const_proj 0 n). reflexivity.
  - exact (b5c_arctan_partial_zero n).
Qed.

(* arctan(real_const 0) == 0 *)
Lemma b5c_arctan_const0 : forall (H0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 1),
  real_eq (cauchy_real_arctan (real_const 0) H0) real_zero.
Proof.
  intro H0.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (b5c_arctan_const0_proj H0 n).
  cbn [projT1 real_zero].
  reflexivity.
Qed.

(* sin(real_zero) == real_zero（逐点 sin_partial n 0 == 0，根 sc_sin_partial_zero） *)
Lemma b5c_sin_zero : real_eq (cauchy_real_sin real_zero) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_sin_proj real_zero n).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz.
  rewrite (sc_sin_partial_zero n).
  cbn [projT1 real_zero].
  reflexivity.
Qed.

(* cos(real_zero) == real_one（逐点 cos_partial n 0 == 1，根 sc_cos_partial_one） *)
Lemma b5c_cos_one : real_eq (cauchy_real_cos real_zero) real_one.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_cos_proj real_zero n).
  assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
  rewrite Hz.
  rewrite (sc_cos_partial_one n).
  cbn [projT1 real_one].
  reflexivity.
Qed.

(* E(real_const 0) == real_zero（sin(arctan 0) − 0·cos(arctan 0) == 0 − 0） *)
Lemma b5c_E_zero_at_zero : forall (H0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 1),
  real_eq (b5a_E (real_const 0) H0) real_zero.
Proof.
  intro H0.
  unfold b5a_E.
  (* sin(arctan 0) == sin 0 == 0 *)
  assert (Hs0 : real_eq (cauchy_real_sin (cauchy_real_arctan (real_const 0) H0)) real_zero).
  { apply (real_eq_trans (cauchy_real_sin (cauchy_real_arctan (real_const 0) H0))
                         (cauchy_real_sin real_zero) real_zero).
    - apply (b5a_sin_wd_exact (cauchy_real_arctan (real_const 0) H0) real_zero).
      intros n. exact (b5c_arctan_const0_proj H0 n).
    - exact b5c_sin_zero. }
  (* 0·cos(arctan 0) == 0 *)
  assert (Hm0 : real_eq (real_mult (real_const 0) (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))
                        real_zero).
  { apply (real_eq_trans (real_mult (real_const 0) (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))
                         (real_mult real_zero (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))
                         real_zero).
    - apply (RealSetoid.real_eq_mult_compat (real_const 0) (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0))
                                            real_zero (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0))).
      + apply real_eq_of_zero_diff. intro n.
        rewrite (real_const_proj 0 n).
        assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
        rewrite Hz. reflexivity.
      + apply real_eq_refl.
    - apply (real_eq_trans (real_mult real_zero (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))
                           real_zero real_zero).
      + apply real_eq_of_zero_diff. intro n.
        rewrite (real_mult_proj real_zero (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)) n).
        cbn [projT1 real_zero]. ring.
      + apply real_eq_refl. }
  (* E(0) == sin0stuff + (−(0stuff)) == 0 + (−0) == 0 *)
  apply (real_eq_trans (real_plus (cauchy_real_sin (cauchy_real_arctan (real_const 0) H0))
                                  (real_opp (real_mult (real_const 0)
                                                       (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))))
                       (real_plus real_zero (real_opp real_zero))
                       real_zero).
  - apply (RealSetoid.real_eq_plus_compat
             (cauchy_real_sin (cauchy_real_arctan (real_const 0) H0))
             (real_opp (real_mult (real_const 0) (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0))))
             real_zero (real_opp real_zero)).
    + exact Hs0.
    + apply (RealSetoid.real_eq_opp_compat
               (real_mult (real_const 0) (cauchy_real_cos (cauchy_real_arctan (real_const 0) H0)))
               real_zero).
      exact Hm0.
  - apply (real_eq_trans (real_plus real_zero (real_opp real_zero)) real_zero real_zero).
    + apply real_plus_opp.
    + apply real_eq_refl.
Qed.

(* J(real_const 0) == 0（E(0) == 0 ⟹ E(0)·S(0)^{-1} == 0） *)
Lemma b5c_J_zero_at_zero : forall (H0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 1),
  real_eq (b5c_J (real_const 0) H0) real_zero.
Proof.
  intro H0.
  unfold b5c_J.
  apply (real_eq_trans (real_mult (b5a_E (real_const 0) H0)
                                  (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0))))
                       (real_mult real_zero (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0))))
                       real_zero).
  - apply (RealSetoid.real_eq_mult_compat (b5a_E (real_const 0) H0)
                                           (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0)))
                                           real_zero
                                           (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0)))).
    + exact (b5c_E_zero_at_zero H0).
    + apply real_eq_refl.
  - apply (real_eq_trans (real_mult real_zero (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0))))
                         real_zero real_zero).
    + apply real_eq_of_zero_diff. intro n.
      rewrite (real_mult_proj real_zero (real_inv_pos (b5a_S (real_const 0)) (b5c_S_pos (real_const 0))) n).
      cbn [projT1 real_zero]. ring.
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Part E：item-2 代数核心恒等（无 Variable，纯 real_eq 代数）    *)
(*   E := sA − x·cA（sA := sin A，cA := cos A，A := arctan x）    *)
(*   E'(x) 组装式 := cA·d − cA + x·sA·d  ==  x·E·d  (d := inv(1+x²)) *)
(*   差 == cA·(d·(1+x²) − 1) == cA·0 == 0（real_inv_pos_correct）  *)
(* ============================================================ *)

(* E'(x) 的组装式（item-2 的"导数项形态"） *)
Definition b5c_E_form (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real :=
  real_plus (real_plus (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx)) (b5a_atan_d x))
                       (real_opp (cauchy_real_cos (cauchy_real_arctan x Hx))))
            (real_mult (real_mult x (cauchy_real_sin (cauchy_real_arctan x Hx))) (b5a_atan_d x)).

(* x·E(x)·d（item-2 目标线性项的内部系数） *)
Definition b5c_E_lin (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real :=
  real_mult (real_mult x (b5a_E x Hx)) (b5a_atan_d x).

(* W := d·(1+x²) − 1（== 0，inv_pos_correct） *)
Definition b5c_W (x : Real) : Real :=
  real_plus (real_mult (b5a_atan_d x) (real_plus real_one (real_mult x x)))
            (real_opp real_one).

Definition b5c_cA (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) : Real :=
  cauchy_real_cos (cauchy_real_arctan x Hx).

(* W == 0：d·(1+x²) == (1+x²)·d == 1（real_inv_pos_correct + 交换律） *)
Lemma b5c_W_zero : forall (x : Real), real_eq (b5c_W x) real_zero.
Proof.
  intro x.
  unfold b5c_W, b5a_atan_d.
  apply (real_eq_trans (real_plus (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                             (b5a_one_plus_sq_pos x))
                                             (real_plus real_one (real_mult x x)))
                                  (real_opp real_one))
                       (real_plus real_one (real_opp real_one))
                       real_zero).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                      (b5a_one_plus_sq_pos x))
                        (real_plus real_one (real_mult x x)))
             (real_opp real_one)
             real_one (real_opp real_one)).
    + apply (real_eq_trans (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b5a_one_plus_sq_pos x))
                                      (real_plus real_one (real_mult x x)))
                           (real_mult (real_plus real_one (real_mult x x))
                                      (real_inv_pos (real_plus real_one (real_mult x x))
                                                    (b5a_one_plus_sq_pos x)))
                           real_one).
      * apply real_mult_comm.
      * exact (real_inv_pos_correct (real_plus real_one (real_mult x x))
                                    (b5a_one_plus_sq_pos x)).
    + apply real_eq_refl.
  - apply real_plus_opp.
Qed.

(* 差为零：E'-form − xEd − cA·W == 0（逐点 Q ring，原子 sA/cA/d/x） *)
Lemma b5c_E_deriv_diff_zero : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_eq (real_plus (real_plus (b5c_E_form x Hx) (real_opp (b5c_E_lin x Hx)))
                     (real_opp (real_mult (b5c_cA x Hx) (b5c_W x))))
          real_zero.
Proof.
  intros x Hx.
  unfold b5c_E_form, b5c_E_lin, b5c_W, b5c_cA, b5a_E.
  apply real_eq_of_zero_diff. intro n.
  repeat (first [ rewrite real_plus_proj | rewrite real_opp_proj
                | rewrite real_mult_proj | rewrite real_const_proj ]).
  cbn [projT1 real_zero real_one].
  simpl. ring.
Qed.

(* 主件：E'(x) == x·E(x)·d（item-2 代数核心；E' 组装式 == 目标线性项系数） *)
Lemma b5c_E_deriv_core : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  real_eq (b5c_E_form x Hx) (b5c_E_lin x Hx).
Proof.
  intros x Hx.
  assert (Hmid : real_eq (real_plus (b5c_E_form x Hx) (real_opp (b5c_E_lin x Hx))) real_zero).
  { apply (real_eq_trans (real_plus (b5c_E_form x Hx) (real_opp (b5c_E_lin x Hx)))
                         (real_mult (b5c_cA x Hx) (b5c_W x))
                         real_zero).
    - apply (real_eq_minus_zero (real_plus (b5c_E_form x Hx) (real_opp (b5c_E_lin x Hx)))
                                (real_mult (b5c_cA x Hx) (b5c_W x))).
      exact (b5c_E_deriv_diff_zero x Hx).
    - apply (real_eq_trans (real_mult (b5c_cA x Hx) (b5c_W x))
                           (real_mult (b5c_cA x Hx) real_zero)
                           real_zero).
      + apply (RealSetoid.real_eq_mult_compat (b5c_cA x Hx) (b5c_W x)
                                              (b5c_cA x Hx) real_zero).
        * apply real_eq_refl.
        * exact (b5c_W_zero x).
      + apply real_mult_zero. }
  apply (real_eq_minus_zero (b5c_E_form x Hx) (b5c_E_lin x Hx)).
  exact Hmid.
Qed.

(* ============================================================ *)
(* Part F：item-1 逐点 Q 路线的预备件（route (i) 需要）          *)
(* ============================================================ *)

(* 1 + x_n² ≥ 1（逐点，∀x） *)
Lemma b5c_one_sq_proj_ge_one : forall (x : Real) (n : nat),
  Qle 1 (projT1 (real_plus real_one (real_mult x x)) n).
Proof.
  intros x n.
  assert (H : projT1 (real_plus real_one (real_mult x x)) n ==
              1 + (projT1 x n * projT1 x n)).
  { setoid_rewrite (real_plus_proj real_one (real_mult x x) n).
    setoid_rewrite (real_mult_proj x x n).
    cbn [projT1 real_one].
    ring. }
  rewrite H.
  apply (Qle_trans 1 (1 + 0) (1 + (projT1 x n * projT1 x n))).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat 1 1 0 (projT1 x n * projT1 x n)).
    + apply Qle_refl.
    + apply (Qsquare_nonneg (projT1 x n)).
Qed.

(* Q 层：0 < y、1 ≤ y ⟹ Qinv y ≤ 1（1 − Qinv y == (y−1)·Qinv y ≥ 0） *)
Lemma b5c_qinv_le_one : forall (y : Q), Qlt 0 y -> Qle 1 y -> Qle (Qinv y) 1.
Proof.
  intros y Hy0 Hy1.
  apply (proj2 (Qle_minus_iff (Qinv y) 1)).
  assert (Hf : 1 - Qinv y == (y - 1) * Qinv y) by (field; exact (q_neq_of_lt y Hy0)).
  rewrite Hf.
  assert (Hy1m : Qle 0 (y - 1)).
  { apply (proj1 (Qle_minus_iff 1 y)). exact Hy1. }
  assert (Hinv0 : Qle 0 (Qinv y)).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy0. }
  apply (Qle_trans 0 (0 * Qinv y) ((y - 1) * Qinv y)).
  - apply qeq_le. ring.
  - apply (Qmult_le_compat_r 0 (y - 1) (Qinv y)).
    + exact Hy1m.
    + exact Hinv0.
Qed.

(* 逐点（eventual）：|proj d n| == d_n ≤ 1（real_inv_proj：n ≥ N 时   *)
(* d_n == Qinv(1+x_n²)，0 < 1+x_n² 且 1 ≤ 1+x_n² ⟹ Qinv ≤ 1）        *)
Lemma b5c_d_proj_le_one : forall (x : Real),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (b5a_atan_d x) n)) 1).
Proof.
  intro x.
  unfold b5a_atan_d.
  destruct (real_inv_proj (real_plus real_one (real_mult x x))
                          (b5a_one_plus_sq_pos x)) as [Ni HNi].
  exists Ni.
  intros n Hn.
  assert (Hproj : projT1 (real_inv_pos (real_plus real_one (real_mult x x))
                                       (b5a_one_plus_sq_pos x)) n ==
                  Qinv (projT1 (real_plus real_one (real_mult x x)) n)).
  { exact (HNi n Hn). }
  rewrite Hproj.
  assert (Hge1 : Qle 1 (projT1 (real_plus real_one (real_mult x x)) n)).
  { exact (b5c_one_sq_proj_ge_one x n). }
  assert (Hpos : Qlt 0 (projT1 (real_plus real_one (real_mult x x)) n)).
  { apply (Qlt_le_trans 0 1 (projT1 (real_plus real_one (real_mult x x)) n)).
    - unfold Qlt. simpl. lia.
    - exact Hge1. }
  (* |Qinv y| == Qinv y（0 < Qinv y）≤ 1 *)
  apply (Qle_trans (Qabs (Qinv (projT1 (real_plus real_one (real_mult x x)) n)))
                   (Qinv (projT1 (real_plus real_one (real_mult x x)) n))
                   1).
  - apply qeq_imp_qle.
    apply (Qabs_pos (Qinv (projT1 (real_plus real_one (real_mult x x)) n))).
    apply (Qlt_le_weak 0 (Qinv (projT1 (real_plus real_one (real_mult x x)) n))).
    apply Qinv_lt_0_compat. exact Hpos.
  - apply (b5c_qinv_le_one (projT1 (real_plus real_one (real_mult x x)) n)).
    + exact Hpos.
    + exact Hge1.
Qed.

(* ============================================================ *)
(* B5-A item-1 逐点 Q 层全证    *)
(* （I1-I6 + J1-J3 装配套，40 Qed；主引理 b5a_sin/cos_atan_diff  *)
(* 未入文件，外层装配留后续批）；来源：                          *)
(* 演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item1.v       *)
(* ============================================================ *)

(* ============================================================ *)
(* Part I0：item-1 目标语句（§4.1 精确形态；续批抄用）           *)
(*   Lemma b5a_sin_atan_diff : forall (x : Real)                *)
(*     (Hx : forall n, QleT' (Qabs (projT1 x n)) 1),            *)
(*     forall (eps : Real), real_lt real_zero eps ->            *)
(*     sigT (fun delta : Real => And (real_lt real_zero delta)  *)
(*       (forall (h : Real), real_lt (real_abs h) delta ->      *)
(*         forall (Hxh : forall n, QleT' (Qabs (projT1 (real_plus x h) n)) 1), *)
(*         forall (eps' : Real), real_lt real_zero eps' ->      *)
(*         real_le (real_abs (b5a_comp_err_sin x Hx h Hxh))     *)
(*                 (real_plus (real_mult eps (real_abs h)) eps')))). *)
(*   b5a_cos_atan_diff 同构于 b5a_comp_err_cos。                *)
(* ============================================================ *)

Section B5A_Item1.

(* ---- arctan'（B3 形态；sc2_b5a_ode.v §B5A_Ode 同款规格）---- *)
Variable real_arctan_deriv :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                        (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* Part I1：逐点投影代数（纯 x/Hx/h/Hxh，无 Variable 依赖）     *)
(* ============================================================ *)

(* 逐点：proj (b5a_comp_err_sin x Hx h Hxh) n 的完全展开 *)
Lemma b5i_sin_err_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (b5a_comp_err_sin x Hx h Hxh) n ==
  sin_partial n (arctan_partial n (projT1 (real_plus x h) n))
  - sin_partial n (arctan_partial n (projT1 x n))
  - cos_partial n (arctan_partial n (projT1 x n))
    * (projT1 (b5a_atan_d x) n * projT1 h n).
Proof.
  intros x Hx h Hxh n.
  unfold b5a_comp_err_sin.
  (* 外层：real_plus (sin(arctan(x+h))) (opp (...)) *)
  setoid_rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan (real_plus x h) Hxh))
                                 (real_opp (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                      (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                                                 (real_mult (b5a_atan_d x) h)))) n).
  setoid_rewrite (real_opp_proj (real_plus (cauchy_real_sin (cauchy_real_arctan x Hx))
                                           (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                                      (real_mult (b5a_atan_d x) h))) n).
  setoid_rewrite (real_plus_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                 (real_mult (cauchy_real_cos (cauchy_real_arctan x Hx))
                                            (real_mult (b5a_atan_d x) h)) n).
  setoid_rewrite (real_mult_proj (cauchy_real_cos (cauchy_real_arctan x Hx))
                                 (real_mult (b5a_atan_d x) h) n).
  setoid_rewrite (real_mult_proj (b5a_atan_d x) h n).
  setoid_rewrite (real_sin_proj (cauchy_real_arctan (real_plus x h) Hxh) n).
  setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
  setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
  setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
  setoid_rewrite (arctan_real_proj x Hx n).
  ring.
Qed.

(* cos 版投影展开 *)
Lemma b5i_cos_err_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (b5a_comp_err_cos x Hx h Hxh) n ==
  cos_partial n (arctan_partial n (projT1 (real_plus x h) n))
  - cos_partial n (arctan_partial n (projT1 x n))
  - (- (sin_partial n (arctan_partial n (projT1 x n))
        * (projT1 (b5a_atan_d x) n * projT1 h n))).
Proof.
  intros x Hx h Hxh n.
  unfold b5a_comp_err_cos.
  setoid_rewrite (real_plus_proj (cauchy_real_cos (cauchy_real_arctan (real_plus x h) Hxh))
                                 (real_opp (real_plus (cauchy_real_cos (cauchy_real_arctan x Hx))
                                                      (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                                           (real_mult (b5a_atan_d x) h))))) n).
  setoid_rewrite (real_opp_proj (real_plus (cauchy_real_cos (cauchy_real_arctan x Hx))
                                           (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                                (real_mult (b5a_atan_d x) h)))) n).
  setoid_rewrite (real_plus_proj (cauchy_real_cos (cauchy_real_arctan x Hx))
                                 (real_opp (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                                      (real_mult (b5a_atan_d x) h))) n).
  setoid_rewrite (real_opp_proj (real_mult (cauchy_real_sin (cauchy_real_arctan x Hx))
                                           (real_mult (b5a_atan_d x) h)) n).
  setoid_rewrite (real_mult_proj (cauchy_real_sin (cauchy_real_arctan x Hx))
                                 (real_mult (b5a_atan_d x) h) n).
  setoid_rewrite (real_mult_proj (b5a_atan_d x) h n).
  setoid_rewrite (real_cos_proj (cauchy_real_arctan (real_plus x h) Hxh) n).
  setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
  setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
  setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
  setoid_rewrite (arctan_real_proj x Hx n).
  ring.
Qed.

(* 逐点精确 S1/S2 分裂：D_n == [Δsin − cA·v] + cA·(v − d·h) *)
(* v_n := arctan_partial n (x_n+h_n) − arctan_partial n x_n       *)
Lemma b5i_sin_err_split : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (b5a_comp_err_sin x Hx h Hxh) n ==
  (sin_partial n (arctan_partial n (projT1 (real_plus x h) n))
   - sin_partial n (arctan_partial n (projT1 x n))
   - cos_partial n (arctan_partial n (projT1 x n))
     * (arctan_partial n (projT1 (real_plus x h) n)
        - arctan_partial n (projT1 x n)))
  + cos_partial n (arctan_partial n (projT1 x n))
    * ((arctan_partial n (projT1 (real_plus x h) n)
         - arctan_partial n (projT1 x n))
       - projT1 (b5a_atan_d x) n * projT1 h n).
Proof.
  intros x Hx h Hxh n.
  rewrite (b5i_sin_err_proj x Hx h Hxh n).
  ring.
Qed.

(* |arctan_partial n (x_n)| ≤ 2（|x_n| ≤ 1） *)
Lemma b5i_A_norm_le2 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1) (n : nat),
  Qle (Qabs (arctan_partial n (projT1 x n))) 2.
Proof.
  intros x Hx n.
  apply (b5b_ap_abs_le2 (projT1 x n) n).
  exact (Hx n).
Qed.

(* |arctan_partial n ((x+h)_n)| ≤ 2（|(x+h)_n| ≤ 1） *)
Lemma b5i_Ah_norm_le2 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  Qle (Qabs (arctan_partial n (projT1 (real_plus x h) n))) 2.
Proof.
  intros x Hx h Hxh n.
  apply (b5b_ap_abs_le2 (projT1 (real_plus x h) n) n).
  exact (Hxh n).
Qed.

(* |v_n| ≤ 4（v_n := Ah_n − A_n） *)
Lemma b5i_v_norm_le4 : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  Qle (Qabs (arctan_partial n (projT1 (real_plus x h) n)
            - arctan_partial n (projT1 x n))) 4.
Proof.
  intros x Hx h Hxh n.
  apply (Qle_trans _ (Qabs (arctan_partial n (projT1 (real_plus x h) n))
                        + Qabs (- arctan_partial n (projT1 x n))) _).
  - unfold Qminus. apply Qabs_triangle.
  - apply (Qle_trans _ (2 + 2) _).
    + apply Qplus_le_compat.
      * exact (b5i_Ah_norm_le2 x Hx h Hxh n).
      * apply (Qle_trans (Qabs (- arctan_partial n (projT1 x n)))
                         (Qabs (arctan_partial n (projT1 x n))) 2).
        -- apply qeq_imp_qle. apply Qabs_opp.
        -- exact (b5i_A_norm_le2 x Hx n).
    + unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* Part I2：逐点 cos/sin 部分和范数界（cos/sin A 的 norm bound） *)
(* ============================================================ *)

(* |sin_partial n (A_n)| ≤ Ms 逐点（Ms 由 real_norm_bounded (sin A)） *)
Lemma b5i_sinA_bounded : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  sigT (fun Ms : Q => And (QltT 0 Ms)
    (forall n : nat,
      Qle (Qabs (sin_partial n (arctan_partial n (projT1 x n)))) Ms)).
Proof.
  intros x Hx.
  destruct (real_norm_bounded (cauchy_real_sin (cauchy_real_arctan x Hx))) as [Ms [HMs Hpt]].
  exists Ms.
  split.
  - exact HMs.
  - intro n.
    apply (Qle_trans (Qabs (sin_partial n (arctan_partial n (projT1 x n))))
                     (Qabs (projT1 (cauchy_real_sin (cauchy_real_arctan x Hx)) n))
                     Ms).
    + apply qeq_le. apply Qabs_wd.
      apply Qeq_sym.
      setoid_rewrite (real_sin_proj (cauchy_real_arctan x Hx) n).
      setoid_rewrite (arctan_real_proj x Hx n).
      reflexivity.
    + apply QleT'_to_Qle. exact (Hpt n).
Qed.

(* |cos_partial n (A_n)| ≤ Mc 逐点 *)
Lemma b5i_cosA_bounded : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  sigT (fun Mc : Q => And (QltT 0 Mc)
    (forall n : nat,
      Qle (Qabs (cos_partial n (arctan_partial n (projT1 x n)))) Mc)).
Proof.
  intros x Hx.
  destruct (real_norm_bounded (cauchy_real_cos (cauchy_real_arctan x Hx))) as [Mc [HMc Hpt]].
  exists Mc.
  split.
  - exact HMc.
  - intro n.
    apply (Qle_trans (Qabs (cos_partial n (arctan_partial n (projT1 x n))))
                     (Qabs (projT1 (cauchy_real_cos (cauchy_real_arctan x Hx)) n))
                     Mc).
    + apply qeq_le. apply Qabs_wd.
      apply Qeq_sym.
      setoid_rewrite (real_cos_proj (cauchy_real_arctan x Hx) n).
      setoid_rewrite (arctan_real_proj x Hx n).
      reflexivity.
    + apply QleT'_to_Qle. exact (Hpt n).
Qed.

(* |cos_partial n (v_n)| ≤ Mcv 逐点（cos v 的 norm bound） *)
Lemma b5i_cosv_bounded : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  sigT (fun Mcv : Q => And (QltT 0 Mcv)
    (forall n : nat,
      Qle (Qabs (cos_partial n
                   ((arctan_partial n (projT1 (real_plus x h) n))
                    - (arctan_partial n (projT1 x n))))) Mcv)).
Proof.
  intros x Hx h Hxh.
  set (v := real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (cauchy_real_arctan x Hx))).
  destruct (real_norm_bounded (cauchy_real_cos v)) as [Mcv [HMcv Hpt]].
  exists Mcv.
  split.
  - exact HMcv.
  - intro n.
    apply (Qle_trans (Qabs (cos_partial n
                             ((arctan_partial n (projT1 (real_plus x h) n))
                              - (arctan_partial n (projT1 x n)))))
                     (Qabs (projT1 (cauchy_real_cos v) n))
                     Mcv).
    + apply qeq_imp_qle. apply Qabs_wd.
      apply (Qeq_trans (cos_partial n
                          ((arctan_partial n (projT1 (real_plus x h) n))
                           - (arctan_partial n (projT1 x n))))
                       (cos_partial n (projT1 v n))
                       (projT1 (cauchy_real_cos v) n)).
      * apply (b5a_cos_partial_wd n
                 ((arctan_partial n (projT1 (real_plus x h) n))
                  - (arctan_partial n (projT1 x n)))
                 (projT1 v n)).
        unfold v.
        setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                       (real_opp (cauchy_real_arctan x Hx)) n).
        setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
        setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
        setoid_rewrite (arctan_real_proj x Hx n).
        ring.
      * apply Qeq_sym. exact (real_cos_proj v n).
    + apply QleT'_to_Qle. exact (Hpt n).
Qed.

(* |sin_partial n (v_n)| ≤ Msv 逐点（sin v 的 norm bound） *)
Lemma b5i_sinv_bounded : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
  sigT (fun Msv : Q => And (QltT 0 Msv)
    (forall n : nat,
      Qle (Qabs (sin_partial n
                   ((arctan_partial n (projT1 (real_plus x h) n))
                    - (arctan_partial n (projT1 x n))))) Msv)).
Proof.
  intros x Hx h Hxh.
  set (v := real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                      (real_opp (cauchy_real_arctan x Hx))).
  destruct (real_norm_bounded (cauchy_real_sin v)) as [Msv [HMsv Hpt]].
  exists Msv.
  split.
  - exact HMsv.
  - intro n.
    apply (Qle_trans (Qabs (sin_partial n
                             ((arctan_partial n (projT1 (real_plus x h) n))
                              - (arctan_partial n (projT1 x n)))))
                     (Qabs (projT1 (cauchy_real_sin v) n))
                     Msv).
    + apply qeq_imp_qle. apply Qabs_wd.
      apply (Qeq_trans (sin_partial n
                          ((arctan_partial n (projT1 (real_plus x h) n))
                           - (arctan_partial n (projT1 x n))))
                       (sin_partial n (projT1 v n))
                       (projT1 (cauchy_real_sin v) n)).
      * apply (b5a_sin_partial_wd n
                 ((arctan_partial n (projT1 (real_plus x h) n))
                  - (arctan_partial n (projT1 x n)))
                 (projT1 v n)).
        unfold v.
        setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                       (real_opp (cauchy_real_arctan x Hx)) n).
        setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
        setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
        setoid_rewrite (arctan_real_proj x Hx n).
        ring.
      * apply Qeq_sym. exact (real_sin_proj v n).
    + apply QleT'_to_Qle. exact (Hpt n).
Qed.

(* ============================================================ *)
(* Part I4：逐点表达式定义（主装配用，压缩语句）                *)
(* ============================================================ *)

(* A_n / Ah_n / v_n / d_n（逐点） *)
Definition b5i_An (x : Real) (n : nat) : Q :=
  arctan_partial n (projT1 x n).
Definition b5i_Ahn (x h : Real) (n : nat) : Q :=
  arctan_partial n (projT1 (real_plus x h) n).
Definition b5i_vn (x h : Real) (n : nat) : Q :=
  b5i_Ahn x h n - b5i_An x n.
Definition b5i_dn (x : Real) (n : nat) : Q :=
  projT1 (b5a_atan_d x) n.

(* rs_add_sin 的逐点误差列（sin_partial n (A+v) vs sA·cv + cA·sv；
   A_n + v_n == Ah_n 逐点 ⟹ 用 Ah_n 表示） *)
Definition b5i_addcol_sin (x h : Real) (Hxh : forall n : nat,
  QleT' (Qabs (projT1 (real_plus x h) n)) 1) (n : nat) : Q :=
  Qabs (sin_partial n (b5i_Ahn x h n)
        - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
           + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))).

(* S1_n / S2_n（D_n 的逐点两件） *)
Definition b5i_S1n (x h : Real) (n : nat) : Q :=
  sin_partial n (b5i_Ahn x h n) - sin_partial n (b5i_An x n)
  - cos_partial n (b5i_An x n) * b5i_vn x h n.
Definition b5i_S2n (x h : Real) (n : nat) : Q :=
  cos_partial n (b5i_An x n)
  * (b5i_vn x h n - b5i_dn x n * projT1 h n).

(* ============================================================ *)
(* ============================================================ *)
(* Part I5：S1 二次界 / S1 全局界 / S2 界（主装配内件，已 Qed）*)
(* ============================================================ *)

(* S1 二次界（|v_n| ≤ 1；c := rs_add 列误差上界） *)
Lemma b5i_S1_quad : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc c : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  Qle (Qabs (b5i_vn x h n)) 1 ->
  QltT (b5i_addcol_sin x h Hxh n) c ->
  Qle (Qabs (b5i_S1n x h n))
      (Qplus c (Qplus (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))
                      (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3)))).
Proof.
  intros x Hx h Hxh n Ms Mc c HMs HMc Hv1 Hcol.
  assert (Halg : b5i_S1n x h n ==
                 Qplus (sin_partial n (b5i_Ahn x h n)
                        - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                           + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))
                       (Qplus (sin_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1))
                              (cos_partial n (b5i_An x n) * (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))).
  { unfold b5i_S1n, b5i_vn. ring. }
  rewrite Halg.
  set (A := sin_partial n (b5i_Ahn x h n)
            - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
               + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))).
  set (B := sin_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1)).
  set (C := cos_partial n (b5i_An x n) * (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
  assert (Ht1 : Qle (Qabs (Qplus A (Qplus B C)))
                    (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))).
  { apply (Qle_trans _ (Qplus (Qabs A) (Qabs (Qplus B C))) _).
    - apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qabs_triangle. }
  assert (HA : Qle (Qabs A) c).
  { apply Qlt_le_weak. apply QltT_to_Qlt.
    apply (qltT_eq_compat_l (b5i_addcol_sin x h Hxh n) (Qabs A) c).
    - unfold A, b5i_addcol_sin, b5i_vn. reflexivity.
    - exact Hcol. }
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HMc0 : Qle 0 Mc).
  { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
    - apply Qabs_nonneg.
    - exact HMc. }
  assert (HB : Qle (Qabs B) (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))).
  { apply (Qle_trans (Qabs B)
                     (Qmult (Qabs (sin_partial n (b5i_An x n)))
                            (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                     (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))).
    - unfold B.
      apply qeq_imp_qle. apply (Qabs_Qmult (sin_partial n (b5i_An x n))
                                           (cos_partial n (b5i_vn x h n) - 1)).
    - apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Ms (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))).
      + apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_An x n))) Ms
                                 (Qabs (cos_partial n (b5i_vn x h n) - 1))).
        * exact HMs.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Ms (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                         (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Ms)
                         (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))).
        * apply qeq_imp_qle. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Ms)
                           (Qmult (q_pow (Qabs (b5i_vn x h n)) 2) Ms)
                           (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))).
          -- apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                      (q_pow (Qabs (b5i_vn x h n)) 2) Ms).
             ++ apply (sc_cos_sq_bound_c1 n (b5i_vn x h n)). exact Hv1.
             ++ exact HMs0.
          -- apply qeq_imp_qle. apply Qmult_comm. }
  assert (HC : Qle (Qabs C) (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))).
  { apply (Qle_trans (Qabs C)
                     (Qmult (Qabs (cos_partial n (b5i_An x n)))
                            (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                     (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))).
    - unfold C.
      apply qeq_imp_qle. apply (Qabs_Qmult (cos_partial n (b5i_An x n))
                                           (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
    - apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Mc (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))).
      + apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_An x n))) Mc
                                 (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
        * exact HMc.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Mc (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                         (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Mc)
                         (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))).
        * apply qeq_imp_qle. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Mc)
                           (Qmult (q_pow (Qabs (b5i_vn x h n)) 3) Mc)
                           (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))).
          -- apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                      (q_pow (Qabs (b5i_vn x h n)) 3) Mc).
             ++ apply (sc_sin_cube_bound_c1 n (b5i_vn x h n)). exact Hv1.
             ++ exact HMc0.
          -- apply qeq_imp_qle. apply Qmult_comm. }
  apply (Qle_trans (Qabs (Qplus A (Qplus B C)))
                   (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))
                   (Qplus c (Qplus (Qmult Ms (q_pow (Qabs (b5i_vn x h n)) 2))
                                   (Qmult Mc (q_pow (Qabs (b5i_vn x h n)) 3))))).
  - exact Ht1.
  - apply Qplus_le_compat.
    + exact HA.
    + apply Qplus_le_compat.
      * exact HB.
      * exact HC.
Qed.

(* S1 全局界（无需 |v| ≤ 1）：|S1| ≤ |addcol| + Ms(Mcv+1) + Mc(Msv+|v|) *)
Lemma b5i_S1_crude : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc Mcv Msv : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  Qle (Qabs (cos_partial n (b5i_vn x h n))) Mcv ->
  Qle (Qabs (sin_partial n (b5i_vn x h n))) Msv ->
  Qle (Qabs (b5i_S1n x h n))
      (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                    - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                       + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
             (Qplus (Qmult Ms (Qplus Mcv 1))
                    (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n)))))).
Proof.
  intros x Hx h Hxh n Ms Mc Mcv Msv HMs HMc HMcv HMsv.
  assert (Halg : b5i_S1n x h n ==
                 Qplus (sin_partial n (b5i_Ahn x h n)
                        - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                           + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n)))
                       (Qplus (sin_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1))
                              (cos_partial n (b5i_An x n) * (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))).
  { unfold b5i_S1n, b5i_vn. ring. }
  rewrite Halg.
  set (A := sin_partial n (b5i_Ahn x h n)
            - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
               + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))).
  set (B := sin_partial n (b5i_An x n) * (cos_partial n (b5i_vn x h n) - 1)).
  set (C := cos_partial n (b5i_An x n) * (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
  assert (Ht1 : Qle (Qabs (Qplus A (Qplus B C)))
                    (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))).
  { apply (Qle_trans _ (Qplus (Qabs A) (Qabs (Qplus B C))) _).
    - apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply Qabs_triangle. }
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HB : Qle (Qabs B) (Qmult Ms (Qplus Mcv 1))).
  { apply (Qle_trans (Qabs B)
                     (Qmult (Qabs (sin_partial n (b5i_An x n)))
                            (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                     (Qmult Ms (Qplus Mcv 1))).
    - unfold B.
      apply qeq_imp_qle. apply (Qabs_Qmult (sin_partial n (b5i_An x n))
                                           (cos_partial n (b5i_vn x h n) - 1)).
    - apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_An x n)))
                              (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Ms (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                       (Qmult Ms (Qplus Mcv 1))).
      + apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_An x n))) Ms
                                 (Qabs (cos_partial n (b5i_vn x h n) - 1))).
        * exact HMs.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Ms (Qabs (cos_partial n (b5i_vn x h n) - 1)))
                         (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Ms)
                         (Qmult Ms (Qplus Mcv 1))).
        * apply qeq_imp_qle. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_vn x h n) - 1)) Ms)
                           (Qmult (Qplus Mcv 1) Ms)
                           (Qmult Ms (Qplus Mcv 1))).
          -- apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                      (Qplus Mcv 1) Ms).
             ++ apply (Qle_trans (Qabs (cos_partial n (b5i_vn x h n) - 1))
                                 (Qplus (Qabs (cos_partial n (b5i_vn x h n))) 1)
                                 (Qplus Mcv 1)).
                ** apply (Qle_trans (Qabs (cos_partial n (b5i_vn x h n) + - 1))
                                    (Qplus (Qabs (cos_partial n (b5i_vn x h n))) (Qabs (- 1)))
                                    (Qplus (Qabs (cos_partial n (b5i_vn x h n))) 1)).
                   --- unfold Qminus. apply Qabs_triangle.
                   --- apply Qplus_le_compat.
                       ++++ apply Qle_refl.
                       ++++ unfold Qabs, Qle. simpl. lia.
                ** apply Qplus_le_compat.
                   --- exact HMcv.
                   --- apply Qle_refl.
             ++ apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
                ** apply Qabs_nonneg.
                ** exact HMs.
          -- apply qeq_imp_qle. apply Qmult_comm. }
  assert (HC : Qle (Qabs C) (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))).
  { apply (Qle_trans (Qabs C)
                     (Qmult (Qabs (cos_partial n (b5i_An x n)))
                            (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                     (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))).
    - unfold C.
      apply qeq_imp_qle. apply (Qabs_Qmult (cos_partial n (b5i_An x n))
                                           (sin_partial n (b5i_vn x h n) - b5i_vn x h n)).
    - apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_An x n)))
                              (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Mc (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                       (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))).
      + apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_An x n))) Mc
                                 (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))).
        * exact HMc.
        * apply Qabs_nonneg.
      + apply (Qle_trans (Qmult Mc (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)))
                         (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Mc)
                         (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))).
        * apply qeq_imp_qle. apply Qmult_comm.
        * apply (Qle_trans (Qmult (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n)) Mc)
                           (Qmult (Qplus Msv (Qabs (b5i_vn x h n))) Mc)
                           (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))).
          -- apply (Qmult_le_compat_r (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                      (Qplus Msv (Qabs (b5i_vn x h n))) Mc).
             ++ apply (Qle_trans (Qabs (sin_partial n (b5i_vn x h n) - b5i_vn x h n))
                                 (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                        (Qabs (b5i_vn x h n)))
                                 (Qplus Msv (Qabs (b5i_vn x h n)))).
                ** apply (Qle_trans (Qabs (sin_partial n (b5i_vn x h n) + - b5i_vn x h n))
                                    (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                           (Qabs (- b5i_vn x h n)))
                                    (Qplus (Qabs (sin_partial n (b5i_vn x h n)))
                                           (Qabs (b5i_vn x h n)))).
                   --- unfold Qminus. apply Qabs_triangle.
                   --- apply Qplus_le_compat.
                       ++++ apply Qle_refl.
                       ++++ apply qeq_imp_qle. apply Qabs_opp.
                ** apply Qplus_le_compat.
                   --- exact HMsv.
                   --- apply Qle_refl.
             ++ apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
                ** apply Qabs_nonneg.
                ** exact HMc.
          -- apply qeq_imp_qle. apply Qmult_comm. }
  apply (Qle_trans (Qabs (Qplus A (Qplus B C)))
                   (Qplus (Qabs A) (Qplus (Qabs B) (Qabs C)))
                   (Qplus (Qabs A)
                          (Qplus (Qmult Ms (Qplus Mcv 1))
                                 (Qmult Mc (Qplus Msv (Qabs (b5i_vn x h n))))))).
  - exact Ht1.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qplus_le_compat.
      * exact HB.
      * exact HC.
Qed.

(* S2 界：|cA·(v−dh)| ≤ Mc·wb（|v−dh|_n ≤ wb） *)
Lemma b5i_S2_le : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Mc wb : Q),
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  Qle (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) wb ->
  Qle (Qabs (b5i_S2n x h n)) (Qmult Mc wb).
Proof.
  intros x Hx h Hxh n Mc wb HMc Hwb.
  unfold b5i_S2n.
  apply (Qle_trans (Qabs (cos_partial n (b5i_An x n)
                          * (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                   (Qmult (Qabs (cos_partial n (b5i_An x n)))
                          (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                   (Qmult Mc wb)).
  - apply qeq_imp_qle.
    apply (Qabs_Qmult (cos_partial n (b5i_An x n))
                      (b5i_vn x h n - b5i_dn x n * projT1 h n)).
  - assert (HMc0 : Qle 0 Mc).
    { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
      - apply Qabs_nonneg.
      - exact HMc. }
    apply (Qle_trans (Qmult (Qabs (cos_partial n (b5i_An x n)))
                              (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                       (Qmult Mc (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                       (Qmult Mc wb)).
    + apply (Qmult_le_compat_r (Qabs (cos_partial n (b5i_An x n))) Mc
                               (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n))).
      * exact HMc.
      * apply Qabs_nonneg.
    + apply (Qle_trans (Qmult Mc (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)))
                       (Qmult (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) Mc)
                       (Qmult Mc wb)).
      * apply qeq_imp_qle. apply Qmult_comm.
      * apply (Qle_trans (Qmult (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) Mc)
                         (Qmult wb Mc)
                         (Qmult Mc wb)).
        -- apply (Qmult_le_compat_r (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n))
                                    wb Mc).
           ++ exact Hwb.
           ++ exact HMc0.
        -- apply qeq_imp_qle. apply Qmult_comm.
Qed.

(* ============================================================ *)
(* Part I6：E1 通用 exp 界（|sin/cos_partial m a| ≤ C(|a| ≤ 4)）*)
(* ============================================================ *)

(* 0 ≤ |a| ≤ 4 ⟹ |cos_partial m a| ≤ 4·C + 1（C := ∀j exp_series j 4 ≤ C） *)
Lemma b5i_cos_partial_le4 : forall (C : Q),
  (forall j : nat, QleT' (exp_series j 4) C) ->
  Qle 0 C ->
  forall (m : nat) (a : Q), Qle (Qabs a) 4 ->
  Qle (Qabs (cos_partial m a)) (Qplus (Qmult 4 C) 1).
Proof.
  intros C HC HC0 m a Ha.
  assert (HaT : QleT' (Qabs a) 4) by (apply Qle_to_QleT'; exact Ha).
  apply (Qle_trans (Qabs (cos_partial m a))
                   (Qplus (Qabs (cos_partial m a - cos_partial m 0))
                          (Qabs (cos_partial m 0)))
                   (Qplus (Qmult 4 C) 1)).
  - apply (Qle_trans (Qabs (cos_partial m a))
                     (Qabs ((cos_partial m a - cos_partial m 0) + cos_partial m 0))
                     (Qplus (Qabs (cos_partial m a - cos_partial m 0))
                            (Qabs (cos_partial m 0)))).
    + apply qeq_imp_qle. apply Qabs_wd. ring.
    + apply Qabs_triangle.
  - apply Qplus_le_compat.
    + apply (Qle_trans (Qabs (cos_partial m a - cos_partial m 0))
                       (Qmult (Qabs (a - 0)) C)
                       (Qmult 4 C)).
      * apply (b5b_cos_family_lip a 0 4 C m).
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- exact HaT.
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
        -- exact HC0.
        -- exact HC.
      * apply (Qmult_le_compat_r (Qabs (a - 0)) 4 C).
        -- apply (Qle_trans (Qabs (a - 0)) (Qabs a) 4).
           ++ apply qeq_imp_qle. apply Qabs_wd. ring.
           ++ exact Ha.
        -- exact HC0.
    + apply (Qle_trans (Qabs (cos_partial m 0)) 1 1).
      * apply qeq_imp_qle.
        transitivity (Qabs 1).
        -- apply Qabs_wd. apply (sc_cos_partial_one m).
        -- apply (Qabs_pos 1). unfold Qle. simpl. lia.
      * apply Qle_refl.
Qed.

(* 0 ≤ |a| ≤ 4 ⟹ |sin_partial m a| ≤ 4·C（C := ∀j exp_series j 4 ≤ C） *)
Lemma b5i_sin_partial_le4 : forall (C : Q),
  (forall j : nat, QleT' (exp_series j 4) C) ->
  Qle 0 C ->
  forall (m : nat) (a : Q), Qle (Qabs a) 4 ->
  Qle (Qabs (sin_partial m a)) (Qmult 4 C).
Proof.
  intros C HC HC0 m a Ha.
  assert (HaT : QleT' (Qabs a) 4) by (apply Qle_to_QleT'; exact Ha).
  apply (Qle_trans (Qabs (sin_partial m a))
                   (Qplus (Qabs (sin_partial m a - sin_partial m 0))
                          (Qabs (sin_partial m 0)))
                   (Qmult 4 C)).
  - apply (Qle_trans (Qabs (sin_partial m a))
                     (Qabs ((sin_partial m a - sin_partial m 0) + sin_partial m 0))
                     (Qplus (Qabs (sin_partial m a - sin_partial m 0))
                            (Qabs (sin_partial m 0)))).
    + apply qeq_imp_qle. apply Qabs_wd. ring.
    + apply Qabs_triangle.
  - apply (Qle_trans (Qplus (Qabs (sin_partial m a - sin_partial m 0))
                            (Qabs (sin_partial m 0)))
                     (Qplus (Qmult (Qabs (a - 0)) C) 0)
                     (Qmult 4 C)).
    + apply Qplus_le_compat.
      * apply (Qle_trans (Qabs (sin_partial m a - sin_partial m 0))
                         (Qmult (Qabs (a - 0)) C)
                         (Qmult (Qabs (a - 0)) C)).
        -- apply (b5b_sin_family_lip a 0 4 C m).
           ++ apply Qle_to_QleT'. unfold Qle. simpl. lia.
           ++ exact HaT.
           ++ apply Qle_to_QleT'. unfold Qle. simpl. lia.
           ++ exact HC.
        -- apply Qle_refl.
      * apply (Qle_trans (Qabs (sin_partial m 0)) 0 0).
        -- apply qeq_imp_qle.
           rewrite (sc_sin_partial_zero m).
           apply (Qabs_pos 0). apply Qle_refl.
        -- apply Qle_refl.
    + apply (Qle_trans (Qplus (Qmult (Qabs (a - 0)) C) 0)
                       (Qmult (Qabs (a - 0)) C)
                       (Qmult 4 C)).
      * apply qeq_imp_qle. ring.
      * apply (Qle_trans (Qmult (Qabs (a - 0)) C)
                         (Qmult 4 C)
                         (Qmult 4 C)).
        -- apply (Qmult_le_compat_r (Qabs (a - 0)) 4 C).
           ++ apply (Qle_trans (Qabs (a - 0)) (Qabs a) 4).
              ** apply qeq_imp_qle. apply Qabs_wd. ring.
              ** exact Ha.
           ++ exact HC0.
        -- apply Qle_refl.
Qed.

(* 通用界实例化：∃C4 ≥ 1：∀j exp_series j 4 ≤ C4（exp_series_arch 直接） *)
Lemma b5i_exp_arch4 : sigT (fun C : Q => And (QleT' 1 C)
  (forall j : nat, QleT' (exp_series j 4) C)).
Proof.
  apply (exp_series_arch 4).
  apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* S1 x-无关全局界：|S1| ≤ |addcol| + Ms(4C+2) + Mc(4C+4)（|v| ≤ 4、C 通用 exp 界） *)
Lemma b5i_S1_crude_x : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc C : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C) ->
  Qle 0 C ->
  Qle (Qabs (b5i_vn x h n)) 4 ->
  Qle (Qabs (b5i_S1n x h n))
      (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                    - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                       + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
             (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                    (Qmult Mc (Qplus (Qmult 4 C) 4)))).
Proof.
  intros x Hx h Hxh n Ms Mc C HMs HMc HC HC0 Hv4.
  apply (Qle_trans (Qabs (b5i_S1n x h n))
                   (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                                 - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                    + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
                          (Qplus (Qmult Ms (Qplus (Qplus (Qmult 4 C) 1) 1))
                                 (Qmult Mc (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))))))
                   (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                                 - (sin_partial n (b5i_An x n) * cos_partial n (b5i_vn x h n)
                                    + cos_partial n (b5i_An x n) * sin_partial n (b5i_vn x h n))))
                          (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                 (Qmult Mc (Qplus (Qmult 4 C) 4))))).
  - apply (b5i_S1_crude x Hx h Hxh n Ms Mc (Qplus (Qmult 4 C) 1) (Qmult 4 C)).
    + exact HMs.
    + exact HMc.
    + exact (b5i_cos_partial_le4 C HC HC0 n (b5i_vn x h n) Hv4).
    + exact (b5i_sin_partial_le4 C HC HC0 n (b5i_vn x h n) Hv4).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qplus_le_compat.
      * apply qeq_imp_qle. ring.
      * apply (Qle_trans (Qmult Mc (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))))
                         (Qmult (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))) Mc)
                         (Qmult Mc (Qplus (Qmult 4 C) 4))).
        -- apply qeq_imp_qle. apply Qmult_comm.
        -- apply (Qle_trans (Qmult (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n))) Mc)
                           (Qmult (Qplus (Qmult 4 C) 4) Mc)
                           (Qmult Mc (Qplus (Qmult 4 C) 4))).
           ++ apply (Qmult_le_compat_r (Qplus (Qmult 4 C) (Qabs (b5i_vn x h n)))
                                       (Qplus (Qmult 4 C) 4) Mc).
              ** apply Qplus_le_compat.
                 --- apply Qle_refl.
                 --- exact Hv4.
              ** apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
                 --- apply Qabs_nonneg.
                 --- exact HMc.
           ++ apply qeq_imp_qle. apply Qmult_comm.
Qed.

(* ============================================================ *)
(* ============================================================ *)
(* Part I7：逐点提取（E4 模板；主装配可独立引用）               *)
(* ============================================================ *)

(* |h| < eps·k（Real 积，k > 0）⟹ ∃N ∀n≥N：|h_n| ≤ en·k        *)
Lemma b5i_h_le_enk : forall (h : Real) (eps : Real) (k : Q),
  real_lt (real_abs h) (real_mult eps (real_const k)) ->
  QltT 0 k ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    Qle (Qabs (projT1 h n)) (Qmult (projT1 eps n) k)).
Proof.
  intros h eps k Hh Hk.
  destruct Hh as [eps2 [Heps2 [N2 HN2]]].
  exists N2.
  intros n Hn.
  apply Qlt_le_weak.
  apply (Qlt_le_trans (Qabs (projT1 h n))
                      (Qminus (Qmult (projT1 eps n) k) eps2)
                      (Qmult (projT1 eps n) k)).
  - apply (q_lt_minus_shift eps2 (Qmult (projT1 eps n) k) (Qabs (projT1 h n))).
    apply QltT_to_Qlt.
    apply (qltT_eq_compat_r (Qmult (projT1 eps n) k - Qabs (projT1 h n))
                            (projT1 (real_mult eps (real_const k)) n
                                     - projT1 (real_abs h) n)
                            eps2).
    + rewrite (real_mult_proj eps (real_const k) n).
      rewrite (real_const_proj k n).
      rewrite (real_abs_proj h n).
      reflexivity.
    + exact (HN2 n Hn).
  - apply (proj2 (Qle_minus_iff (Qminus (Qmult (projT1 eps n) k) eps2)
                                (Qmult (projT1 eps n) k))).
    apply (Qle_trans _ eps2 _).
    + apply (Qlt_le_weak 0 eps2). apply QltT_to_Qlt. exact Heps2.
    + apply qeq_imp_qle. ring.
Qed.

(* |h| < real-const c ⟹ ∃N ∀n≥N：|h_n| ≤ c（c > 0） *)
Lemma b5i_h_le_const : forall (h : Real) (c : Q),
  real_lt (real_abs h) (real_const c) ->
  QltT 0 c ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    Qle (Qabs (projT1 h n)) c).
Proof.
  intros h c Hh Hc.
  destruct Hh as [eps2 [Heps2 [N2 HN2]]].
  exists N2.
  intros n Hn.
  apply Qlt_le_weak.
  apply (Qlt_le_trans (Qabs (projT1 h n))
                      (Qminus c eps2)
                      c).
  - apply (q_lt_minus_shift eps2 c (Qabs (projT1 h n))).
    apply QltT_to_Qlt.
    apply (qltT_eq_compat_r (Qminus c (Qabs (projT1 h n)))
                            (Qminus (projT1 (real_const c) n)
                                    (projT1 (real_abs h) n))
                            eps2).
    + rewrite (real_const_proj c n).
      rewrite (real_abs_proj h n).
      reflexivity.
    + exact (HN2 n Hn).
  - apply (proj2 (Qle_minus_iff (Qminus c eps2) c)).
    apply (Qle_trans _ eps2 _).
    + apply (Qlt_le_weak 0 eps2). apply QltT_to_Qlt. exact Heps2.
    + apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* ============================================================ *)
(* Part I8：real_le → 逐点桥（主装配 |v−dh| 提取的 lt/eq 双分支）*)
(* ============================================================ *)

(* real_le (real_abs A) B ⟹ ∃N ∀n≥N：|A_n| ≤ B_n + sh_n（sh > 0 松弛） *)
Lemma b5i_abs_le_pointwise : forall (A B : Real),
  real_le (real_abs A) B ->
  forall (sh : Real), real_lt real_zero sh ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    Qle (Qabs (projT1 A n)) (Qplus (projT1 B n) (projT1 sh n))).
Proof.
  intros A B Hle sh Hsh.
  destruct Hsh as [sh0 [Hsh0 [Nsh HNsh]]].
  destruct Hle as [Hlt | Heq].
  - (* lt 分支 *)
    destruct Hlt as [eps0w [Heps0w [Nw HNw]]].
    exists (Nat.max Nw Nsh).
    intros n Hn.
    apply NatLe_drop in Hn.
    apply (Qle_trans (Qabs (projT1 A n))
                     (projT1 B n)
                     (Qplus (projT1 B n) (projT1 sh n))).
    + apply (Qle_trans (Qabs (projT1 A n))
                       (Qminus (projT1 B n) eps0w)
                       (projT1 B n)).
      * apply Qlt_le_weak.
        apply (q_lt_minus_shift eps0w (projT1 B n) (Qabs (projT1 A n))).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (Qminus (projT1 B n) (Qabs (projT1 A n)))
                                (Qminus (projT1 B n) (projT1 (real_abs A) n))
                                eps0w).
        -- rewrite (real_abs_proj A n). reflexivity.
        -- exact (HNw n (NatLe_lift _ _ (Nat.le_trans _ _ _ (Nat.le_max_l Nw Nsh) Hn))).
      * apply (proj2 (Qle_minus_iff (Qminus (projT1 B n) eps0w) (projT1 B n))).
        apply (Qle_trans _ eps0w _).
        -- apply (Qlt_le_weak 0 eps0w). apply QltT_to_Qlt. exact Heps0w.
        -- apply qeq_imp_qle. ring.
    + apply Qle_plus_nonneg_r.
      apply (Qle_trans 0 sh0 (projT1 sh n)).
      * apply (Qlt_le_weak 0 sh0). apply QltT_to_Qlt. exact Hsh0.
      * apply Qlt_le_weak. apply QltT_to_Qlt.
        apply (qltT_eq_compat_r (projT1 sh n)
                                (Qminus (projT1 sh n) (projT1 real_zero n))
                                sh0).
        -- cbn [projT1 real_zero]. ring.
        -- exact (HNsh n (NatLe_lift _ _ (Nat.le_trans _ _ _ (Nat.le_max_r Nw Nsh) Hn))).
  - (* eq 分支：在 sh0/2 处 destruct ⟹ |A_n| ≤ B_n + sh0/2 ≤ B_n + sh_n *)
    set (e := Qmult sh0 (Qinv 2)).
    assert (He : QltT 0 e).
    { unfold e. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat sh0 (Qinv 2)).
      - apply QltT_to_Qlt. exact Hsh0.
      - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
    destruct (Heq e He) as [Ne HNe].
    exists (Nat.max Ne Nsh).
    intros n Hn.
    apply NatLe_drop in Hn.
    apply (Qle_trans (Qabs (projT1 A n))
                     (Qplus (projT1 B n) e)
                     (Qplus (projT1 B n) (projT1 sh n))).
    + apply (Qle_trans (Qabs (projT1 A n))
                       (Qplus (projT1 B n)
                              (Qminus (projT1 (real_abs A) n) (projT1 B n)))
                       (Qplus (projT1 B n) e)).
      * apply qeq_imp_qle.
        rewrite (real_abs_proj A n). ring.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qle_trans (Qminus (projT1 (real_abs A) n) (projT1 B n))
                            (Qabs (Qminus (projT1 (real_abs A) n) (projT1 B n)))
                            e).
           ++ apply Qle_Qabs.
           ++ apply Qlt_le_weak. apply QltT_to_Qlt.
              exact (HNe n (NatLe_lift _ _ (Nat.le_trans _ _ _ (Nat.le_max_l Ne Nsh) Hn))).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (Qle_trans e sh0 (projT1 sh n)).
        -- apply (Qle_trans e (Qmult (Qinv 2) sh0) sh0).
           ++ apply qeq_imp_qle. unfold e. ring.
           ++ apply (Qle_trans (Qmult (Qinv 2) sh0) (Qmult 1 sh0) sh0).
              ** apply (Qmult_le_compat_r (Qinv 2) 1 sh0).
                 --- unfold Qle. simpl. lia.
                 --- apply (Qlt_le_weak 0 sh0). apply QltT_to_Qlt. exact Hsh0.
              ** apply qeq_imp_qle. ring.
        -- apply Qlt_le_weak. apply QltT_to_Qlt.
           apply (qltT_eq_compat_r (projT1 sh n)
                                   (Qminus (projT1 sh n) (projT1 real_zero n))
                                   sh0).
           ++ cbn [projT1 real_zero]. ring.
           ++ exact (HNsh n (NatLe_lift _ _ (Nat.le_trans _ _ _ (Nat.le_max_r Ne Nsh) Hn))).
Qed.

(* ============================================================ *)
(* Part I9：|v−dh| 逐点界（段②：投影恒等 + 提取包装）          *)
(* ============================================================ *)

(* proj ((arctan(x+h) − arctan x) − d·h) n == (Ah_n − A_n) − d_n·h_n *)
Lemma b5i_vdh_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (real_plus (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                               (real_opp (cauchy_real_arctan x Hx)))
                    (real_opp (real_mult (b5a_atan_d x) h))) n ==
  (b5i_Ahn x h n - b5i_An x n) - b5i_dn x n * projT1 h n.
Proof.
  intros x Hx h Hxh n.
  setoid_rewrite (real_plus_proj (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                            (real_opp (cauchy_real_arctan x Hx)))
                                 (real_opp (real_mult (b5a_atan_d x) h)) n).
  setoid_rewrite (real_opp_proj (real_mult (b5a_atan_d x) h) n).
  setoid_rewrite (real_mult_proj (b5a_atan_d x) h n).
  setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                 (real_opp (cauchy_real_arctan x Hx)) n).
  setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
  setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
  setoid_rewrite (arctan_real_proj x Hx n).
  unfold b5i_Ahn, b5i_An, b5i_dn.
  ring.
Qed.

(* |proj ((v − dh)) n| ≤ wb ⟹ |(v_n − d_n h_n)| ≤ wb（b5i 形态） *)
Lemma b5i_vdh_abs : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (wb : Q),
  Qle (Qabs (projT1 (real_plus (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                          (real_opp (cauchy_real_arctan x Hx)))
                               (real_opp (real_mult (b5a_atan_d x) h))) n)) wb ->
  Qle (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n)) wb.
Proof.
  intros x Hx h Hxh n wb H.
  apply (Qle_trans (Qabs (b5i_vn x h n - b5i_dn x n * projT1 h n))
                   (Qabs (projT1 (real_plus (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                       (real_opp (cauchy_real_arctan x Hx)))
                                            (real_opp (real_mult (b5a_atan_d x) h))) n))
                   wb).
  - apply qeq_imp_qle. apply Qabs_wd.
    unfold b5i_vn.
    apply Qeq_sym. exact (b5i_vdh_proj x Hx h Hxh n).
  - exact H.
Qed.

(* ============================================================ *)
(* Part J1：主装配 Q 系数工具 + Real 提取件（增量 1，纯 Q/Real） *)
(* （预算符号化：kδ/k2/k2' 的数值界统一由 b5i_kbig 单一件给出；  *)
(*   常数一律用规范 Qmake 形态（1#4）等，避免 Qdiv 的 ring 陷阱） *)
(* ============================================================ *)

(* ≤/≥ 可判定二分（|v_n| ≤ 1 双分支的 case-split 用） *)
Lemma b5i_qle_dec : forall (x y : Q), {Qle x y} + {Qlt y x}.
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - left. apply qeq_imp_qle. apply Qeq_alt. exact E.
  - left. apply Qlt_le_weak. apply Qlt_alt. exact E.
  - right. apply (proj2 (Qgt_alt x y)). exact E.
Qed.

(* |a·b| ≤ |a|·|b| *)
Lemma b5i_abs_prod_le : forall (a b : Q),
  Qle (Qabs (Qmult a b)) (Qmult (Qabs a) (Qabs b)).
Proof.
  intros a b. apply qeq_imp_qle. exact (Qabs_Qmult a b).
Qed.

(* |d| ≤ 1 ⟹ |d·h| ≤ |h|（逐点 dh 吸收） *)
Lemma b5i_dh_abs_le_h : forall (d h : Q), Qle (Qabs d) 1 ->
  Qle (Qabs (Qmult d h)) (Qabs h).
Proof.
  intros d h Hd.
  apply (Qle_trans (Qabs (Qmult d h)) (Qmult (Qabs d) (Qabs h)) (Qabs h)).
  - exact (b5i_abs_prod_le d h).
  - apply (Qle_trans (Qmult (Qabs d) (Qabs h)) (Qmult 1 (Qabs h)) (Qabs h)).
    + apply (Qmult_le_compat_r (Qabs d) 1 (Qabs h) Hd (Qabs_nonneg h)).
    + apply qeq_le. ring.
Qed.

(* (a+b)² ≤ 2a² + 2b²（纯代数，无需非负假设） *)
Lemma b5i_sq_sum2 : forall (a b : Q),
  Qle (q_pow (Qplus a b) 2)
      (Qplus (Qmult 2 (q_pow a 2)) (Qmult 2 (q_pow b 2))).
Proof.
  intros a b.
  rewrite (sc_qpow2_form (Qplus a b)).
  rewrite (sc_qpow2_form a). rewrite (sc_qpow2_form b).
  apply (proj2 (Qle_minus_iff (Qmult (Qplus a b) (Qplus a b))
                              (Qplus (Qmult 2 (Qmult a a)) (Qmult 2 (Qmult b b))))).
  assert (Heq : Qminus (Qplus (Qmult 2 (Qmult a a)) (Qmult 2 (Qmult b b)))
                        (Qmult (Qplus a b) (Qplus a b)) ==
                Qmult (Qminus a b) (Qminus a b)) by ring.
  rewrite Heq.
  apply Qsquare_nonneg.
Qed.

(* 0 ≤ x ≤ y ⟹ x² ≤ y² *)
Lemma b5i_sq_mono : forall (x y : Q), Qle 0 x -> Qle x y ->
  Qle (q_pow x 2) (q_pow y 2).
Proof.
  intros x y Hx0 Hxy.
  rewrite (sc_qpow2_form x). rewrite (sc_qpow2_form y).
  apply (Qmult_le_compat_nonneg x y x y).
  - split; [exact Hx0 | exact Hxy].
  - split; [exact Hx0 | exact Hxy].
Qed.

(* |v| ≤ |w| + |h| ⟹ |v|² ≤ 2|w|² + 2|h|² *)
Lemma b5i_vsq_bound : forall (v w h : Q),
  Qle (Qabs v) (Qplus (Qabs w) (Qabs h)) ->
  Qle (q_pow (Qabs v) 2)
      (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs h) 2))).
Proof.
  intros v w h Hv.
  apply (Qle_trans (q_pow (Qabs v) 2) (q_pow (Qplus (Qabs w) (Qabs h)) 2)
                   (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs h) 2)))).
  - apply (b5i_sq_mono (Qabs v) (Qplus (Qabs w) (Qabs h)) (Qabs_nonneg v) Hv).
  - apply (b5i_sq_sum2 (Qabs w) (Qabs h)).
Qed.

(* 0 ≤ u ≤ a 且 u ≤ b ⟹ u² ≤ a·b（B1·B2 乘积技巧） *)
Lemma b5i_sq_le_prod : forall (u a b : Q), Qle 0 u -> Qle u a -> Qle u b ->
  Qle (q_pow u 2) (Qmult a b).
Proof.
  intros u a b Hu0 Hua Hub.
  rewrite (sc_qpow2_form u).
  apply (Qmult_le_compat_nonneg u a u b).
  - split; [exact Hu0 | exact Hua].
  - split; [exact Hu0 | exact Hub].
Qed.

(* |x| ≤ 1 ⟹ |x|³ ≤ |x|²（二次界内 |v|³ 吸收） *)
Lemma b5i_cube_le_sq : forall (x : Q), Qle (Qabs x) 1 ->
  Qle (q_pow (Qabs x) 3) (q_pow (Qabs x) 2).
Proof.
  intros x Hx1.
  rewrite (sc_qpow3_form (Qabs x)). rewrite (sc_qpow2_form (Qabs x)).
  apply (Qle_trans (Qmult (Qmult (Qabs x) (Qabs x)) (Qabs x))
                   (Qmult (Qmult (Qabs x) (Qabs x)) 1)
                   (Qmult (Qabs x) (Qabs x))).
  - apply (Qmult_le_compat_nonneg (Qmult (Qabs x) (Qabs x)) (Qmult (Qabs x) (Qabs x))
                                  (Qabs x) 1).
    + split; [apply (Qmult_le_0_compat (Qabs x) (Qabs x) (Qabs_nonneg x) (Qabs_nonneg x)) | apply Qle_refl].
    + split; [exact (Qabs_nonneg x) | exact Hx1].
  - apply qeq_le. ring.
Qed.

(* |h| ≤ 1/2 ⟹ (1 + |h|) ≤ 3/2（B2 上界件） *)
Lemma b5i_one_plus_abs_le32 : forall (h : Q), Qle (Qabs h) (1 # 2) ->
  Qle (Qplus 1 (Qabs h)) (3 # 2).
Proof.
  intros h Hh.
  apply (Qle_trans (Qplus 1 (Qabs h)) (Qplus 1 (1 # 2)) (3 # 2)).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact Hh.
  - apply qeq_le. ring.
Qed.

(* 预算数值件：a·inv(c·(b+1)·(a+1)) ≤ 1/c
   （a > 0、c > 0、b ≥ 0；kδ/k2/k2' 所有系数界的单一来源） *)
Lemma b5i_kbig : forall (a b c : Q), Qlt 0 a -> Qlt 0 c -> Qle 0 b ->
  Qle (Qmult a (Qinv (Qmult c (Qmult (Qplus b 1) (Qplus a 1))))) (Qinv c).
Proof.
  intros a b c Ha Hc Hb.
  apply (Qle_trans (Qmult a (Qinv (Qmult c (Qmult (Qplus b 1) (Qplus a 1)))))
                   (Qdiv a (Qmult c (Qmult (Qplus b 1) (Qplus a 1))))
                   (Qinv c)).
  - apply qeq_le. unfold Qdiv. reflexivity.
  - apply (Qle_trans (Qdiv a (Qmult c (Qmult (Qplus b 1) (Qplus a 1))))
                     (Qdiv 1 c)
                     (Qinv c)).
    + apply (q_le_div_le a (Qmult c (Qmult (Qplus b 1) (Qplus a 1))) 1 c).
      * apply (Qmult_lt_0_compat c (Qmult (Qplus b 1) (Qplus a 1))).
        -- exact Hc.
        -- apply (Qmult_lt_0_compat (Qplus b 1) (Qplus a 1)).
           ++ apply (Qlt_le_trans 0 1 (Qplus b 1)).
              ** unfold Qlt. simpl. lia.
              ** apply (Qle_trans 1 (0 + 1) (Qplus b 1)).
                 *** apply qeq_le. ring.
                 *** apply Qplus_le_compat.
                     **** exact Hb.
                     **** apply Qle_refl.
           ++ apply (Qlt_le_trans 0 1 (Qplus a 1)).
              ** unfold Qlt. simpl. lia.
              ** apply (Qle_trans 1 (0 + 1) (Qplus a 1)).
                 *** apply qeq_le. ring.
                 *** apply Qplus_le_compat.
                     **** apply (Qlt_le_weak 0 a). exact Ha.
                     **** apply Qle_refl.
      * exact Hc.
      * (* a·c ≤ 1·(c(b+1)(a+1))：a ≤ (b+1)(a+1) 后乘 c *)
        assert (Hsub : Qle (Qmult a c) (Qmult c (Qmult (Qplus b 1) (Qplus a 1)))).
        { apply (Qle_trans (Qmult a c) (Qmult (Qmult (Qplus b 1) (Qplus a 1)) c)
                           (Qmult c (Qmult (Qplus b 1) (Qplus a 1)))).
          - apply (Qmult_le_compat_r a (Qmult (Qplus b 1) (Qplus a 1)) c).
            + apply (Qle_trans a (Qplus a 1) (Qmult (Qplus b 1) (Qplus a 1))).
              * apply (Qle_plus_nonneg_r a 1). unfold Qle. simpl. lia.
              * apply (Qle_trans (Qplus a 1) (Qmult 1 (Qplus a 1))
                                 (Qmult (Qplus b 1) (Qplus a 1))).
                -- apply qeq_le. ring.
                -- apply (Qmult_le_compat_r 1 (Qplus b 1) (Qplus a 1)).
                   ++ apply (Qle_trans 1 (0 + 1) (Qplus b 1)).
                      ** apply qeq_le. ring.
                      ** apply Qplus_le_compat.
                         *** exact Hb.
                         *** apply Qle_refl.
                   ++ apply (Qlt_le_weak 0 (Qplus a 1)).
                      apply (Qlt_le_trans 0 1 (Qplus a 1)).
                      ** unfold Qlt. simpl. lia.
                      ** apply (Qle_trans 1 (0 + 1) (Qplus a 1)).
                         *** apply qeq_le. ring.
                         *** apply Qplus_le_compat.
                             **** apply (Qlt_le_weak 0 a). exact Ha.
                             **** apply Qle_refl.
            + apply (Qlt_le_weak 0 c). exact Hc.
          - apply qeq_le. ring. }
        apply (Qle_trans (Qmult a c) (Qmult c (Qmult (Qplus b 1) (Qplus a 1)))
                         (Qmult 1 (Qmult c (Qmult (Qplus b 1) (Qplus a 1))))).
        -- exact Hsub.
        -- apply qeq_le. ring.
    + apply qeq_le. unfold Qdiv. ring.
Qed.

(* ============================================================ *)
(* Real 层提取件（主装配 δ 组装用）                              *)
(* ============================================================ *)

(* 1 + eps·const k2 > 0（k2 > 0；δ 的 inv-pos 部分正性见证） *)
Lemma b5i_one_plus_eps2_pos : forall (eps : Real) (k2 : Q),
  real_lt real_zero eps -> QltT 0 k2 ->
  real_lt real_zero (real_plus real_one (real_mult eps (real_const k2))).
Proof.
  intros eps k2 Heps Hk2.
  destruct Heps as [eps1 [Heps1 [N1 HN1]]].
  unfold real_lt.
  exists (1 # 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists N1.
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hen : Qlt 0 (projT1 eps n)).
    { apply (Qlt_le_trans 0 eps1 (projT1 eps n)).
      - apply QltT_to_Qlt. exact Heps1.
      - apply (Qle_trans eps1 (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
        + apply Qlt_le_weak. apply QltT_to_Qlt. exact (HN1 n Hn).
        + apply qeq_le. cbn [projT1 real_zero]. ring. }
    apply (Qlt_le_trans (1 # 2) 1
                        (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                                (projT1 real_zero n))).
    + unfold Qlt. simpl. lia.
    + apply (Qle_trans 1 (Qplus 1 (Qmult (projT1 eps n) k2))
                       (Qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                               (projT1 real_zero n))).
      * apply (Qle_trans 1 (Qplus 1 0) (Qplus 1 (Qmult (projT1 eps n) k2))).
        -- apply qeq_le. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (Qmult_le_0_compat (projT1 eps n) k2).
              ** apply (Qlt_le_weak 0 (projT1 eps n)). exact Hen.
              ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2.
      * apply qeq_le.
        setoid_rewrite (real_plus_proj real_one (real_mult eps (real_const k2)) n).
        setoid_rewrite (real_mult_proj eps (real_const k2) n).
        rewrite (real_const_proj k2 n).
        cbn [projT1 real_one projT1 real_zero].
        ring.
Qed.

(* |h| < (1/4)·inv_pos(1+eps2) ⟹ ∃N ∀n≥N：(1+eps2_n)·|h_n| ≤ 1/4
   （δ 组装第 (d) 部分；real_inv_proj 尾表示 + q_lt_minus_shift） *)
Lemma b5i_h_inv_quarter : forall (h eps2 : Real)
  (Hp : real_lt real_zero (real_plus real_one eps2)),
  real_lt (real_abs h)
          (real_mult (real_const (1 # 4)) (real_inv_pos (real_plus real_one eps2) Hp)) ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    Qle (Qmult (projT1 (real_plus real_one eps2) n) (Qabs (projT1 h n))) (1 # 4)).
Proof.
  intros h eps2 Hp Hh.
  destruct Hh as [e [He [Ne HNe]]].
  destruct (real_inv_proj (real_plus real_one eps2) Hp) as [Ni HNi].
  pose (Hp' := Hp).
  destruct Hp' as [p [Hp0 [Np HNp]]].
  exists (Nat.max (Nat.max Ne Ni) Np).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnNe : NatLe Ne n) by (apply NatLe_lift; lia).
  assert (HnNi : NatLe Ni n) by (apply NatLe_lift; lia).
  assert (HnNp : NatLe Np n) by (apply NatLe_lift; lia).
  set (yn := projT1 (real_plus real_one eps2) n).
  set (invs := projT1 (real_inv_pos (real_plus real_one eps2) Hp) n).
  (* 1) 逐点：e < (1/4)·invs − |h_n|（HNe 经投影恒等改写） *)
  assert (Hew : Qlt e (Qminus (Qmult (1 # 4) invs) (Qabs (projT1 h n)))).
  { apply QltT_to_Qlt.
    apply (qltT_eq_compat_r (Qminus (Qmult (1 # 4) invs) (Qabs (projT1 h n)))
                            (Qminus (projT1 (real_mult (real_const (1 # 4))
                                                       (real_inv_pos (real_plus real_one eps2) Hp)) n)
                                    (projT1 (real_abs h) n))
                            e).
    - apply Qminus_comp.
      + setoid_rewrite (real_mult_proj (real_const (1 # 4))
                                       (real_inv_pos (real_plus real_one eps2) Hp) n).
        rewrite (real_const_proj (1 # 4) n).
        unfold invs.
        reflexivity.
      + rewrite (real_abs_proj h n). reflexivity.
    - exact (HNe n HnNe).
  }
  (* 2) |h_n| < (1/4)·invs − e（q_lt_minus_shift） *)
  assert (Hshift : Qlt (Qabs (projT1 h n)) (Qminus (Qmult (1 # 4) invs) e)).
  { apply (q_lt_minus_shift e (Qmult (1 # 4) invs) (Qabs (projT1 h n))). exact Hew. }
  (* 3) yn > 0（Hp 见证 p） *)
  assert (Hyn : Qlt 0 yn).
  { apply (Qlt_le_trans 0 p yn).
    - apply QltT_to_Qlt. exact Hp0.
    - apply (Qle_trans p (Qminus (projT1 (real_plus real_one eps2) n) (projT1 real_zero n)) yn).
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact (HNp n HnNp).
      + unfold yn. apply qeq_le. cbn [projT1 real_zero]. ring. }
  (* 4) |h_n|·yn < ((1/4)·invs − e)·yn（Qmult_lt_compat_r；无 _l 变体） *)
  assert (Hmul : Qlt (Qmult (Qabs (projT1 h n)) yn)
                     (Qmult (Qminus (Qmult (1 # 4) invs) e) yn)).
  { apply (Qmult_lt_compat_r (Qabs (projT1 h n))
                             (Qminus (Qmult (1 # 4) invs) e) yn).
    - exact Hyn.
    - exact Hshift. }
  (* 5) ((1/4)·invs − e)·yn ≤ 1/4（invs == Qinv yn ⟹ (1/4)·(yn·invs) == 1/4） *)
  assert (Hinv : invs == Qinv yn).
  { unfold invs, yn. exact (HNi n (NatLe_drop _ _ HnNi)). }
  assert (Hle1 : Qle (Qmult (Qminus (Qmult (1 # 4) invs) e) yn) (1 # 4)).
  { assert (Heq : Qmult (Qminus (Qmult (1 # 4) invs) e) yn ==
                  Qminus (Qmult (1 # 4) (Qmult yn invs)) (Qmult yn e)) by ring.
    apply (Qle_trans (Qmult (Qminus (Qmult (1 # 4) invs) e) yn)
                     (Qminus (Qmult (1 # 4) (Qmult yn invs)) (Qmult yn e))
                     (1 # 4)).
    - apply qeq_le. exact Heq.
    - assert (Hle2 : Qle (Qminus (Qmult (1 # 4) (Qmult yn invs)) (Qmult yn e))
                         (1 # 4)).
      { apply (proj2 (Qle_minus_iff (Qminus (Qmult (1 # 4) (Qmult yn invs)) (Qmult yn e))
                                    (1 # 4))).
        assert (Hinvn : Qmult yn (Qinv yn) == 1).
        { apply Qmult_inv_r. exact (q_neq_of_lt yn Hyn). }
        assert (Hz : Qminus (Qmult (1 # 4) (Qmult yn invs)) (Qmult yn e) ==
                     Qminus (1 # 4) (Qmult yn e)).
        { rewrite Hinv. rewrite Hinvn. ring. }
        rewrite Hz.
        assert (Hze : Qminus (1 # 4) (Qminus (1 # 4) (Qmult yn e)) == Qmult yn e) by ring.
        rewrite Hze.
        apply (Qmult_le_0_compat yn e).
        + apply (Qlt_le_weak 0 yn). exact Hyn.
        + apply (Qlt_le_weak 0 e). apply QltT_to_Qlt. exact He. }
      exact Hle2. }
  (* 6) 组装：yn·|h_n| == |h_n|·yn < ... ≤ 1/4 ⟹ Qle *)
  apply (Qle_trans (Qmult yn (Qabs (projT1 h n)))
                   (Qmult (Qabs (projT1 h n)) yn)
                   (1 # 4)).
  - apply qeq_le. ring.
  - apply Qlt_le_weak.
    apply (Qlt_le_trans (Qmult (Qabs (projT1 h n)) yn)
                        (Qmult (Qminus (Qmult (1 # 4) invs) e) yn)
                        (1 # 4)).
    + exact Hmul.
    + exact Hle1.
Qed.

(* ============================================================ *)
(* Part J2：逐点 glue（增量 2a：D_n 分裂 / rs_add 列 / vdh 桥）  *)
(* ============================================================ *)

(* D_n == S1n + S2n（b5i_sin_err_split + 定义展开） *)
Lemma b5i_dn_split : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (b5a_comp_err_sin x Hx h Hxh) n ==
  Qplus (b5i_S1n x h n) (b5i_S2n x h n).
Proof.
  intros x Hx h Hxh n.
  rewrite (b5i_sin_err_split x Hx h Hxh n).
  unfold b5i_S1n, b5i_S2n, b5i_vn, b5i_dn, b5i_Ahn, b5i_An.
  reflexivity.
Qed.

(* rs_add_sin (A:=arctan x, v:=arctan(x+h)−arctan x) 的逐点列误差 →
   列误差 ≤ b5i_addcol_sin 界（∃N ∀n≥N QltT (b5i_addcol_sin ...) eps） *)
Lemma b5i_rs_addcol : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (b5i_addcol_sin x h Hxh n) eps).
Proof.
  intros x Hx h Hxh eps Heps.
  set (A := cauchy_real_arctan x Hx).
  set (Ah := cauchy_real_arctan (real_plus x h) Hxh).
  set (v := real_plus Ah (real_opp A)).
  destruct (rs_add_sin A v eps Heps) as [N HN].
  exists N.
  intros n Hn.
  assert (Heq : Qeq (b5i_addcol_sin x h Hxh n)
                    (Qabs (Qminus (projT1 (cauchy_real_sin (real_plus A v)) n)
                                  (projT1 (real_plus (real_mult (cauchy_real_sin A) (cauchy_real_cos v))
                                                    (real_mult (cauchy_real_cos A) (cauchy_real_sin v))) n)))).
  { apply Qabs_wd.
    transitivity (Qminus (sin_partial n (b5i_Ahn x h n))
                         (Qplus (Qmult (sin_partial n (b5i_An x n)) (cos_partial n (b5i_vn x h n)))
                                (Qmult (cos_partial n (b5i_An x n)) (sin_partial n (b5i_vn x h n))))).
    - unfold b5i_addcol_sin. reflexivity.
    - apply Qminus_comp.
      + apply Qeq_sym.
        setoid_rewrite (real_sin_proj (real_plus A v) n).
        apply (b5a_sin_partial_wd n (projT1 (real_plus A v) n) (b5i_Ahn x h n)).
        unfold v, A, Ah.
        setoid_rewrite (real_plus_proj (cauchy_real_arctan x Hx)
                                       (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                                  (real_opp (cauchy_real_arctan x Hx))) n).
        setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                       (real_opp (cauchy_real_arctan x Hx)) n).
        setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
        setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
        setoid_rewrite (arctan_real_proj x Hx n).
        unfold b5i_Ahn, b5i_An. ring.
      + transitivity (Qplus (Qmult (projT1 (cauchy_real_sin A) n) (projT1 (cauchy_real_cos v) n))
                            (Qmult (projT1 (cauchy_real_cos A) n) (projT1 (cauchy_real_sin v) n))).
        * apply Qplus_comp; apply Qmult_comp.
          -- apply Qeq_sym.
             setoid_rewrite (real_sin_proj A n).
             apply (b5a_sin_partial_wd n (projT1 A n) (b5i_An x n)).
             unfold A. setoid_rewrite (arctan_real_proj x Hx n). unfold b5i_An. reflexivity.
          -- apply Qeq_sym.
             setoid_rewrite (real_cos_proj v n).
             apply (b5a_cos_partial_wd n (projT1 v n) (b5i_vn x h n)).
             unfold v, A, Ah.
             setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                            (real_opp (cauchy_real_arctan x Hx)) n).
             setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
             setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
             setoid_rewrite (arctan_real_proj x Hx n).
             unfold b5i_vn, b5i_Ahn, b5i_An. ring.
          -- apply Qeq_sym.
             setoid_rewrite (real_cos_proj A n).
             apply (b5a_cos_partial_wd n (projT1 A n) (b5i_An x n)).
             unfold A. setoid_rewrite (arctan_real_proj x Hx n). unfold b5i_An. reflexivity.
          -- apply Qeq_sym.
             setoid_rewrite (real_sin_proj v n).
             apply (b5a_sin_partial_wd n (projT1 v n) (b5i_vn x h n)).
             unfold v, A, Ah.
             setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                            (real_opp (cauchy_real_arctan x Hx)) n).
             setoid_rewrite (real_opp_proj (cauchy_real_arctan x Hx) n).
             setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
             setoid_rewrite (arctan_real_proj x Hx n).
             unfold b5i_vn, b5i_Ahn, b5i_An. ring.
        * apply Qeq_sym.
          setoid_rewrite (real_plus_proj (real_mult (cauchy_real_sin A) (cauchy_real_cos v))
                                         (real_mult (cauchy_real_cos A) (cauchy_real_sin v)) n).
          setoid_rewrite (real_mult_proj (cauchy_real_sin A) (cauchy_real_cos v) n).
          setoid_rewrite (real_mult_proj (cauchy_real_cos A) (cauchy_real_sin v) n).
          apply Qplus_comp; apply Qmult_comp; reflexivity. }
  apply (qltT_eq_compat_l (Qabs (Qminus (projT1 (cauchy_real_sin (real_plus A v)) n)
                                        (projT1 (real_plus (real_mult (cauchy_real_sin A) (cauchy_real_cos v))
                                                          (real_mult (cauchy_real_cos A) (cauchy_real_sin v))) n)))
                          (b5i_addcol_sin x h Hxh n) eps).
  - apply Qeq_sym. exact Heq.
  - exact (HN n Hn).
Qed.

(* proj V n == (Ah_n − A_n) − d_n·h_n（V := arctan(x+h) − (arctan x + d·h)） *)
Lemma b5i_vdhV_proj : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat),
  projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                    (real_opp (real_plus (cauchy_real_arctan x Hx)
                               (real_mult (b5a_atan_d x) h)))) n ==
  (b5i_Ahn x h n - b5i_An x n) - b5i_dn x n * projT1 h n.
Proof.
  intros x Hx h Hxh n.
  setoid_rewrite (real_plus_proj (cauchy_real_arctan (real_plus x h) Hxh)
                                 (real_opp (real_plus (cauchy_real_arctan x Hx)
                                            (real_mult (b5a_atan_d x) h))) n).
  setoid_rewrite (real_opp_proj (real_plus (cauchy_real_arctan x Hx)
                                           (real_mult (b5a_atan_d x) h)) n).
  setoid_rewrite (real_plus_proj (cauchy_real_arctan x Hx)
                                 (real_mult (b5a_atan_d x) h) n).
  setoid_rewrite (real_mult_proj (b5a_atan_d x) h n).
  setoid_rewrite (arctan_real_proj (real_plus x h) Hxh n).
  setoid_rewrite (arctan_real_proj x Hx n).
  unfold b5i_Ahn, b5i_An, b5i_dn.
  ring.
Qed.

(* Qle (Qabs (proj V n)) wb ⟹ Qle (Qabs (v_n − d_n·h_n)) wb（vdh 桥） *)
Lemma b5i_vdh_absV : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (wb : Q),
  Qle (Qabs (projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                               (real_opp (real_plus (cauchy_real_arctan x Hx)
                                          (real_mult (b5a_atan_d x) h)))) n)) wb ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n)))) wb.
Proof.
  intros x Hx h Hxh n wb H.
  apply (Qle_trans (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                   (Qabs (projT1 (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                                            (real_opp (real_plus (cauchy_real_arctan x Hx)
                                                       (real_mult (b5a_atan_d x) h)))) n))
                   wb).
  - apply qeq_imp_qle. apply Qabs_wd.
    unfold b5i_vn.
    apply Qeq_sym. exact (b5i_vdhV_proj x Hx h Hxh n).
  - exact H.
Qed.


(* ============================================================ *)
(* Part J3：per-n 双分支核心界（增量 2b）                        *)
(* ============================================================ *)

(* 分支 A（|v_n| ≤ 1）：二次界吸收 ⟹
   |D_n| ≤ colQ + (2S·kδ + (3S+Mc)·k2)·en·|hn| + (3S+Mc)·E2 *)
Lemma b5i_pern_quad : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc colQ kδ k2 : Q) (en E2 : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  QltT (b5i_addcol_sin x h Hxh n) colQ ->
  Qle (Qabs (b5i_vn x h n)) 1 ->
  Qle (Qabs (projT1 h n)) (Qmult en kδ) ->
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  Qle (Qabs (b5i_dn x n)) 1 ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) ->
  Qle 0 en -> Qle 0 k2 -> Qle 0 E2 ->
  Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
      (Qplus colQ
             (Qplus (Qmult (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                                  (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                           (Qmult en (Qabs (projT1 h n))))
                    (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) E2))).
Proof.
  intros x Hx h Hxh n Ms Mc colQ kδ k2 en E2
         HMs HMc Hcol Hv1 Hhδ Hh12 Hd1 Hw Hen0 Hk20 HE20.
  set (v := b5i_vn x h n).
  set (w := Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))).
  set (S := Qplus Ms Mc).
  assert (HMs0 : Qle 0 Ms).
  { apply (Qle_trans 0 (Qabs (sin_partial n (b5i_An x n))) Ms).
    - apply Qabs_nonneg.
    - exact HMs. }
  assert (HMc0 : Qle 0 Mc).
  { apply (Qle_trans 0 (Qabs (cos_partial n (b5i_An x n))) Mc).
    - apply Qabs_nonneg.
    - exact HMc. }
  assert (HS0 : Qle 0 S).
  { apply (Qle_trans 0 (Qplus 0 0) S).
    - apply qeq_le. ring.
    - apply Qplus_le_compat.
      + exact HMs0.
      + exact HMc0. }
  assert (H2S0 : Qle 0 (Qmult 2 S)).
  { apply (Qmult_le_0_compat 2 S).
    - unfold Qle. simpl. lia.
    - exact HS0. }
  assert (H3S0 : Qle 0 (Qmult 3 S)).
  { apply (Qmult_le_0_compat 3 S).
    - unfold Qle. simpl. lia.
    - exact HS0. }
  assert (HB1 : Qle 0 (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
  { apply (Qle_trans 0 (Qplus 0 0) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - apply qeq_le. ring.
    - apply Qplus_le_compat.
      + apply (Qmult_le_0_compat (Qmult en k2) (Qabs (projT1 h n))).
        * apply (Qmult_le_0_compat en k2 Hen0 Hk20).
        * exact (Qabs_nonneg (projT1 h n)).
      + exact HE20. }
  assert (Hw0 : Qle 0 (Qabs w)).
  { exact (Qabs_nonneg w). }
  (* |v|²、|v|³ 非负 *)
  assert (Hv2n : Qle 0 (q_pow (Qabs v) 2)).
  { rewrite (sc_qpow2_form (Qabs v)).
    apply (Qmult_le_0_compat (Qabs v) (Qabs v) (Qabs_nonneg v) (Qabs_nonneg v)). }
  assert (Hv3n : Qle 0 (q_pow (Qabs v) 3)).
  { rewrite (sc_qpow3_form (Qabs v)).
    apply (Qmult_le_0_compat (Qmult (Qabs v) (Qabs v)) (Qabs v)).
    - apply (Qmult_le_0_compat (Qabs v) (Qabs v) (Qabs_nonneg v) (Qabs_nonneg v)).
    - apply Qabs_nonneg. }
  (* |S1| ≤ colQ + S·|v|² *)
  assert (HS1 : Qle (Qabs (b5i_S1n x h n)) (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))).
  { apply (Qle_trans (Qabs (b5i_S1n x h n))
                     (Qplus colQ (Qplus (Qmult Ms (q_pow (Qabs v) 2)) (Qmult Mc (q_pow (Qabs v) 3))))
                     (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))).
    - apply (b5i_S1_quad x Hx h Hxh n Ms Mc colQ).
      + exact HMs.
      + exact HMc.
      + exact Hv1.
      + exact Hcol.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply (Qle_trans (Qplus (Qmult Ms (q_pow (Qabs v) 2)) (Qmult Mc (q_pow (Qabs v) 3)))
                         (Qplus (Qmult Ms (q_pow (Qabs v) 2)) (Qmult Mc (q_pow (Qabs v) 2)))
                         (Qmult S (q_pow (Qabs v) 2))).
        * apply Qplus_le_compat.
          -- apply Qle_refl.
          -- apply (Qmult_le_compat_nonneg Mc Mc (q_pow (Qabs v) 3) (q_pow (Qabs v) 2)).
             ++ split; [exact HMc0 | apply Qle_refl].
             ++ split; [exact Hv3n | exact (b5i_cube_le_sq v Hv1)].
        * apply qeq_le. unfold S. ring. }
  (* |S2| ≤ Mc·(en·k2·|(projT1 h n)| + E2) *)
  assert (HS2 : Qle (Qabs (b5i_S2n x h n))
                    (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply (b5i_S2_le x Hx h Hxh n Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - exact HMc.
    - exact Hw. }
  (* 三角：|v| ≤ |w| + |(projT1 h n)| *)
  assert (Htri : Qle (Qabs v) (Qplus (Qabs w) (Qabs (projT1 h n)))).
  { unfold v, w.
    apply (Qle_trans (Qabs (b5i_vn x h n))
                     (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                            (Qabs (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                            (Qabs (projT1 h n)))).
    - apply (Qle_trans (Qabs (b5i_vn x h n))
                       (Qabs (Qplus (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n)))
                                    (Qmult (b5i_dn x n) (projT1 h n))))
                       (Qplus (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                              (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
      + apply qeq_imp_qle. apply Qabs_wd. ring.
      + apply Qabs_triangle.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). }
  (* |v|² ≤ 2|w|² + 2|(projT1 h n)|² *)
  assert (Hvsq : Qle (q_pow (Qabs v) 2)
                     (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2)))).
  { apply (b5i_vsq_bound v w (projT1 h n) Htri). }
  (* B2：|w| ≤ 1 + |(projT1 h n)|（|v| ≤ 1、|d| ≤ 1） *)
  assert (Hw2 : Qle (Qabs w) (Qplus 1 (Qabs (projT1 h n)))).
  { unfold v, w.
    apply (Qle_trans (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qmult (b5i_dn x n) (projT1 h n))))
                     (Qplus 1 (Qabs (projT1 h n)))).
    - apply (Qle_trans (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
                       (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qopp (Qmult (b5i_dn x n) (projT1 h n)))))
                       (Qplus (Qabs (b5i_vn x h n)) (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
      + apply Qabs_triangle.
      + apply Qplus_le_compat.
        * apply Qle_refl.
        * apply qeq_imp_qle. apply Qabs_opp.
    - apply Qplus_le_compat.
      + exact Hv1.
      + apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). }
  (* |w|² ≤ B1·B2（B1·B2 乘积；B2 := 1+|(projT1 h n)|） *)
  assert (Hwsq : Qle (q_pow (Qabs w) 2)
                     (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                            (Qplus 1 (Qabs (projT1 h n))))).
  { apply (b5i_sq_le_prod (Qabs w)
                          (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                          (Qplus 1 (Qabs (projT1 h n)))).
    - exact Hw0.
    - exact Hw.
    - exact Hw2. }
  (* |(projT1 h n)|² ≤ (en·kδ)·|(projT1 h n)| *)
  assert (Hhsq : Qle (q_pow (Qabs (projT1 h n)) 2) (Qmult (Qmult en kδ) (Qabs (projT1 h n)))).
  { rewrite (sc_qpow2_form (Qabs (projT1 h n))).
    apply (Qmult_le_compat_r (Qabs (projT1 h n)) (Qmult en kδ) (Qabs (projT1 h n)) Hhδ (Qabs_nonneg (projT1 h n))). }
  (* |(projT1 h n)|²、|w|² 非负 *)
  assert (Hh2n : Qle 0 (q_pow (Qabs (projT1 h n)) 2)).
  { rewrite (sc_qpow2_form (Qabs (projT1 h n))).
    apply (Qmult_le_0_compat (Qabs (projT1 h n)) (Qabs (projT1 h n))
                             (Qabs_nonneg (projT1 h n)) (Qabs_nonneg (projT1 h n))). }
  assert (Hw2n : Qle 0 (q_pow (Qabs w) 2)).
  { rewrite (sc_qpow2_form (Qabs w)).
    apply (Qmult_le_0_compat (Qabs w) (Qabs w) (Qabs_nonneg w) (Qabs_nonneg w)). }
  (* 2S·|(projT1 h n)|² ≤ (2S·kδ)·(en·|(projT1 h n)|) *)
  assert (Ha1 : Qle (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                    (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
  { apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                     (Qmult (Qmult 2 S) (Qmult (Qmult en kδ) (Qabs (projT1 h n))))
                     (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
    - apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                    (q_pow (Qabs (projT1 h n)) 2) (Qmult (Qmult en kδ) (Qabs (projT1 h n)))).
      + split; [exact H2S0 | apply Qle_refl].
      + split.
        * exact Hh2n.
        * exact Hhsq.
    - apply qeq_le. ring. }
  (* 2S·B1·B2 ≤ 3S·B1（B2 ≤ 3/2） *)
  assert (H32 : Qle (Qplus 1 (Qabs (projT1 h n))) (3 # 2)).
  { apply (b5i_one_plus_abs_le32 (projT1 h n) Hh12). }
  assert (Ha2 : Qle (Qmult (Qmult 2 S)
                           (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                  (Qplus 1 (Qabs (projT1 h n)))))
                    (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply (Qle_trans (Qmult (Qmult 2 S)
                            (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                   (Qplus 1 (Qabs (projT1 h n)))))
                     (Qmult (Qmult 2 S)
                            (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) (3 # 2)))
                     (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
    - apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                    (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                           (Qplus 1 (Qabs (projT1 h n))))
                                    (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) (3 # 2))).
      + split; [exact H2S0 | apply Qle_refl].
      + split.
        * apply (Qmult_le_0_compat (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                   (Qplus 1 (Qabs (projT1 h n)))).
          -- exact HB1.
          -- apply (Qle_trans 0 1 (Qplus 1 (Qabs (projT1 h n)))).
             ++ unfold Qle. simpl. lia.
             ++ apply Qle_plus_nonneg_r. exact (Qabs_nonneg (projT1 h n)).
        * apply (Qmult_le_compat_nonneg (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                        (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                        (Qplus 1 (Qabs (projT1 h n)))
                                        (3 # 2)).
          -- split; [exact HB1 | apply Qle_refl].
          -- split.
             ++ apply (Qle_trans 0 1 (Qplus 1 (Qabs (projT1 h n)))).
                ** unfold Qle. simpl. lia.
                ** apply Qle_plus_nonneg_r. exact (Qabs_nonneg (projT1 h n)).
             ++ exact H32.
    - apply qeq_le. ring. }
  (* S·|v|² ≤ (2S·kδ)·(en·|(projT1 h n)|) + (3S)·B1 *)
  assert (Hmain : Qle (Qmult S (q_pow (Qabs v) 2))
                      (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                             (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
  { apply (Qle_trans (Qmult S (q_pow (Qabs v) 2))
                     (Qmult S (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2))))
                     (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                            (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
    - apply (Qmult_le_compat_nonneg S S
                                    (q_pow (Qabs v) 2)
                                    (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2)))).
      + split; [exact HS0 | apply Qle_refl].
      + split; [exact Hv2n | exact Hvsq].
    - apply (Qle_trans (Qmult S (Qplus (Qmult 2 (q_pow (Qabs w) 2)) (Qmult 2 (q_pow (Qabs (projT1 h n)) 2))))
                       (Qplus (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                              (Qmult (Qmult 2 S) (q_pow (Qabs w) 2)))
                       (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                              (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
      + apply qeq_le. ring.
      + apply Qplus_le_compat.
        * apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs (projT1 h n)) 2))
                           (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                           (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))).
          -- exact Ha1.
          -- apply Qle_refl.
        * apply (Qle_trans (Qmult (Qmult 2 S) (q_pow (Qabs w) 2))
                           (Qmult (Qmult 2 S)
                                  (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                         (Qplus 1 (Qabs (projT1 h n)))))
                           (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
          -- apply (Qmult_le_compat_nonneg (Qmult 2 S) (Qmult 2 S)
                                           (q_pow (Qabs w) 2)
                                           (Qmult (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)
                                                  (Qplus 1 (Qabs (projT1 h n))))).
             ++ split; [exact H2S0 | apply Qle_refl].
             ++ split; [exact Hw2n | exact Hwsq].
          -- exact Ha2. }
  (* |D| ≤ |S1| + |S2| *)
  assert (Hdn : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                    (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))).
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                     (Qabs (Qplus (b5i_S1n x h n) (b5i_S2n x h n)))
                     (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))).
    - apply qeq_imp_qle. apply Qabs_wd. exact (b5i_dn_split x Hx h Hxh n).
    - apply Qabs_triangle. }
  (* |S1| + |S2| ≤ (colQ + S·|v|²) + Mc·B1 *)
  assert (Hsum : Qle (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))
                     (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
  { apply Qplus_le_compat.
    - exact HS1.
    - exact HS2. }
  (* 最终装配 *)
  apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                   (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                          (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                   (Qplus colQ
                          (Qplus (Qmult (Qplus (Qmult (Qmult 2 S) kδ)
                                               (Qmult (Qplus (Qmult 3 S) Mc) k2))
                                        (Qmult en (Qabs (projT1 h n))))
                                 (Qmult (Qplus (Qmult 3 S) Mc) E2)))).
  - apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                     (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))
                     (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
    + exact Hdn.
    + exact Hsum.
  - apply (Qle_trans (Qplus (Qplus colQ (Qmult S (q_pow (Qabs v) 2)))
                            (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus (Qplus colQ
                                   (Qplus (Qmult (Qmult (Qmult 2 S) kδ) (Qmult en (Qabs (projT1 h n))))
                                          (Qmult (Qmult 3 S) (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                            (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus colQ
                            (Qplus (Qmult (Qplus (Qmult (Qmult 2 S) kδ)
                                                 (Qmult (Qplus (Qmult 3 S) Mc) k2))
                                          (Qmult en (Qabs (projT1 h n))))
                                   (Qmult (Qplus (Qmult 3 S) Mc) E2)))).
    + apply Qplus_le_compat.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact Hmain.
      * apply Qle_refl.
    + apply qeq_le. ring.
Qed.
(* 分支 B（|v_n| > 1）：crude 全局界 ⟹
   |D_n| ≤ colQ + Ms(4C+2)+Mc(4C+4) + Mc·(en·k2·|h_n| + E2) *)
Lemma b5i_pern_crude : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat) (Ms Mc C colQ k2 : Q) (en E2 : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C) -> Qle 0 C ->
  QltT (b5i_addcol_sin x h Hxh n) colQ ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2) ->
  Qle 0 en -> Qle 0 k2 -> Qle 0 E2 ->
  Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
      (Qplus colQ
             (Qplus (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                           (Qmult Mc (Qplus (Qmult 4 C) 4)))
                    (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))).
Proof.
  intros x Hx h Hxh n Ms Mc C colQ k2 en E2
         HMs HMc HC HC0 Hcol Hw Hen0 Hk20 HE20.
  assert (Hv4 : Qle (Qabs (b5i_vn x h n)) 4).
  { unfold b5i_vn, b5i_Ahn, b5i_An.
    exact (b5i_v_norm_le4 x Hx h Hxh n). }
  (* |S1| ≤ |addcol| + Ms(4C+2) + Mc(4C+4)（b5i_S1_crude_x） *)
  assert (HS1c : Qle (Qabs (b5i_S1n x h n))
                     (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                                   - (Qplus (Qmult (sin_partial n (b5i_An x n))
                                                   (cos_partial n (b5i_vn x h n)))
                                            (Qmult (cos_partial n (b5i_An x n))
                                                   (sin_partial n (b5i_vn x h n))))))
                            (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                   (Qmult Mc (Qplus (Qmult 4 C) 4))))).
  { apply (b5i_S1_crude_x x Hx h Hxh n Ms Mc C).
    - exact HMs.
    - exact HMc.
    - exact HC.
    - exact HC0.
    - exact Hv4. }
  (* |S1| ≤ colQ + Ms(4C+2) + Mc(4C+4) *)
  assert (HS1 : Qle (Qabs (b5i_S1n x h n))
                    (Qplus colQ (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                       (Qmult Mc (Qplus (Qmult 4 C) 4))))).
  { apply (Qle_trans (Qabs (b5i_S1n x h n))
                     (Qplus (b5i_addcol_sin x h Hxh n)
                            (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                   (Qmult Mc (Qplus (Qmult 4 C) 4))))
                     (Qplus colQ (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                        (Qmult Mc (Qplus (Qmult 4 C) 4))))).
    - apply (Qle_trans (Qabs (b5i_S1n x h n))
                       (Qplus (Qabs (sin_partial n (b5i_Ahn x h n)
                                     - (Qplus (Qmult (sin_partial n (b5i_An x n))
                                                     (cos_partial n (b5i_vn x h n)))
                                              (Qmult (cos_partial n (b5i_An x n))
                                                     (sin_partial n (b5i_vn x h n))))))
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C) 4))))
                       (Qplus (b5i_addcol_sin x h Hxh n)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C) 4))))).
      + exact HS1c.
      + apply Qplus_le_compat.
        * apply qeq_imp_qle. unfold b5i_addcol_sin. reflexivity.
        * apply Qle_refl.
    - apply Qplus_le_compat.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hcol.
      + apply Qle_refl. }
  (* |S2| ≤ Mc·B1 *)
  assert (HS2 : Qle (Qabs (b5i_S2n x h n))
                    (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))).
  { apply (b5i_S2_le x Hx h Hxh n Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)).
    - exact HMc.
    - exact Hw. }
  (* |D| ≤ |S1| + |S2| *)
  assert (Hdn : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                    (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))).
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                     (Qabs (Qplus (b5i_S1n x h n) (b5i_S2n x h n)))
                     (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))).
    - apply qeq_imp_qle. apply Qabs_wd. exact (b5i_dn_split x Hx h Hxh n).
    - apply Qabs_triangle. }
  (* 装配 *)
  apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                   (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))
                   (Qplus colQ
                          (Qplus (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                        (Qmult Mc (Qplus (Qmult 4 C) 4)))
                                 (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))).
  - exact Hdn.
  - apply (Qle_trans (Qplus (Qabs (b5i_S1n x h n)) (Qabs (b5i_S2n x h n)))
                     (Qplus (Qplus colQ (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                               (Qmult Mc (Qplus (Qmult 4 C) 4))))
                            (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2)))
                     (Qplus colQ
                            (Qplus (Qplus (Qmult Ms (Qplus (Qmult 4 C) 2))
                                          (Qmult Mc (Qplus (Qmult 4 C) 4)))
                                   (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))).
    + apply Qplus_le_compat.
      * exact HS1.
      * exact HS2.
    + apply qeq_le. ring.
Qed.

End B5A_Item1.

(* ============================================================ *)
(* B4 Tier2 完结                  *)
(* （导数界 ⟹ 函数界：eps 桥 + eps0 端点界 + 区间常值；10 Qed）；  *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b4_chain/p5_tier2_fin.v； *)
(* 零公理面、零承认件、零参数声明。                              *)
(* ============================================================ *)

(* ================= ① 逐点换形件 =================
   projT1 (real_abs (real_plus x (real_opp y))) n == Qabs (projT1 x n - projT1 y n) *)
Lemma b4_abs_minus_proj_eq : forall (x y : Real) (n : nat),
  projT1 (real_abs (real_plus x (real_opp y))) n
  == Qabs (projT1 x n - projT1 y n).
Proof.
  intros x y n.
  rewrite (real_abs_proj (real_plus x (real_opp y)) n).
  rewrite (real_plus_proj x (real_opp y) n).
  rewrite (real_opp_proj y n).
  apply Qabs_wd. ring.
Qed.

(* ================= ② 严格 eps 桥 =================
   ∀e>0(Real): real_lt |x−y| e ⟹ real_eq x y。
   p4 检验第 52/58 行 setoid_rewrite 于 Qlt(Prop) 上下文的卡点修复：
   改以 Qlt_minus_iff 双向 + Qlt_le_trans/qeq_le ring 桥（无 Proper 依赖）。 *)
Lemma b4_abs_lt_forall_eps_eq : forall (x y : Real),
  (forall (e : Real), real_lt real_zero e ->
    real_lt (real_abs (real_plus x (real_opp y))) e) ->
  real_eq x y.
Proof.
  intros x y H.
  unfold real_eq.
  intros eps0 Heps0.
  destruct (H (real_const eps0) (real_const_pos eps0 Heps0)) as [sep [Hsep [N HN]]].
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  (* 目标：QltT (Qabs (x_n − y_n)) eps0 —— 经 b4_abs_minus_proj_eq 换形 *)
  apply (qltT_eq_compat_l (projT1 (real_abs (real_plus x (real_opp y))) n)
                          (Qabs (projT1 x n - projT1 y n)) eps0).
  - exact (b4_abs_minus_proj_eq x y n).
  - apply Qlt_to_QltT.
    (* Prop 层链：Xn < eps0 − sep < eps0 *)
    apply (Qlt_trans (projT1 (real_abs (real_plus x (real_opp y))) n)
                     (eps0 - sep) eps0).
    + (* Xn < eps0 − sep：HN : sep < eps0 − Xn *)
      apply (proj2 (Qlt_minus_iff (projT1 (real_abs (real_plus x (real_opp y))) n)
                                  (eps0 - sep))).
      apply (Qlt_le_trans 0
               ((eps0 - projT1 (real_abs (real_plus x (real_opp y))) n) - sep)
               ((eps0 - sep) + - projT1 (real_abs (real_plus x (real_opp y))) n)).
      * apply (proj1 (Qlt_minus_iff sep
                        (eps0 - projT1 (real_abs (real_plus x (real_opp y))) n))).
        apply QltT_to_Qlt. exact HN.
      * apply qeq_le. ring.
    + (* eps0 − sep < eps0（0 < sep） *)
      apply (proj2 (Qlt_minus_iff (eps0 - sep) eps0)).
      apply (Qlt_le_trans 0 sep (eps0 + - (eps0 - sep))).
      * apply QltT_to_Qlt. exact Hsep.
      * apply qeq_le. ring.
Qed.

(* ================= ③ 纯 Q 余量件（eps0/3 口径） ================= *)
Lemma b4_q_three_pos : QltT 0 3.
Proof.
  apply Qlt_to_QltT. unfold Qlt. simpl. lia.
Qed.

(* 0 <T a ⟹ a/3 < a（Prop Qlt；可判定，非经典） *)
Lemma b4_q_lt_half : forall a : Q, QltT 0 a -> Qlt (Qdiv a 3) a.
Proof.
  intros a Ha.
  apply (proj2 (Qlt_minus_iff (Qdiv a 3) a)).
  apply (Qlt_le_trans 0 (Qmult 2 (Qdiv a 3)) (a + - (Qdiv a 3))).
  - apply (Qmult_lt_0_compat 2 (Qdiv a 3)).
    + unfold Qlt. simpl. lia.
    + apply (Qlt_shift_div_l 0 a 3).
      * apply QltT_to_Qlt. exact b4_q_three_pos.
      * assert (Hz : 0 * 3 == 0) by ring. rewrite Hz. apply QltT_to_Qlt. exact Ha.
  - apply qeq_le. field.
Qed.

(* 0 <T a ⟹ 2·(a/3) < a（Prop Qlt） *)
Lemma b4_q_lt_two_thirds : forall a : Q, QltT 0 a -> Qlt (Qmult 2 (Qdiv a 3)) a.
Proof.
  intros a Ha.
  apply (proj2 (Qlt_minus_iff (Qmult 2 (Qdiv a 3)) a)).
  apply (Qlt_le_trans 0 (Qdiv a 3) (a + - (Qmult 2 (Qdiv a 3)))).
  - apply (Qlt_shift_div_l 0 a 3).
    + apply QltT_to_Qlt. exact b4_q_three_pos.
    + assert (Hz : 0 * 3 == 0) by ring. rewrite Hz. apply QltT_to_Qlt. exact Ha.
  - apply qeq_le. field.
Qed.

(* ================= ④ eps0-对角端点界 =================
   逐 e（Real）界：由 Tier1（M:=eps0、ε:=e/2）+ d ≤ 1+|d| 缩放 +
   eps0·C == e/2 代入 ⟹ real_le (|f b − f a|) e。
   （p4_tier2.v ② 同款移植；依赖根内 b4_chain_lipschitz/b4_inv_cancel/
    b4_pos_diff/b4_qring/real_abs_plus_one_pos，按名引用。零 setoid_rewrite。） *)
Lemma b4_chain_bound_eps0 :
  forall (f : Real -> Real) (a b e : Real)
    (Hab : real_lt a b) (He : real_lt real_zero e)
    (Hext : forall x y : Real, real_eq x y -> real_eq (f x) (f y)),
  (forall (eps0 : Real), real_lt real_zero eps0 ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (x : Real), real_le a x -> real_le x b ->
        forall (h : Real), real_lt (real_abs h) delta ->
        forall (Hxl : real_le a (real_plus x h)) (Hxr : real_le (real_plus x h) b),
        forall (eps1 : Real), real_lt real_zero eps1 ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult eps0 (real_abs h)) eps1)))) ->
  real_le (real_abs (real_plus (f b) (real_opp (f a)))) e.
Proof.
  intros f a b e Hab He Hext Hmod0.
  pose (d := real_plus b (real_opp a)).
  assert (Hd : real_lt real_zero d).
  { unfold d. apply b4_pos_diff. exact Hab. }
  pose (C := real_plus real_one (real_abs d)).
  assert (HC : real_lt real_zero C).
  { unfold C. apply real_abs_plus_one_pos. }
  pose (eps0 := real_mult (real_mult (real_const (1 / 2)) e) (real_inv_pos C HC)).
  assert (Heps0 : real_lt real_zero eps0).
  { unfold eps0. apply real_mult_positive.
    - apply (real_mult_positive (real_const (1 / 2)) e).
      + apply real_const_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
      + exact He.
    - exact (real_inv_pos_pos C HC). }
  pose (e2 := real_mult (real_const (1 / 2)) e).
  assert (He2 : real_lt real_zero e2).
  { unfold e2. apply (real_mult_positive (real_const (1 / 2)) e).
    - apply real_const_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
    - exact He. }
  destruct (Hmod0 eps0 Heps0) as [delta [Hdelta Hmodd]].
  assert (Hbd : real_le (real_abs (real_plus (f b) (real_opp (f a))))
                        (real_plus (real_mult eps0 d) e2)).
  { apply (RealSetoid.real_le_id_r
             (real_abs (real_plus (f b) (real_opp (f a))))
             (real_plus (real_mult eps0 (real_abs (real_plus b (real_opp a)))) e2)
             (real_plus (real_mult eps0 d) e2)).
    - apply (RealSetoid.real_eq_plus_compat (real_mult eps0 (real_abs (real_plus b (real_opp a)))) e2
               (real_mult eps0 d) e2).
      + apply (RealSetoid.real_eq_mult_compat eps0 (real_abs (real_plus b (real_opp a))) eps0 d).
        * apply real_eq_refl.
        * apply real_abs_pos_req. exact Hd.
      + apply real_eq_refl.
    - apply (b4_chain_lipschitz f a b eps0 e2 Hab He2 Hext).
      exists delta. split.
      * exact Hdelta.
      * exact Hmodd. }
  assert (HdC : real_le d C).
  { unfold C.
    (* d ≤ 1+|d|：d ≤ 1+d（real_le_trans 链）再经 d==|d|（real_abs_pos_req）抬到 1+|d| *)
    apply (RealSetoid.real_le_id_r d (real_plus real_one d) (real_plus real_one (real_abs d))).
    - apply (RealSetoid.real_eq_plus_compat real_one d real_one (real_abs d)).
      + apply real_eq_refl.
      + apply real_eq_sym. apply (real_abs_pos_req d Hd).
    - apply (real_le_trans d (real_plus real_zero d) (real_plus real_one d)).
      + apply (RealSetoid.real_eq_le d (real_plus real_zero d)).
        apply (real_eq_trans d (real_plus d real_zero) (real_plus real_zero d)).
        * apply real_eq_sym. apply real_plus_zero.
        * apply real_plus_comm.
      + apply (real_le_plus_compat real_zero real_one d d).
        * apply (RealSetoid.real_lt_le_iff_req real_zero real_one). left. exact real_lt_zero_one.
        * apply real_le_refl. }
  assert (Heps0C : real_eq (real_mult eps0 C) e2).
  { unfold eps0, e2.
    apply (real_eq_trans _ (real_mult C (real_mult (real_mult (real_const (1 / 2)) e)
                                                  (real_inv_pos C HC))) _).
    - b4_qring.
    - apply (b4_inv_cancel C (real_mult (real_const (1 / 2)) e) HC). }
  assert (Heps0d : real_le (real_mult eps0 d) e2).
  { apply (real_le_trans (real_mult eps0 d) (real_mult eps0 C) e2).
    - (* (eps0·d) ≤ (eps0·C)：eps0·d == d·eps0（id_l）→ d·eps0 ≤ C·eps0
         （mult_compat_weak：0≤eps0、d≤C）→ C·eps0 == eps0·C（id_r） *)
      apply (real_le_trans (real_mult eps0 d) (real_mult d eps0) (real_mult eps0 C)).
      + apply (RealSetoid.real_le_id_l (real_mult eps0 d) (real_mult d eps0)
                                       (real_mult d eps0)).
        * apply real_mult_comm.
        * apply real_le_refl.
      + apply (RealSetoid.real_le_id_r (real_mult d eps0) (real_mult C eps0)
                                       (real_mult eps0 C)).
        * apply real_mult_comm.
        * apply (real_le_mult_compat_weak d C eps0).
          -- apply (RealSetoid.real_lt_le_iff_req real_zero eps0). left. exact Heps0.
          -- exact HdC.
    - apply (RealSetoid.real_eq_le (real_mult eps0 C) e2). exact Heps0C. }
  apply (real_le_trans (real_abs (real_plus (f b) (real_opp (f a))))
                       (real_plus (real_mult eps0 d) e2)
                       e).
  - exact Hbd.
  - apply (real_le_trans (real_plus (real_mult eps0 d) e2)
                         (real_plus e2 e2) e).
    + apply (real_le_plus_compat (real_mult eps0 d) e2 e2 e2).
      * exact Heps0d.
      * apply real_le_refl.
    + apply (RealSetoid.real_eq_le (real_plus e2 e2) e).
      unfold e2. b4_qring.
Qed.

(* ================= ⑤ real_le 版 eps 桥 =================
   ∀e>0(Real): real_le |x−y| e ⟹ real_eq x y。
   real_le = Or real_lt real_eq（根 3521）：对每 Q eps0 > 0 用
   e := real_const (eps0/3) 实例化前提：
    - inl（real_lt X (eps0/3)）：同 ② unpack（sep 见证），链
      Xn < eps0/3 − sep < eps0/3 < eps0（经 b4_q_lt_half）；
    - inr（real_eq X (real_const (eps0/3))）：X ≈ eps0/3，取 δ := eps0/3：
      |X_n − eps0/3| < eps0/3 ⟹ X_n < 2·(eps0/3) < eps0（q_abs_lt_lower
      上支 + b4_q_lt_two_thirds 证毕）。
   零 setoid_rewrite：全程 Qlt_minus_iff + qeq_le + q_abs_lt_lower。 *)
Lemma b4_abs_le_forall_eps_eq : forall (x y : Real),
  (forall (e : Real), real_lt real_zero e ->
    real_le (real_abs (real_plus x (real_opp y))) e) ->
  real_eq x y.
Proof.
  intros x y H.
  unfold real_eq.
  intros eps0 Heps0.
  (* eps0/3 > 0（可判定纯 Q；0 < 3 与 0 < eps0 双向乘回） *)
  assert (Ht : QltT 0 (Qdiv eps0 3)).
  { apply Qlt_to_QltT.
    apply (Qlt_shift_div_l 0 eps0 3).
    - apply QltT_to_Qlt. exact b4_q_three_pos.
    - assert (Hz : 0 * 3 == 0) by ring. rewrite Hz. apply QltT_to_Qlt. exact Heps0. }
  destruct (H (real_const (Qdiv eps0 3)) (real_const_pos (Qdiv eps0 3) Ht))
    as [Hlt | Heq].
  - (* inl：real_lt X (real_const (eps0/3))：unpack sep 见证（同 ②） *)
    destruct Hlt as [sep [Hsep [N HN]]].
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    apply (qltT_eq_compat_l (projT1 (real_abs (real_plus x (real_opp y))) n)
                            (Qabs (projT1 x n - projT1 y n)) eps0).
    + exact (b4_abs_minus_proj_eq x y n).
    + apply Qlt_to_QltT.
      apply (Qlt_trans (projT1 (real_abs (real_plus x (real_opp y))) n)
                       ((Qdiv eps0 3) - sep) eps0).
      * (* Xn < (eps0/3) − sep：HN : sep < (eps0/3) − Xn *)
        apply (proj2 (Qlt_minus_iff (projT1 (real_abs (real_plus x (real_opp y))) n)
                                    ((Qdiv eps0 3) - sep))).
        apply (Qlt_le_trans 0
                 (((Qdiv eps0 3) - projT1 (real_abs (real_plus x (real_opp y))) n) - sep)
                 (((Qdiv eps0 3) - sep) + - projT1 (real_abs (real_plus x (real_opp y))) n)).
        -- apply (proj1 (Qlt_minus_iff sep
                           ((Qdiv eps0 3) - projT1 (real_abs (real_plus x (real_opp y))) n))).
           apply QltT_to_Qlt. exact HN.
        -- apply qeq_le. ring.
      * (* (eps0/3 − sep) < eps0：经 eps0/3 中转（0 < sep、b4_q_lt_half） *)
        apply (Qlt_trans ((Qdiv eps0 3) - sep) (Qdiv eps0 3) eps0).
        -- apply (proj2 (Qlt_minus_iff ((Qdiv eps0 3) - sep) (Qdiv eps0 3))).
           apply (Qlt_le_trans 0 sep ((Qdiv eps0 3) + - ((Qdiv eps0 3) - sep))).
           ++ apply QltT_to_Qlt. exact Hsep.
           ++ apply qeq_le. ring.
        -- apply b4_q_lt_half. exact Heps0.
  - (* inr：real_eq X (real_const (eps0/3))：X ≈ eps0/3 ⟹ |X_n| < eps0 *)
    destruct (Heq (Qdiv eps0 3) Ht) as [M HM].
    exists M.
    intros n Hn.
    specialize (HM n Hn).
    apply (qltT_eq_compat_l (projT1 (real_abs (real_plus x (real_opp y))) n)
                            (Qabs (projT1 x n - projT1 y n)) eps0).
    + exact (b4_abs_minus_proj_eq x y n).
    + apply Qlt_to_QltT.
      apply (Qlt_trans (projT1 (real_abs (real_plus x (real_opp y))) n)
                       (Qmult 2 (Qdiv eps0 3)) eps0).
      * (* X_n < 2·(eps0/3)：|X_n − eps0/3| < eps0/3 ⟹ X_n < eps0/3 + eps0/3（q_abs_lt_lower 上支） *)
        apply (Qlt_le_trans (projT1 (real_abs (real_plus x (real_opp y))) n)
                            (Qplus (Qdiv eps0 3) (Qdiv eps0 3))
                            (Qmult 2 (Qdiv eps0 3))).
        -- apply (q_abs_lt_lower (projT1 (real_abs (real_plus x (real_opp y))) n)
                                 (Qdiv eps0 3) (Qdiv eps0 3)).
           apply QltT_to_Qlt. exact HM.
        -- apply qeq_le. field.
      * (* 2·(eps0/3) < eps0 *)
        apply b4_q_lt_two_thirds. exact Heps0.
Qed.

(* ================= ⑥ 终引理 =================
   均匀模(eps0)（M:=eps0 对角）⟹ f b == f a。
   管线：real_le 版 eps 桥（⑤）套 |f b − f a|；每 Real e>0 界由
   ④ b4_chain_bound_eps0 直接给出（无需 eps0/3 手工拆——拆留于 ⑤ 内）。 *)
Lemma b4_deriv_zero_eq_endpoints :
  forall (f : Real -> Real) (a b : Real) (Hab : real_lt a b)
    (Hext : forall x y : Real, real_eq x y -> real_eq (f x) (f y)),
  (forall (eps0 : Real), real_lt real_zero eps0 ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (x : Real), real_le a x -> real_le x b ->
        forall (h : Real), real_lt (real_abs h) delta ->
        forall (Hxl : real_le a (real_plus x h)) (Hxr : real_le (real_plus x h) b),
        forall (eps1 : Real), real_lt real_zero eps1 ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult eps0 (real_abs h)) eps1)))) ->
  real_eq (f b) (f a).
Proof.
  intros f a b Hab Hext Hmod.
  apply (b4_abs_le_forall_eps_eq (f b) (f a)).
  intros e He.
  exact (b4_chain_bound_eps0 f a b e Hab He Hext Hmod).
Qed.

(* ================= ⑦ 区间内常值包装 =================
   ∀x ∈ [a,b]：f x == f a。destruct real_le a x：
    - inl（a < x）：子区间 [a,x] 上重建均匀模（由 [a,b] 模量 +
      real_le_trans 把 x'≤x / (x'+h)≤x 抬到 ≤b）后套 ⑥ 端点引理；
    - inr（a == x）：Hext 直接给 f a == f x，对称。 *)
Lemma b4_const_on_interval :
  forall (f : Real -> Real) (a b : Real) (Hab : real_lt a b)
    (Hext : forall x y : Real, real_eq x y -> real_eq (f x) (f y)),
  (forall (eps0 : Real), real_lt real_zero eps0 ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (x : Real), real_le a x -> real_le x b ->
        forall (h : Real), real_lt (real_abs h) delta ->
        forall (Hxl : real_le a (real_plus x h)) (Hxr : real_le (real_plus x h) b),
        forall (eps1 : Real), real_lt real_zero eps1 ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult eps0 (real_abs h)) eps1)))) ->
  forall (x : Real), real_le a x -> real_le x b -> real_eq (f x) (f a).
Proof.
  intros f a b Hab Hext Hmod x Hax Hxb.
  destruct Hax as [Haxlt | Haxeq].
  - (* inl：a < x ⟹ 子区间 [a,x] 套 ⑥ *)
    assert (Hmod_x : forall (eps0 : Real), real_lt real_zero eps0 ->
      sigT (fun delta : Real => And (real_lt real_zero delta)
        (forall (y : Real), real_le a y -> real_le y x ->
          forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hyl : real_le a (real_plus y h)) (Hyr : real_le (real_plus y h) x),
          forall (eps1 : Real), real_lt real_zero eps1 ->
          real_le (real_abs (real_plus (f (real_plus y h)) (real_opp (f y))))
                  (real_plus (real_mult eps0 (real_abs h)) eps1)))).
    { intros eps0 Heps0.
      destruct (Hmod eps0 Heps0) as [delta [Hdelta Hinner]].
      exists delta. split.
      - exact Hdelta.
      - intros y Hay Hyx h Hh Hyl Hyr eps1 Heps1.
        apply (Hinner y Hay (real_le_trans y x b Hyx Hxb) h Hh Hyl
               (real_le_trans (real_plus y h) x b Hyr Hxb) eps1 Heps1). }
    exact (b4_deriv_zero_eq_endpoints f a x Haxlt Hext Hmod_x).
  - (* inr：a == x ⟹ f x == f a（Hext + 对称） *)
    apply real_eq_sym.
    apply Hext. exact Haxeq.
Qed.

(* ∀x y ∈ [a,b]：f x == f y（两次 ⑦ 首件经 f a 中转） *)
Lemma b4_const_on_interval_pair :
  forall (f : Real -> Real) (a b : Real) (Hab : real_lt a b)
    (Hext : forall x y : Real, real_eq x y -> real_eq (f x) (f y)),
  (forall (eps0 : Real), real_lt real_zero eps0 ->
    sigT (fun delta : Real => And (real_lt real_zero delta)
      (forall (x : Real), real_le a x -> real_le x b ->
        forall (h : Real), real_lt (real_abs h) delta ->
        forall (Hxl : real_le a (real_plus x h)) (Hxr : real_le (real_plus x h) b),
        forall (eps1 : Real), real_lt real_zero eps1 ->
        real_le (real_abs (real_plus (f (real_plus x h)) (real_opp (f x))))
                (real_plus (real_mult eps0 (real_abs h)) eps1)))) ->
  forall (x y : Real), real_le a x -> real_le x b ->
    real_le a y -> real_le y b -> real_eq (f x) (f y).
Proof.
  intros f a b Hab Hext Hmod x y Hax Hxb Hay Hyb.
  apply (real_eq_trans (f x) (f a) (f y)).
  - exact (b4_const_on_interval f a b Hab Hext Hmod x Hax Hxb).
  - apply real_eq_sym.
    exact (b4_const_on_interval f a b Hab Hext Hmod y Hay Hyb).
Qed.

(* ============================================================ *)
(* B5-B task3 Q 层端点闭合件        *)
(* （b5b_E_close_q 主件 + 10 个 b5b_ecl_* 纯 Q 辅助；11 Qed）；      *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b5b_endpoint/              *)
(*   sc2_b5b_05_eclose.v；依赖根 b5b_En/b5b_E_gap/b5b_arch2。       *)
(* ============================================================ *)

(* ============ 纯 Q 辅助（顶层，field 安全） ============ *)

(* ---- 正数除以正数仍正：0<a、0<b ⟹ 0<a/b ---- *)
Lemma b5b_ecl_div_pos : forall (a b : Q), Qlt 0 a -> Qlt 0 b -> Qlt 0 (a / b).
Proof.
  intros a b Ha Hb.
  unfold Qdiv.
  apply (Qmult_lt_0_compat a (Qinv b)).
  - exact Ha.
  - apply (Qinv_lt_0_compat b). exact Hb.
Qed.

(* ---- 0<c ⟹ 0<12c ---- *)
Lemma b5b_ecl_12c_pos : forall (c : Q), Qlt 0 c -> Qlt 0 (12 * c).
Proof.
  intros c Hc.
  apply (Qmult_lt_0_compat 12 c).
  - change (Qlt 0 12). unfold Qlt. simpl. lia.
  - exact Hc.
Qed.

(* ---- arch 输入正性：0<c、0<eps ⟹ 0<eps/(12c) ---- *)
Lemma b5b_ecl_arch_in : forall (c eps : Q), Qlt 0 c -> Qlt 0 eps ->
  Qlt 0 (eps / (12 * c)).
Proof.
  intros c eps Hc Heps.
  apply (b5b_ecl_div_pos eps (12 * c)).
  - exact Heps.
  - apply (b5b_ecl_12c_pos c). exact Hc.
Qed.

(* ---- field 恒等（顶层）：(4c)·(eps/(12c)) == eps/3（c≠0、3≠0） ---- *)
Lemma b5b_ecl_arch_cancel : forall (c eps : Q), Qlt 0 c -> Qlt 0 eps ->
  (4 * c) * (eps / (12 * c)) == eps / 3.
Proof.
  intros c eps Hc Heps.
  field.
  all: try (apply q_neq_of_lt;
            first [ exact Hc
                  | apply (b5b_ecl_12c_pos c); exact Hc
                  | change (Qlt 0 3); unfold Qlt; simpl; lia ]).
Qed.

(* ---- field 恒等（顶层）：eps/3 + 2·(eps/3) == eps（3≠0） ---- *)
Lemma b5b_ecl_third_sum : forall (eps : Q), Qlt 0 eps ->
  (eps / 3) + 2 * (eps / 3) == eps.
Proof.
  intros eps Heps.
  field.
  all: try (apply q_neq_of_lt; change (Qlt 0 3); unfold Qlt; simpl; lia).
Qed.

(* ---- 0<eps ⟹ 0<eps/3 ---- *)
Lemma b5b_ecl_third_pos : forall (eps : Q), Qlt 0 eps -> Qlt 0 (eps / 3).
Proof.
  intros eps Heps.
  unfold Qdiv.
  apply (Qmult_lt_0_compat eps (Qinv 3)).
  - exact Heps.
  - apply (Qinv_lt_0_compat 3). change (Qlt 0 3). unfold Qlt. simpl. lia.
Qed.

(* ---- 左乘严格保序：0<c、a<b ⟹ c·a < c·b（经 comm 桥） ---- *)
Lemma b5b_ecl_mult_lt_l : forall (a b c : Q), Qlt 0 c -> Qlt a b ->
  Qlt (c * a) (c * b).
Proof.
  intros a b c Hc Hab.
  assert (H1 : Qlt (a * c) (b * c)).
  { apply (Qmult_lt_compat_r a b c Hc Hab). }
  rewrite (Qmult_comm a c) in H1.
  rewrite (Qmult_comm b c) in H1.
  exact H1.
Qed.

(* ---- K := 2c(S M)#1 + 2c + 1 ≥ 1（c ≥ 1，2 因子非负） ---- *)
Lemma b5b_ecl_K_ge1 : forall (M : nat) (c : Q), Qle 1 c ->
  Qle 1 (2 * c * (Z.of_nat (Datatypes.S M) # 1) + (2 * c + 1)).
Proof.
  intros M c Hc1.
  assert (Hc0 : Qle 0 c).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hc1]. }
  assert (H2 : Qle 0 (2 * c)).
  { apply (Qmult_le_0_compat 2 c); [unfold Qle; simpl; lia | exact Hc0]. }
  assert (Hsm : Qle 0 (Z.of_nat (Datatypes.S M) # 1)).
  { unfold Qle. simpl. lia. }
  assert (Ht : Qle 0 (2 * c * (Z.of_nat (Datatypes.S M) # 1))).
  { apply (Qmult_le_0_compat (2 * c) (Z.of_nat (Datatypes.S M) # 1)); [exact H2 | exact Hsm]. }
  assert (Hone : Qle 1 (2 * c + 1)).
  { apply (proj2 (Qle_minus_iff 1 (2 * c + 1))).
    assert (Heq : ((2 * c + 1) + - 1) == 2 * c) by ring.
    rewrite Heq. exact H2. }
  apply (Qle_trans _ (Qplus (2 * c * (Z.of_nat (Datatypes.S M) # 1)) (2 * c + 1)) _).
  - apply (Qplus_le_compat 0 (2 * c * (Z.of_nat (Datatypes.S M) # 1)) 1 (2 * c + 1)).
    + exact Ht.
    + exact Hone.
  - apply qeq_imp_qle. ring.
Qed.

(* ---- field 恒等（顶层）：X := (2·(eps/3))/K ⟹ X·K == 2·(eps/3)（K≠0、3≠0） ---- *)
Lemma b5b_ecl_XK_cancel : forall (eps K : Q), ~ (K == 0) ->
  ((2 * (eps / 3)) / K) * K == 2 * (eps / 3).
Proof.
  intros eps K HK0.
  field.
  all: try (exact HK0).
  all: try (apply q_neq_of_lt; change (Qlt 0 3); unfold Qlt; simpl; lia).
Qed.

(* ---- min 正性：0<a、0<b ⟹ 0 < min a b ---- *)
Lemma b5b_ecl_min_pos : forall (a b : Q), Qlt 0 a -> Qlt 0 b -> Qlt 0 (Qmin a b).
Proof.
  intros a b Ha Hb.
  destruct (Q.min_dec a b) as [Hm | Hm].
  - rewrite Hm. exact Ha.
  - rewrite Hm. exact Hb.
Qed.

(* ============================================================ *)
(* 主件：b5b_E_close_q                                           *)
(* ============================================================ *)
Lemma b5b_E_close_q : forall (eps : Q), Qlt 0 eps ->
  sigT (fun N : nat => sigT (fun g0 : Q => And (QltT 0 g0)
    (forall (n : nat) (g : Q), NatLe N n -> Qlt 0 g -> Qle g g0 ->
      Qlt (Qabs (b5b_En n (1 - g) - b5b_En n 1)) eps))).
Proof.
  intros eps Heps.
  (* c := b5b_arch2（c ≥ 1；HC := ∀j exp_series j 2 ≤T c） *)
  destruct b5b_arch2 as [c [Hc1T HC]].
  assert (Hc1 : Qle 1 c) by (exact (QleT'_to_Qle 1 c Hc1T)).
  assert (Hcpos : Qlt 0 c).
  { apply (Qlt_le_trans 0 1 c); [unfold Qlt; simpl; lia | exact Hc1]. }
  assert (Hc0 : Qle 0 c).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hc1]. }
  (* arch 输入正性，q_arch_inv 取 M：1/(M+2) < eps/(12c) *)
  assert (Harchpos : Qlt 0 (eps / (12 * c))) by
    (apply (b5b_ecl_arch_in c eps Hcpos Heps)).
  destruct (q_arch_inv (eps / (12 * c)) Harchpos) as [M HM].
  (* 记 T := 1/(2M+3)、K := 2c(S M)#1 + 2c + 1（与 b5b_E_gap RHS 逐字一致） *)
  set (T := 1 / (Z.of_nat (2 * M + 3) # 1)).
  set (K := 2 * c * (Z.of_nat (Datatypes.S M) # 1) + (2 * c + 1)).
  (* X := (2·(eps/3))/K；g0 := min(1, X) *)
  set (X := (2 * (eps / 3)) / K).
  set (g0 := Qmin 1 X).
  (* 事实：K ≥ 1、K > 0、K ≠ 0；X > 0；X·K == 2·(eps/3)；0<eps/3 *)
  assert (He3 : Qlt 0 (eps / 3)) by (apply (b5b_ecl_third_pos eps); exact Heps).
  assert (Hk1 : Qle 1 K).
  { unfold K. apply (b5b_ecl_K_ge1 M c). exact Hc1. }
  assert (Hkpos : Qlt 0 K).
  { apply (Qlt_le_trans 0 1 K); [unfold Qlt; simpl; lia | exact Hk1]. }
  assert (Hk0 : Qle 0 K).
  { apply (Qle_trans _ 1 _); [unfold Qle; simpl; lia | exact Hk1]. }
  assert (Hkneq : ~ (K == 0)) by (apply (q_neq_of_lt K); exact Hkpos).
  assert (H2e3 : Qlt 0 (2 * (eps / 3))).
  { apply (Qmult_lt_0_compat 2 (eps / 3)); [unfold Qlt; simpl; lia | exact He3]. }
  assert (HXpos : Qlt 0 X).
  { unfold X. apply (b5b_ecl_div_pos (2 * (eps / 3)) K); [exact H2e3 | exact Hkpos]. }
  assert (HXK : X * K == 2 * (eps / 3)).
  { unfold X. apply (b5b_ecl_XK_cancel eps K Hkneq). }
  (* g0 事实：0<g0、g0≤1、g0≤X *)
  assert (Hg0pos : Qlt 0 g0).
  { unfold g0. apply (b5b_ecl_min_pos 1 X); [unfold Qlt; simpl; lia | exact HXpos]. }
  assert (Hg0le1 : Qle g0 1).
  { unfold g0. exact (Q.le_min_l 1 X). }
  assert (Hg0leX : Qle g0 X).
  { unfold g0. exact (Q.le_min_r 1 X). }
  (* 返回 N := M、g0 *)
  exists M. exists g0. split.
  - exact (Qlt_to_QltT 0 g0 Hg0pos).
  - intros n g Hn Hgpos Hgg0.
    (* 域：0≤g≤1（g≤g0≤1）；g≤X（g≤g0≤X） *)
    assert (Hg0le : Qle 0 g) by (apply (Qlt_le_weak 0 g); exact Hgpos).
    assert (Hg1 : Qle g 1) by (apply (Qle_trans _ g0 _); [exact Hgg0 | exact Hg0le1]).
    assert (HgX : Qle g X) by (apply (Qle_trans _ g0 _); [exact Hgg0 | exact Hg0leX]).
    (* b5b_E_gap：|Δ| ≤ 4cT + gK *)
    assert (Hgap : Qle (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                     ((4 * c) * T + g * K)).
    { apply (b5b_E_gap n M g c Hc0 HC Hg0le Hg1 Hn). }
    (* 第 1 项：4cT < eps/3（T ≤ 1/(M+2) < eps/(12c)，乘 4c>0，field 收） *)
    assert (Ht_le : Qle T (1 / (Z.of_nat (M + 2) # 1))).
    { unfold T. apply (atan_inv_chain M M). lia. }
    assert (Ht_arch : Qlt T (eps / (12 * c))).
    { apply (Qle_lt_trans T (1 / (Z.of_nat (M + 2) # 1)) (eps / (12 * c)));
        [exact Ht_le | exact HM]. }
    assert (H4c : Qlt 0 (4 * c)) by
      (apply (Qmult_lt_0_compat 4 c); [unfold Qlt; simpl; lia | exact Hcpos]).
    assert (Ht1m : Qlt ((4 * c) * T) ((4 * c) * (eps / (12 * c)))).
    { apply (b5b_ecl_mult_lt_l T (eps / (12 * c)) (4 * c)); [exact H4c | exact Ht_arch]. }
    assert (Ht1 : Qlt ((4 * c) * T) (eps / 3)).
    { apply (Qlt_le_trans ((4 * c) * T) ((4 * c) * (eps / (12 * c))) (eps / 3));
        [exact Ht1m | apply qeq_le; apply (b5b_ecl_arch_cancel c eps Hcpos Heps)]. }
    (* 第 2 项：gK ≤ XK == 2·(eps/3)（K≥0 乘 g≤X） *)
    assert (HgK : Qle (g * K) (X * K)).
    { apply (Qmult_le_compat_r g X K); [exact HgX | exact Hk0]. }
    assert (Ht2 : Qle (g * K) (2 * (eps / 3))).
    { apply (Qle_trans (g * K) (X * K) (2 * (eps / 3)));
        [exact HgK | apply qeq_le; exact HXK]. }
    (* 总和：4cT + gK < eps/3 + 2·(eps/3) == eps *)
    assert (Hsum : Qlt ((4 * c) * T + g * K) (eps / 3 + 2 * (eps / 3))).
    { apply (Qplus_lt_le_compat ((4 * c) * T) (eps / 3) (g * K) (2 * (eps / 3)));
        [exact Ht1 | exact Ht2]. }
    assert (Hsum2 : Qlt ((4 * c) * T + g * K) eps).
    { apply (Qlt_le_trans ((4 * c) * T + g * K) (eps / 3 + 2 * (eps / 3)) eps);
        [exact Hsum | apply qeq_le; apply (b5b_ecl_third_sum eps Heps)]. }
    (* 结论：|Δ| ≤ 4cT + gK < eps *)
    apply (Qle_lt_trans (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                         ((4 * c) * T + g * K) eps);
      [exact Hgap | exact Hsum2].
Qed.

(* ============================================================ *)
(* B5-B task2 + task5 收尾          *)
(* （b5b_sin_cont / b5b_cos_cont 全域逐 eps 连续；b6_f1_template 与 *)
(* Section B5bEndpointBridge 桥接引理 b5b_f1_closure；6 Qed）；来源：    *)
(*   演变/.ablation/sc2_parallel/sc2_b5b_endpoint/sc2_b5b_07_cont.v *)
(* ============================================================ *)

(* ---- Q 层：正分数（1/4、1/8）与整除正性 ---- *)
Lemma b5b_qpos4 : forall (q : Q), Qlt 0 q -> Qlt 0 (q / 4).
Proof.
  intros q Hq.
  unfold Qdiv.
  apply (Qmult_lt_0_compat q (Qinv 4)).
  - exact Hq.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Qed.

Lemma b5b_qpos8 : forall (q : Q), Qlt 0 q -> Qlt 0 (q / 8).
Proof.
  intros q Hq.
  unfold Qdiv.
  apply (Qmult_lt_0_compat q (Qinv 8)).
  - exact Hq.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Qed.

(* ============================================================ *)
(* B6 模板与闭包（零公理面；b5b_hsc_theorem 未在上游根件        *)
(*  Qed——A 线（05_eclose/06_endpoint）产出——本文件以 Section    *)
(*  Hypothesis 声明其语句证明 b5b_f1_closure，A 线并入 *)
(*  后再组装（b5b_f1_closure hsc 消去第一参数）。）               *)
(* ============================================================ *)

(* ---- B6 模板：Hsc（sin(arctan 1) == cos(arctan 1)）⟹ F1 ---- *)
Lemma b6_f1_template :
  (real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real)) ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intro Hsc.
  exact (a3_closure_f1 Hsc).
Qed.

(* ---- Section 桥：b5a_E_zero_on_unit ⟹ Hsc（Hypothesis 版） ---- *)
Section B5bEndpointBridge.
Hypothesis b5b_hsc_theorem : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (real_E x Hx) real_zero ->
  real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real).

Lemma b5b_f1_closure : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (real_E x Hx) real_zero ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intros x Hx Hlt0 Hlt1 HEz.
  apply a3_closure_f1.
  apply (b5b_hsc_theorem x Hx).
  - exact Hlt0.
  - exact Hlt1.
  - exact HEz.
Qed.
End B5bEndpointBridge.

(* ============================================================ *)
(* task 2：sin/cos 全域逐 eps 连续                              *)
(*  实路线：real_sin_deriv_linear（eps := eps' := const(epsQ/4)）*)
(*  给出 |sin(x+h)−(sin x+cos x·h)| ≤ (epsQ/4)|h| + epsQ/4；     *)
(*  |cos x·h| ≤ Mc·|h|（real_norm_bounded 逐点）；               *)
(*  δ := real_min δ' (const c)，c := epsQ/(2·(epsQ/4+Mc))：     *)
(*  |h| < c−e1 ⟹ 总 ≤ epsQ/4 + eps1 + (epsQ/4+Mc)|h| < 7epsQ/8， *)
(*  再经 q_lt_minus_shift 证毕（仿 03 逐点样式）。                 *)
(* ============================================================ *)

(* ---- sin 连续（1/2） ---- *)
Lemma b5b_sin_cont : forall (x : Real) (epsQ : Q), QltT 0 epsQ ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall h : Real, real_lt (real_abs h) delta ->
      real_le (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                                   (real_opp (cauchy_real_sin x))))
              (real_const epsQ))).
Proof.
  intros x epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (Hq4 : Qlt 0 (epsQ / 4)) by (apply b5b_qpos4; exact HepsQ).
  assert (Hq8 : Qlt 0 (epsQ / 8)) by (apply b5b_qpos8; exact HepsQ).
  destruct (real_norm_bounded (cauchy_real_cos x)) as [Mc [HMc_pos HMc]].
  assert (HMc0 : Qlt 0 Mc) by (apply QltT_to_Qlt; exact HMc_pos).
  set (c := epsQ / (2 * (epsQ / 4 + Mc))).
  assert (Hc0 : Qlt 0 c).
  { unfold c.
    unfold Qdiv.
    apply (Qmult_lt_0_compat epsQ (Qinv (2 * (epsQ / 4 + Mc)))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat 2 (epsQ / 4 + Mc)).
      + unfold Qlt. simpl. lia.
      + apply (Qlt_le_trans 0 (epsQ / 4) (epsQ / 4 + Mc)).
        * exact Hq4.
        * apply (Qle_plus_nonneg_r (epsQ / 4) Mc).
          apply Qlt_le_weak. exact HMc0. }
  set (eps1 := epsQ / 8).
  assert (Heps1 : Qlt 0 eps1) by (unfold eps1; exact Hq8).
  assert (Heps1T : QltT 0 eps1) by (apply Qlt_to_QltT; exact Heps1).
  assert (Heps1nn : Qle 0 eps1) by (apply Qlt_le_weak; exact Heps1).
  assert (HepsR : real_lt real_zero (real_const (epsQ / 4)))
    by (apply real_const_pos_f1; exact Hq4).
  destruct (real_sin_deriv_linear x (real_const (epsQ / 4)) HepsR) as [d0 [Hd0 Hcore]].
  exists (real_min d0 (real_const c)).
  split.
  { apply real_min_pos.
    - exact Hd0.
    - apply real_const_pos_f1. exact Hc0. }
  { intros h Hh.
    left.
    assert (Hh_d0 : real_lt (real_abs h) d0)
      by (apply (real_min_lt_l h d0 (real_const c)); exact Hh).
    assert (Hh_c : real_lt (real_abs h) (real_const c))
      by (apply (real_min_lt_r h d0 (real_const c)); exact Hh).
    (* 线性化界：real_sin_deriv_linear 实例化 eps := eps' := const(epsQ/4) *)
    assert (Hlin : real_le
        (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                   (real_opp (real_plus (cauchy_real_sin x)
                                        (real_mult (cauchy_real_cos x) h)))))
        (real_plus (real_mult (real_const (epsQ / 4)) (real_abs h))
                   (real_const (epsQ / 4)))).
    { apply (Hcore h Hh_d0 (real_const (epsQ / 4)) HepsR). }
    (* 逐 eps 化：|D_n| ≤ (epsQ/4)|h_n| + epsQ/4 + eps1（n ≥ N2） *)
    destruct (real_le_pointwise_eps
        (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                   (real_opp (real_plus (cauchy_real_sin x)
                                        (real_mult (cauchy_real_cos x) h)))))
        (real_plus (real_mult (real_const (epsQ / 4)) (real_abs h))
                   (real_const (epsQ / 4)))
        eps1 Hlin Heps1T) as [N2 HN2].
    (* |h| < const c 的分离见证 e1：|h_n| < c − e1（n ≥ N1） *)
    destruct Hh_c as [e1 [He1T [N1 HN1]]].
    assert (He1 : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1T).
    exists (epsQ / 8).
    split.
    { apply Qlt_to_QltT. exact Hq8. }
    { exists (Nat.max N2 N1).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (HnN2 : (N2 <= n)%nat) by lia.
      assert (HnN1 : (N1 <= n)%nat) by lia.
      (* 点态缩写 *)
      set (sn1 := projT1 (cauchy_real_sin (real_plus x h)) n).
      set (snx := projT1 (cauchy_real_sin x) n).
      set (cnx := projT1 (cauchy_real_cos x) n).
      set (hn := projT1 h n).
      (* ① |h_n| < c − e1 *)
      assert (Hhnlt : Qlt (Qabs hn) (c - e1)).
      { apply (q_lt_minus_shift e1 c (Qabs hn)).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r
                 (c - Qabs hn)
                 (projT1 (real_const c) n - projT1 (real_abs h) n) e1).
        - rewrite (real_const_proj c n). rewrite (real_abs_proj h n).
          unfold hn. ring.
        - exact (HN1 n (NatLe_lift _ _ HnN1)). }
      (* ② 线性化点态界：|D_n| ≤ (epsQ/4)|h_n| + epsQ/4 + eps1 *)
      assert (Hdev : Qle
          (Qabs (sn1 - (snx + cnx * hn)))
          (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn)) (Qdiv epsQ 4)) eps1)).
      { apply (Qle_trans _
                 (Qplus (projT1 (real_plus (real_mult (real_const (epsQ / 4))
                                                      (real_abs h))
                                           (real_const (epsQ / 4))) n) eps1) _).
        - apply (Qle_trans _
                   (projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                              (real_opp (real_plus (cauchy_real_sin x)
                                                   (real_mult (cauchy_real_cos x) h))))) n) _).
          + apply qeq_le.
            rewrite (real_abs_proj
                       (real_plus (cauchy_real_sin (real_plus x h))
                                  (real_opp (real_plus (cauchy_real_sin x)
                                                       (real_mult (cauchy_real_cos x) h)))) n).
            apply (Qabs_wd
                     (sn1 - (snx + cnx * hn))
                     (projT1 (real_plus (cauchy_real_sin (real_plus x h))
                                        (real_opp (real_plus (cauchy_real_sin x)
                                                             (real_mult (cauchy_real_cos x) h)))) n)).
            rewrite (real_plus_proj (cauchy_real_sin (real_plus x h))
                                    (real_opp (real_plus (cauchy_real_sin x)
                                                         (real_mult (cauchy_real_cos x) h))) n).
            rewrite (real_opp_proj (real_plus (cauchy_real_sin x)
                                              (real_mult (cauchy_real_cos x) h)) n).
            rewrite (real_plus_proj (cauchy_real_sin x)
                                    (real_mult (cauchy_real_cos x) h) n).
            rewrite (real_mult_proj (cauchy_real_cos x) h n).
            unfold sn1, snx, cnx, hn. ring.
          + exact (HN2 n HnN2).
        - apply qeq_le.
          rewrite (real_plus_proj (real_mult (real_const (epsQ / 4)) (real_abs h))
                                  (real_const (epsQ / 4)) n).
          rewrite (real_mult_proj (real_const (epsQ / 4)) (real_abs h) n).
          rewrite (real_const_proj (epsQ / 4) n).
          rewrite (real_abs_proj h n).
          unfold eps1, hn. ring. }
      (* ③ |cos x·h| 逐点：|cnx·hn| ≤ Mc·|hn| *)
      assert (Hnorm : Qle (Qabs (cnx * hn)) (Qmult Mc (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qabs cnx) (Qabs hn)) _).
        - apply qeq_le. apply (Qabs_Qmult cnx hn).
        - apply (Qmult_le_compat_r (Qabs cnx) Mc (Qabs hn)).
          + apply QleT'_to_Qle. apply (HMc n).
          + apply Qabs_nonneg. }
      (* ④ 三角：|An| ≤ |Dn| + |cnx·hn| *)
      assert (Htri : Qle (Qabs (sn1 - snx))
                         (Qplus (Qabs (sn1 - (snx + cnx * hn)))
                                (Qabs (cnx * hn)))).
      { apply (Qle_trans _ (Qabs ((sn1 - (snx + cnx * hn)) + cnx * hn)) _).
        - apply qeq_le.
          apply (Qabs_wd (sn1 - snx) ((sn1 - (snx + cnx * hn)) + cnx * hn)).
          ring.
        - apply Qabs_triangle. }
      (* ⑤ 汇总：|An| ≤ (epsQ/4+Mc)|h_n| + epsQ/4 + eps1 *)
      assert (Htot : Qle (Qabs (sn1 - snx))
          (Qplus (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn)) (Qdiv epsQ 4)) eps1)
                 (Qmult Mc (Qabs hn)))).
      { apply (Qle_trans _ (Qplus (Qabs (sn1 - (snx + cnx * hn)))
                                  (Qabs (cnx * hn))) _).
        - exact Htri.
        - apply Qplus_le_compat.
          + exact Hdev.
          + exact Hnorm. }
      (* ⑥ ring 重组：|An| ≤ (epsQ/4 + eps1) + (epsQ/4 + Mc)·|h_n| *)
      assert (Htot2 : Qle (Qabs (sn1 - snx))
          (Qplus (Qplus (Qdiv epsQ 4) eps1)
                 (Qmult (Qplus (Qdiv epsQ 4) Mc) (Qabs hn)))).
      { apply (Qle_trans _ (Qplus (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn))
                                                (Qdiv epsQ 4)) eps1)
                                  (Qmult Mc (Qabs hn))) _).
        - exact Htot.
        - apply qeq_le. ring. }
      (* ⑦ 因子正性 F := epsQ/4 + Mc > 0 *)
      assert (HF0 : Qlt 0 (Qplus (Qdiv epsQ 4) Mc)).
      { apply (Qlt_le_trans 0 (epsQ / 4) (Qplus (Qdiv epsQ 4) Mc)).
        - exact Hq4.
        - apply (Qle_plus_nonneg_r (Qdiv epsQ 4) Mc).
          apply Qlt_le_weak. exact HMc0. }
      assert (HFnn : Qle 0 (Qplus (Qdiv epsQ 4) Mc))
        by (apply Qlt_le_weak; exact HF0).
      (* ⑧ 严格链：F·|h_n| < F·(c−e1) < F·c *)
      assert (Hm_lt : Qlt (Qmult (Qplus (Qdiv epsQ 4) Mc) (Qabs hn))
                          (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1))).
      { apply (proj2 (Qmult_lt_l (Qabs hn) (c - e1)
                                 (Qplus (Qdiv epsQ 4) Mc) HF0)).
        exact Hhnlt. }
      assert (Hcme : Qlt (c - e1) c).
      { apply (proj2 (Qlt_minus_iff (c - e1) c)).
        apply (Qlt_le_trans 0 e1 (Qminus c (Qminus c e1))).
        - exact He1.
        - apply qeq_le. ring. }
      assert (Hm_lt2 : Qlt (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1))
                           (Qmult (Qplus (Qdiv epsQ 4) Mc) c)).
      { apply (proj2 (Qmult_lt_l (c - e1) c
                                 (Qplus (Qdiv epsQ 4) Mc) HF0)).
        exact Hcme. }
      (* ⑨ An < (epsQ/4 + eps1) + F·(c−e1) < (epsQ/4 + eps1) + F·c *)
      assert (Hmid_lt : Qlt (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Mc) (Qabs hn)))
                            (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1)))).
      { apply (proj2 (Qplus_lt_r
                        (Qmult (Qplus (Qdiv epsQ 4) Mc) (Qabs hn))
                        (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1))
                        (Qplus (Qdiv epsQ 4) eps1))).
        exact Hm_lt. }
      assert (Hmid_lt2 : Qlt (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                    (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1)))
                             (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                    (Qmult (Qplus (Qdiv epsQ 4) Mc) c))).
      { apply (proj2 (Qplus_lt_r
                        (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1))
                        (Qmult (Qplus (Qdiv epsQ 4) Mc) c)
                        (Qplus (Qdiv epsQ 4) eps1))).
        exact Hm_lt2. }
      assert (HAn_lt : Qlt (Qabs (sn1 - snx))
                           (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                  (Qmult (Qplus (Qdiv epsQ 4) Mc) c))).
      { apply (Qlt_trans (Qabs (sn1 - snx))
                         (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1)))
                         (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                (Qmult (Qplus (Qdiv epsQ 4) Mc) c))).
        - apply (Qle_lt_trans (Qabs (sn1 - snx))
                              (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                     (Qmult (Qplus (Qdiv epsQ 4) Mc) (Qabs hn)))
                              (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                     (Qmult (Qplus (Qdiv epsQ 4) Mc) (c - e1)))).
          + exact Htot2.
          + exact Hmid_lt.
        - exact Hmid_lt2. }
      (* ⑩ 结论：An < epsQ − epsQ/8（(epsQ/4+Mc)·c == epsQ/2） *)
      apply (qltT_eq_compat_r
               (projT1 (real_const epsQ) n
                - projT1 (real_abs (real_plus (cauchy_real_sin (real_plus x h))
                                              (real_opp (cauchy_real_sin x)))) n)
               (Qminus epsQ (Qabs (sn1 - snx)))
               (Qdiv epsQ 8)).
      - (* Qeq：RAW == epsQ − |An| *)
        rewrite (real_const_proj epsQ n).
        rewrite (real_abs_proj (real_plus (cauchy_real_sin (real_plus x h))
                                          (real_opp (cauchy_real_sin x))) n).
        rewrite (real_plus_proj (cauchy_real_sin (real_plus x h))
                                (real_opp (cauchy_real_sin x)) n).
        rewrite (real_opp_proj (cauchy_real_sin x) n).
        unfold sn1, snx. reflexivity.
      - apply Qlt_to_QltT.
        apply (q_lt_minus_shift (Qabs (sn1 - snx)) epsQ (Qdiv epsQ 8)).
        apply (Qlt_le_trans (Qabs (sn1 - snx))
                            (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Mc) c))
                            (Qminus epsQ (Qdiv epsQ 8))).
        + exact HAn_lt.
        + apply qeq_le.
          unfold c, eps1.
          field.
          all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia).
          all: apply q_neq_of_lt;
               apply (Qlt_le_trans 0 epsQ);
               [ exact HepsQ |
                 apply (q_le_plus_nonneg_r_q epsQ);
                 apply (Qmult_le_0_compat Mc);
                 [ apply Qlt_le_weak; exact HMc0 | unfold Qle; simpl; lia ] ]. } }
Qed.

(* ---- cos 连续（2/2） ---- *)
Lemma b5b_cos_cont : forall (x : Real) (epsQ : Q), QltT 0 epsQ ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall h : Real, real_lt (real_abs h) delta ->
      real_le (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                                   (real_opp (cauchy_real_cos x))))
              (real_const epsQ))).
Proof.
  intros x epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (Hq4 : Qlt 0 (epsQ / 4)) by (apply b5b_qpos4; exact HepsQ).
  assert (Hq8 : Qlt 0 (epsQ / 8)) by (apply b5b_qpos8; exact HepsQ).
  destruct (real_norm_bounded (cauchy_real_sin x)) as [Ms [HMs_pos HMs]].
  assert (HMs0 : Qlt 0 Ms) by (apply QltT_to_Qlt; exact HMs_pos).
  set (c := epsQ / (2 * (epsQ / 4 + Ms))).
  assert (Hc0 : Qlt 0 c).
  { unfold c.
    unfold Qdiv.
    apply (Qmult_lt_0_compat epsQ (Qinv (2 * (epsQ / 4 + Ms)))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat.
      apply (Qmult_lt_0_compat 2 (epsQ / 4 + Ms)).
      + unfold Qlt. simpl. lia.
      + apply (Qlt_le_trans 0 (epsQ / 4) (epsQ / 4 + Ms)).
        * exact Hq4.
        * apply (Qle_plus_nonneg_r (epsQ / 4) Ms).
          apply Qlt_le_weak. exact HMs0. }
  set (eps1 := epsQ / 8).
  assert (Heps1 : Qlt 0 eps1) by (unfold eps1; exact Hq8).
  assert (Heps1T : QltT 0 eps1) by (apply Qlt_to_QltT; exact Heps1).
  assert (HepsR : real_lt real_zero (real_const (epsQ / 4)))
    by (apply real_const_pos_f1; exact Hq4).
  destruct (real_cos_deriv_linear x (real_const (epsQ / 4)) HepsR) as [d0 [Hd0 Hcore]].
  exists (real_min d0 (real_const c)).
  split.
  { apply real_min_pos.
    - exact Hd0.
    - apply real_const_pos_f1. exact Hc0. }
  { intros h Hh.
    left.
    assert (Hh_d0 : real_lt (real_abs h) d0)
      by (apply (real_min_lt_l h d0 (real_const c)); exact Hh).
    assert (Hh_c : real_lt (real_abs h) (real_const c))
      by (apply (real_min_lt_r h d0 (real_const c)); exact Hh).
    (* 线性化界：real_cos_deriv_linear 实例化 eps := eps' := const(epsQ/4) *)
    assert (Hlin : real_le
        (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                   (real_opp (real_plus (cauchy_real_cos x)
                                        (real_opp (real_mult (cauchy_real_sin x) h))))))
        (real_plus (real_mult (real_const (epsQ / 4)) (real_abs h))
                   (real_const (epsQ / 4)))).
    { apply (Hcore h Hh_d0 (real_const (epsQ / 4)) HepsR). }
    destruct (real_le_pointwise_eps
        (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                   (real_opp (real_plus (cauchy_real_cos x)
                                        (real_opp (real_mult (cauchy_real_sin x) h))))))
        (real_plus (real_mult (real_const (epsQ / 4)) (real_abs h))
                   (real_const (epsQ / 4)))
        eps1 Hlin Heps1T) as [N2 HN2].
    destruct Hh_c as [e1 [He1T [N1 HN1]]].
    assert (He1 : Qlt 0 e1) by (apply QltT_to_Qlt; exact He1T).
    exists (epsQ / 8).
    split.
    { apply Qlt_to_QltT. exact Hq8. }
    { exists (Nat.max N2 N1).
      intros n Hn.
      apply NatLe_drop in Hn.
      assert (HnN2 : (N2 <= n)%nat) by lia.
      assert (HnN1 : (N1 <= n)%nat) by lia.
      set (cn1 := projT1 (cauchy_real_cos (real_plus x h)) n).
      set (cx := projT1 (cauchy_real_cos x) n).
      set (sx := projT1 (cauchy_real_sin x) n).
      set (hn := projT1 h n).
      (* ① |h_n| < c − e1 *)
      assert (Hhnlt : Qlt (Qabs hn) (c - e1)).
      { apply (q_lt_minus_shift e1 c (Qabs hn)).
        apply QltT_to_Qlt.
        apply (qltT_eq_compat_r
                 (c - Qabs hn)
                 (projT1 (real_const c) n - projT1 (real_abs h) n) e1).
        - rewrite (real_const_proj c n). rewrite (real_abs_proj h n).
          unfold hn. ring.
        - exact (HN1 n (NatLe_lift _ _ HnN1)). }
      (* ② 线性化点态界：|D_n| ≤ (epsQ/4)|h_n| + epsQ/4 + eps1，D := c1−cx+sx·hn *)
      assert (Hdev : Qle
          (Qabs (cn1 - cx + sx * hn))
          (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn)) (Qdiv epsQ 4)) eps1)).
      { apply (Qle_trans _
                 (Qplus (projT1 (real_plus (real_mult (real_const (epsQ / 4))
                                                      (real_abs h))
                                           (real_const (epsQ / 4))) n) eps1) _).
        - apply (Qle_trans _
                   (projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                              (real_opp (real_plus (cauchy_real_cos x)
                                                   (real_opp (real_mult (cauchy_real_sin x) h)))))) n) _).
          + apply qeq_le.
            rewrite (real_abs_proj
                       (real_plus (cauchy_real_cos (real_plus x h))
                                  (real_opp (real_plus (cauchy_real_cos x)
                                                       (real_opp (real_mult (cauchy_real_sin x) h))))) n).
            apply (Qabs_wd
                     (cn1 - cx + sx * hn)
                     (projT1 (real_plus (cauchy_real_cos (real_plus x h))
                                        (real_opp (real_plus (cauchy_real_cos x)
                                                             (real_opp (real_mult (cauchy_real_sin x) h))))) n)).
            rewrite (real_plus_proj (cauchy_real_cos (real_plus x h))
                                    (real_opp (real_plus (cauchy_real_cos x)
                                                         (real_opp (real_mult (cauchy_real_sin x) h)))) n).
            rewrite (real_opp_proj (real_plus (cauchy_real_cos x)
                                              (real_opp (real_mult (cauchy_real_sin x) h))) n).
            rewrite (real_plus_proj (cauchy_real_cos x)
                                    (real_opp (real_mult (cauchy_real_sin x) h)) n).
            rewrite (real_opp_proj (real_mult (cauchy_real_sin x) h) n).
            rewrite (real_mult_proj (cauchy_real_sin x) h n).
            unfold cn1, cx, sx, hn. ring.
          + exact (HN2 n HnN2).
        - apply qeq_le.
          rewrite (real_plus_proj (real_mult (real_const (epsQ / 4)) (real_abs h))
                                  (real_const (epsQ / 4)) n).
          rewrite (real_mult_proj (real_const (epsQ / 4)) (real_abs h) n).
          rewrite (real_const_proj (epsQ / 4) n).
          rewrite (real_abs_proj h n).
          unfold eps1, hn. ring. }
      (* ③ |sin x·h| 逐点：|sx·hn| ≤ Ms·|hn| *)
      assert (Hnorm : Qle (Qabs (sx * hn)) (Qmult Ms (Qabs hn))).
      { apply (Qle_trans _ (Qmult (Qabs sx) (Qabs hn)) _).
        - apply qeq_le. apply (Qabs_Qmult sx hn).
        - apply (Qmult_le_compat_r (Qabs sx) Ms (Qabs hn)).
          + apply QleT'_to_Qle. apply (HMs n).
          + apply Qabs_nonneg. }
      (* ④ 三角：|An| ≤ |Dn| + |sx·hn|（c1−cx == (D 项) − sx·hn） *)
      assert (Htri : Qle (Qabs (cn1 - cx))
                         (Qplus (Qabs (cn1 - cx + sx * hn))
                                (Qabs (sx * hn)))).
      { apply (Qle_trans _ (Qabs ((cn1 - cx + sx * hn) - sx * hn)) _).
        - apply qeq_le.
          apply (Qabs_wd (cn1 - cx) ((cn1 - cx + sx * hn) - sx * hn)).
          ring.
        - apply (Qle_trans _ (Qplus (Qabs (cn1 - cx + sx * hn))
                                    (Qabs (- (sx * hn)))) _).
          + apply Qabs_triangle.
          + apply Qplus_le_compat.
            * apply Qle_refl.
            * apply qeq_le. apply (Qabs_opp (sx * hn)). }
      (* ⑤ 汇总 *)
      assert (Htot : Qle (Qabs (cn1 - cx))
          (Qplus (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn)) (Qdiv epsQ 4)) eps1)
                 (Qmult Ms (Qabs hn)))).
      { apply (Qle_trans _ (Qplus (Qabs (cn1 - cx + sx * hn))
                                  (Qabs (sx * hn))) _).
        - exact Htri.
        - apply Qplus_le_compat.
          + exact Hdev.
          + exact Hnorm. }
      (* ⑥ ring 重组 *)
      assert (Htot2 : Qle (Qabs (cn1 - cx))
          (Qplus (Qplus (Qdiv epsQ 4) eps1)
                 (Qmult (Qplus (Qdiv epsQ 4) Ms) (Qabs hn)))).
      { apply (Qle_trans _ (Qplus (Qplus (Qplus (Qmult (Qdiv epsQ 4) (Qabs hn))
                                                (Qdiv epsQ 4)) eps1)
                                  (Qmult Ms (Qabs hn))) _).
        - exact Htot.
        - apply qeq_le. ring. }
      (* ⑦ 因子正性 F := epsQ/4 + Ms > 0 *)
      assert (HF0 : Qlt 0 (Qplus (Qdiv epsQ 4) Ms)).
      { apply (Qlt_le_trans 0 (epsQ / 4) (Qplus (Qdiv epsQ 4) Ms)).
        - exact Hq4.
        - apply (Qle_plus_nonneg_r (Qdiv epsQ 4) Ms).
          apply Qlt_le_weak. exact HMs0. }
      (* ⑧ 严格链：F·|h_n| < F·(c−e1) < F·c *)
      assert (Hm_lt : Qlt (Qmult (Qplus (Qdiv epsQ 4) Ms) (Qabs hn))
                          (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1))).
      { apply (proj2 (Qmult_lt_l (Qabs hn) (c - e1)
                                 (Qplus (Qdiv epsQ 4) Ms) HF0)).
        exact Hhnlt. }
      assert (Hcme : Qlt (c - e1) c).
      { apply (proj2 (Qlt_minus_iff (c - e1) c)).
        apply (Qlt_le_trans 0 e1 (Qminus c (Qminus c e1))).
        - exact He1.
        - apply qeq_le. ring. }
      assert (Hm_lt2 : Qlt (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1))
                           (Qmult (Qplus (Qdiv epsQ 4) Ms) c)).
      { apply (proj2 (Qmult_lt_l (c - e1) c
                                 (Qplus (Qdiv epsQ 4) Ms) HF0)).
        exact Hcme. }
      (* ⑨ *)
      assert (Hmid_lt : Qlt (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Ms) (Qabs hn)))
                            (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1)))).
      { apply (proj2 (Qplus_lt_r
                        (Qmult (Qplus (Qdiv epsQ 4) Ms) (Qabs hn))
                        (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1))
                        (Qplus (Qdiv epsQ 4) eps1))).
        exact Hm_lt. }
      assert (Hmid_lt2 : Qlt (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                    (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1)))
                             (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                    (Qmult (Qplus (Qdiv epsQ 4) Ms) c))).
      { apply (proj2 (Qplus_lt_r
                        (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1))
                        (Qmult (Qplus (Qdiv epsQ 4) Ms) c)
                        (Qplus (Qdiv epsQ 4) eps1))).
        exact Hm_lt2. }
      assert (HAn_lt : Qlt (Qabs (cn1 - cx))
                           (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                  (Qmult (Qplus (Qdiv epsQ 4) Ms) c))).
      { apply (Qlt_trans (Qabs (cn1 - cx))
                         (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1)))
                         (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                (Qmult (Qplus (Qdiv epsQ 4) Ms) c))).
        - apply (Qle_lt_trans (Qabs (cn1 - cx))
                              (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                     (Qmult (Qplus (Qdiv epsQ 4) Ms) (Qabs hn)))
                              (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                     (Qmult (Qplus (Qdiv epsQ 4) Ms) (c - e1)))).
          + exact Htot2.
          + exact Hmid_lt.
        - exact Hmid_lt2. }
      (* ⑩ 证毕 *)
      apply (qltT_eq_compat_r
               (projT1 (real_const epsQ) n
                - projT1 (real_abs (real_plus (cauchy_real_cos (real_plus x h))
                                              (real_opp (cauchy_real_cos x)))) n)
               (Qminus epsQ (Qabs (cn1 - cx)))
               (Qdiv epsQ 8)).
      - rewrite (real_const_proj epsQ n).
        rewrite (real_abs_proj (real_plus (cauchy_real_cos (real_plus x h))
                                          (real_opp (cauchy_real_cos x))) n).
        rewrite (real_plus_proj (cauchy_real_cos (real_plus x h))
                                (real_opp (cauchy_real_cos x)) n).
        rewrite (real_opp_proj (cauchy_real_cos x) n).
        unfold cn1, cx. reflexivity.
      - apply Qlt_to_QltT.
        apply (q_lt_minus_shift (Qabs (cn1 - cx)) epsQ (Qdiv epsQ 8)).
        apply (Qlt_le_trans (Qabs (cn1 - cx))
                            (Qplus (Qplus (Qdiv epsQ 4) eps1)
                                   (Qmult (Qplus (Qdiv epsQ 4) Ms) c))
                            (Qminus epsQ (Qdiv epsQ 8))).
        + exact HAn_lt.
        + apply qeq_le.
          unfold c, eps1.
          field.
          all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia).
          all: apply q_neq_of_lt;
               apply (Qlt_le_trans 0 epsQ);
               [ exact HepsQ |
                 apply (q_le_plus_nonneg_r_q epsQ);
                 apply (Qmult_le_0_compat Ms);
                 [ apply Qlt_le_weak; exact HMs0 | unfold Qle; simpl; lia ] ]. } }
Qed.

(* ============================================================ *)
(* B5-B task3 端点装配件            *)
(* （Section B5B_Endpoint：b5b_endpoint / b5b_hsc_theorem，End 泛化 *)
(* 为参数；闭式装配套 b5b_f1_closure（依赖 05/07 块）；9 Qed）；     *)
(* 来源：演变/.ablation/sc2_parallel/sc2_b5b_endpoint/              *)
(*   sc2_b5b_06_endpoint.v（上游双 Require 按规格剥除，块内联）。   *)
(* ============================================================ *)

(* ============ 顶层 Q / Real 辅助（field/ring 安全） ============ *)

(* ---- field 恒等（顶层）：eps/2 + eps/2 == eps（2 ≠ 0） ---- *)
Lemma b5b_ep_half_sum : forall (eps : Q), (eps / 2) + (eps / 2) == eps.
Proof.
  intro eps.
  field.
  all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia).
Qed.

(* ---- 0 < 1/2 ---- *)
Lemma b5b_ep_half_pos : Qlt 0 (1 / 2).
Proof.
  apply (b5b_ecl_div_pos 1 2); unfold Qlt; simpl; lia.
Qed.

(* ---- 1/2 ≤ 1（g ≤ 1/2 ⟹ g ≤ 1 的传递终点） ---- *)
Lemma b5b_ep_half_le_one : Qle (1 / 2) 1.
Proof. unfold Qle. simpl. lia. Qed.

(* ---- g ≤ 1/2 ⟹ 1/2 ≤ 1 − g（差 == 1/2 − g ≥ 0，Qle_minus_iff） ---- *)
Lemma b5b_ep_half_le_1mg : forall (g : Q), Qle g (1 / 2) -> Qle (1 / 2) (1 - g).
Proof.
  intros g Hg.
  apply (proj2 (Qle_minus_iff (1 / 2) (1 - g))).
  assert (Heq : ((1 - g) - 1 / 2) == (1 / 2 - g)).
  { field. all: try (apply q_neq_of_lt; unfold Qlt; simpl; lia). }
  rewrite Heq.
  exact (proj1 (Qle_minus_iff g (1 / 2)) Hg).
Qed.

(* ---- xg := real_const (1−g)：real_lt 0 xg（g ≤ 1/2 ⟹ 0 < 1−g） ---- *)
Lemma b5b_ep_xg_pos : forall (g : Q), Qle g (1 / 2) ->
  real_lt real_zero (real_const (1 - g)).
Proof.
  intros g Hg12.
  apply (real_const_pos_f1 (1 - g)).
  apply (Qlt_le_trans 0 (1 / 2) (1 - g)).
  - exact b5b_ep_half_pos.
  - apply (b5b_ep_half_le_1mg g). exact Hg12.
Qed.

(* ---- xg := real_const (1−g)：real_lt xg (real_const 1)（0 < g） ---- *)
Lemma b5b_ep_xg_lt_one : forall (g : Q), Qlt 0 g ->
  real_lt (real_const (1 - g)) (real_const 1).
Proof.
  intros g Hg.
  apply (real_const_lt (1 - g) 1).
  apply (proj2 (Qlt_minus_iff (1 - g) 1)).
  assert (Heq : (1 - (1 - g)) == g) by ring.
  rewrite Heq. exact Hg.
Qed.

(* ============================================================ *)
(* Section B5B_Endpoint：b5a_E_zero_on_unit（b5a 型）内证毕      *)
(* End 后导出：b5b_endpoint : b5a 型 → E(1)==0；                *)
(*             b5b_hsc_theorem : b5a 型 → Hsc。                 *)
(* ============================================================ *)
Section B5B_Endpoint.

Hypothesis b5a_E_zero_on_unit : forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1) ->
  real_eq (real_E x Hx) real_zero.

Lemma b5b_endpoint : real_eq real_E_one real_zero.
Proof.
  intros epsQ HepsQT.
  assert (HepsQ : Qlt 0 epsQ) by (apply QltT_to_Qlt; exact HepsQT).
  assert (HhalfQ : Qlt 0 (epsQ / 2)) by (apply QltT_to_Qlt; apply q_half_pos; exact HepsQT).
  assert (HhalfT : QltT 0 (epsQ / 2)) by (apply Qlt_to_QltT; exact HhalfQ).
  (* b5b_E_close_q (epsQ/2)：∃N0 g0>0：n≥N0、0<g≤g0 ⟹ |E_n(1−g)−E_n(1)| < epsQ/2 *)
  destruct (b5b_E_close_q (epsQ / 2) HhalfQ) as [N0 [g0 [Hg0pos Hclose]]].
  (* q_arch_inv g0 取 K：a := 1/(K+2) < g0；g := Qmin (1/2) a *)
  destruct (q_arch_inv g0 (QltT_to_Qlt 0 g0 Hg0pos)) as [K HK].
  set (a := 1 / (Z.of_nat (K + 2) # 1)).
  set (g := Qmin (1 / 2) a).
  assert (Ha0 : Qlt 0 a).
  { unfold a. exact (q_arch_inv_pos K). }
  assert (Hg0 : Qlt 0 g).
  { unfold g. apply (b5b_ecl_min_pos (1 / 2) a); [exact b5b_ep_half_pos | exact Ha0]. }
  assert (Hg0le : Qle 0 g) by (apply (Qlt_le_weak 0 g); exact Hg0).
  assert (Hg_le_half : Qle g (1 / 2)).
  { unfold g. exact (Q.le_min_l (1 / 2) a). }
  assert (Hg_le_a : Qle g a).
  { unfold g. exact (Q.le_min_r (1 / 2) a). }
  assert (Ha_g0 : Qle a g0).
  { apply (Qlt_le_weak a g0). unfold a. exact HK. }
  assert (Hg_g0 : Qle g g0).
  { apply (Qle_trans _ a _); [exact Hg_le_a | exact Ha_g0]. }
  assert (Hg1 : Qle g 1).
  { apply (Qle_trans _ (1 / 2) _); [exact Hg_le_half | exact b5b_ep_half_le_one]. }
  (* xg := real_const (1−g)；域证书 Hxg；开区间序 Hxg0/Hxg1 *)
  set (xg := real_const (1 - g)).
  assert (Hxg : cw_unit xg).
  { unfold xg. apply (b5b_unit_const g Hg0le Hg1). }
  assert (Hxg0 : real_lt real_zero xg).
  { unfold xg. apply (b5b_ep_xg_pos g Hg_le_half). }
  assert (Hxg1 : real_lt xg (real_const 1)).
  { unfold xg. apply (b5b_ep_xg_lt_one g Hg0). }
  (* b5a 假设实例化：Hz0 := real_eq (real_E xg Hxg) real_zero；取 Nz *)
  assert (Hz0 : real_eq (real_E xg Hxg) real_zero).
  { exact (b5a_E_zero_on_unit xg Hxg Hxg0 Hxg1). }
  destruct (Hz0 (epsQ / 2) HhalfT) as [Nz HNz].
  (* 模：N := max(N0, Nz) *)
  exists (Nat.max N0 Nz).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (HnN0 : (N0 <= n)%nat) by lia.
  assert (HnNz : (Nz <= n)%nat) by lia.
  (* ① |E1_n − Eg_n| < epsQ/2：b5b_En_proj 桥 + b5b_E_close_q *)
  assert (Hq1eq : (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                  (b5b_En n 1 - b5b_En n (1 - g))).
  { unfold real_E_one.
    rewrite (b5b_En_proj (real_const 1) atan1_pt_bound n).
    rewrite (b5b_En_proj xg Hxg n).
    unfold xg.
    (* projT1 (real_const c) k 与 c 定义性相等（real_const_proj 由
       reflexivity 证明），此处不可在 b5b_En 参数内 setoid 重写
       （b5b_En 无 Qeq Proper 实例），靠 kernel 转换 reflexivity 收。 *)
    reflexivity. }
  assert (Hq1abs : Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n) ==
                   Qabs (b5b_En n (1 - g) - b5b_En n 1)).
  { apply (Qeq_trans _ (Qabs (b5b_En n 1 - b5b_En n (1 - g))) _).
    - apply (Qabs_wd (projT1 real_E_one n - projT1 (real_E xg Hxg) n)
                     (b5b_En n 1 - b5b_En n (1 - g))).
      exact Hq1eq.
    - apply (q_abs_minus_sym (b5b_En n 1) (b5b_En n (1 - g))). }
  assert (Hterm1T : QltT (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                         (epsQ / 2)).
  { apply (qltT_eq_compat_l (Qabs (b5b_En n (1 - g) - b5b_En n 1))
                            (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (epsQ / 2)).
    - apply Qeq_sym. exact Hq1abs.
    - apply Qlt_to_QltT.
      exact (Hclose n g (NatLe_lift _ _ HnN0) Hg0 Hg_g0). }
  assert (Hterm1 : Qlt (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm1T).
  (* ② |Eg_n − 0_n| < epsQ/2：Hz（real_eq (E xg) 0）逐点 *)
  assert (Hterm2T : QltT (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                         (epsQ / 2)).
  { exact (HNz n (NatLe_lift _ _ HnNz)). }
  assert (Hterm2 : Qlt (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                       (epsQ / 2))
    by (apply QltT_to_Qlt; exact Hterm2T).
  (* 三角：|E1_n − 0_n| ≤ |E1_n − Eg_n| + |Eg_n − 0_n| *)
  assert (Htri : Qle (Qabs (projT1 real_E_one n - projT1 real_zero n))
                     (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))).
  { apply (Qle_trans _
             (Qabs ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                    (projT1 (real_E xg Hxg) n - projT1 real_zero n))) _).
    - apply qeq_le.
      apply (Qabs_wd (projT1 real_E_one n - projT1 real_zero n)
                     ((projT1 real_E_one n - projT1 (real_E xg Hxg) n) +
                      (projT1 (real_E xg Hxg) n - projT1 real_zero n))).
      ring.
    - apply Qabs_triangle. }
  (* 两项和 < epsQ/2 + epsQ/2 == epsQ *)
  assert (Hsum : Qlt (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                            (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                     (Qplus (epsQ / 2) (epsQ / 2))).
  { apply (Qplus_lt_compat (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                           (epsQ / 2)
                           (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n))
                           (epsQ / 2)).
    - exact Hterm1.
    - exact Hterm2. }
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (projT1 real_E_one n - projT1 real_zero n))
                      (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                             (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                      epsQ).
  - exact Htri.
  - apply (Qlt_le_trans (Qplus (Qabs (projT1 real_E_one n - projT1 (real_E xg Hxg) n))
                               (Qabs (projT1 (real_E xg Hxg) n - projT1 real_zero n)))
                        (Qplus (epsQ / 2) (epsQ / 2)) epsQ).
    + exact Hsum.
    + apply qeq_le. exact (b5b_ep_half_sum epsQ).
Qed.

Lemma b5b_hsc_theorem : real_eq (cauchy_real_sin arctan_one_real)
                                (cauchy_real_cos arctan_one_real).
Proof.
  apply b5b_hsc_main.
  exact b5b_endpoint.
Qed.

End B5B_Endpoint.
Lemma b5b_f1_closure' :
  (forall (x : Real) (Hx : cw_unit x),
    real_lt real_zero x -> real_lt x (real_const 1) ->
    real_eq (real_E x Hx) real_zero) ->
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  intro H.
  apply b6_f1_template.
  apply b5b_hsc_theorem.
  exact H.
Qed.

(* ============================================================ *)
(* B5-A item1b 主装配（对应 Section *)
(* B5A_Item1B：Variable real_arctan_deriv，End 泛化为参数；24 件，  *)
(* 16 整行 Qed，含 b5a_sin_atan_diff；BAD 0）。来源：                *)
(* 演变/.ablation/sc2_parallel/sc2_b5a_ode/sc2_b5a_item1b.v；        *)
(* 注：本块用 Q 域 nra——由 Lqa 供给（AA6 裁定 Psatz→Lqa）。    *)
(* 中段 Require 先例见根 L3069。                                    *)
(* ============================================================ *)

From Stdlib Require Import Lqa.
(* ============================================================ *)
(* U2 对应 Section：arctan' 条件件（B3 形态；上游根件同款规格）  *)
(* ============================================================ *)
Section B5A_Item1B.

Variable real_arctan_deriv :
  forall (x : Real) (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real =>
    And (real_lt real_zero delta)
        (forall (h : Real), real_lt (real_abs h) delta ->
          forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                     (real_opp (real_plus (cauchy_real_arctan x Hx)
                                (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                        (b5a_one_plus_sq_pos x)) h)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* Part A：Q 预算件（纯 Q；nra 禁跨乘；q_le_div_le 证毕）        *)
(* 约定：S > 0、Mc ≥ 0、K1 ≥ 0；                               *)
(*   kδ := Qinv(512(S+1))                                      *)
(*   k2 := Qinv(512(S+1)(3S+Mc+1))                             *)
(*   k2p := Qinv(1024(K1+1)(3S+Mc+1))                          *)
(* 需要界（目标均为规范 (1#N)）：                               *)
(*   B1 2S·kδ ≤ (1#2)   B2 (3S+Mc)k2 ≤ (1#2)                   *)
(*   B3 Mc·k2 ≤ (1#2)   B4 (3S+Mc)·2k2p ≤ (1#32)               *)
(*   B5 Mc·2k2p ≤ (1#32)                                        *)
(*   B6 4k2p·K1 ≤ (1#256)（crude 强制用）                       *)
(*   B7 消去、B8 半化                                       *)
(* ============================================================ *)

(* 跨乘：x·c ≤ D（D,c>0）⟹ x·Qinv D ≤ Qinv c *)
Lemma b5n_xinv_le : forall (x D c : Q),
  Qlt 0 D -> Qlt 0 c -> Qle (Qmult x c) D ->
  Qle (Qmult x (Qinv D)) (Qinv c).
Proof.
  intros x D c HD Hc Hx.
  apply (Qle_trans (Qmult x (Qinv D)) (Qdiv x D) (Qinv c)).
  { apply qeq_imp_qle. unfold Qdiv. reflexivity. }
  { apply (Qle_trans (Qdiv x D) (Qdiv 1 c) (Qinv c)).
    { apply (q_le_div_le x D 1 c).
      { exact HD. }
      { exact Hc. }
      { apply (Qle_trans (Qmult x c) D (Qmult 1 D)).
        { exact Hx. }
        { apply qeq_imp_qle. ring. } } }
    { apply qeq_imp_qle. unfold Qdiv. ring. } }
Qed.

(* B1：2S·kδ ≤ (1#2)；kδ := Qinv(512(S+1)) *)
Lemma b5n_2S_kδ_le : forall (S : Q), Qlt 0 S ->
  Qle (Qmult (Qmult 2 S) (Qinv (Qmult 512 (Qplus S 1)))) (1 # 2).
Proof.
  intros S HS.
  apply (Qle_trans (Qmult (Qmult 2 S) (Qinv (Qmult 512 (Qplus S 1))))
                   (Qinv 2)
                   (1 # 2)).
  { apply (b5n_xinv_le (Qmult 2 S) (Qmult 512 (Qplus S 1)) 2).
    { nra. }
    { unfold Qlt. simpl. lia. }
    { nra. } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B2：(3S+Mc)·k2 ≤ (1#2)；k2 := Qinv(512(S+1)(3S+Mc+1)) *)
Lemma b5n_3S_Mc_k2_le : forall (S Mc : Q), Qlt 0 S -> Qle 0 Mc ->
  Qle (Qmult (Qplus (Qmult 3 S) Mc)
             (Qinv (Qmult (Qmult 512 (Qplus S 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))))
      (1 # 2).
Proof.
  intros S Mc HS HMc.
  apply (Qle_trans (Qmult (Qplus (Qmult 3 S) Mc)
                          (Qinv (Qmult (Qmult 512 (Qplus S 1))
                                       (Qplus (Qplus (Qmult 3 S) Mc) 1))))
                   (Qinv 2)
                   (1 # 2)).
  { apply (b5n_xinv_le (Qplus (Qmult 3 S) Mc)
                       (Qmult (Qmult 512 (Qplus S 1))
                              (Qplus (Qplus (Qmult 3 S) Mc) 1))
                       2).
    { nra. }
    { unfold Qlt. simpl. lia. }
    { nra. } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B3：Mc·k2 ≤ (1#2) *)
Lemma b5n_Mc_k2_le : forall (S Mc : Q), Qlt 0 S -> Qle 0 Mc ->
  Qle (Qmult Mc
             (Qinv (Qmult (Qmult 512 (Qplus S 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))))
      (1 # 2).
Proof.
  intros S Mc HS HMc.
  apply (Qle_trans (Qmult Mc
                          (Qinv (Qmult (Qmult 512 (Qplus S 1))
                                       (Qplus (Qplus (Qmult 3 S) Mc) 1))))
                   (Qinv 2)
                   (1 # 2)).
  { apply (b5n_xinv_le Mc
                       (Qmult (Qmult 512 (Qplus S 1))
                              (Qplus (Qplus (Qmult 3 S) Mc) 1))
                       2).
    { nra. }
    { unfold Qlt. simpl. lia. }
    { nra. } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B4：(3S+Mc)·2k2p ≤ (1#32)；k2p := Qinv(1024(K1+1)(3S+Mc+1)) *)
Lemma b5n_3S_Mc_2k2p_le : forall (S Mc K1 : Q), Qlt 0 S -> Qle 0 Mc -> Qle 0 K1 ->
  Qle (Qmult (Qplus (Qmult 3 S) Mc)
             (Qmult 2 (Qinv (Qmult (Qmult 1024 (Qplus K1 1))
                                   (Qplus (Qplus (Qmult 3 S) Mc) 1)))))
      (1 # 32).
Proof.
  intros S Mc K1 HS HMc HK1.
  set (D := Qmult (Qmult 1024 (Qplus K1 1)) (Qplus (Qplus (Qmult 3 S) Mc) 1)).
  apply (Qle_trans (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 (Qinv D)))
                   (Qinv 32)
                   (1 # 32)).
  { apply (Qle_trans (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 (Qinv D)))
                     (Qmult (Qmult (Qplus (Qmult 3 S) Mc) 2) (Qinv D))
                     (Qinv 32)).
    { apply qeq_imp_qle. ring. }
    { apply (b5n_xinv_le (Qmult (Qplus (Qmult 3 S) Mc) 2) D 32).
      { unfold D. nra. }
      { unfold Qlt. simpl. lia. }
      { unfold D. nra. } } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B5：Mc·2k2p ≤ (1#32) *)
Lemma b5n_Mc_2k2p_le : forall (S Mc K1 : Q), Qlt 0 S -> Qle 0 Mc -> Qle 0 K1 ->
  Qle (Qmult Mc
             (Qmult 2 (Qinv (Qmult (Qmult 1024 (Qplus K1 1))
                                   (Qplus (Qplus (Qmult 3 S) Mc) 1)))))
      (1 # 32).
Proof.
  intros S Mc K1 HS HMc HK1.
  set (D := Qmult (Qmult 1024 (Qplus K1 1)) (Qplus (Qplus (Qmult 3 S) Mc) 1)).
  apply (Qle_trans (Qmult Mc (Qmult 2 (Qinv D)))
                   (Qinv 32)
                   (1 # 32)).
  { apply (Qle_trans (Qmult Mc (Qmult 2 (Qinv D)))
                     (Qmult (Qmult Mc 2) (Qinv D))
                     (Qinv 32)).
    { apply qeq_imp_qle. ring. }
    { apply (b5n_xinv_le (Qmult Mc 2) D 32).
      { unfold D. nra. }
      { unfold Qlt. simpl. lia. }
      { unfold D. nra. } } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B6：4k2p·K1 ≤ (1#256)（crude 强制 K1 ≤ en'/2 用） *)
Lemma b5n_4k2p_K1_le : forall (S Mc K1 : Q), Qlt 0 S -> Qle 0 Mc -> Qle 0 K1 ->
  Qle (Qmult (Qmult 4 (Qinv (Qmult (Qmult 1024 (Qplus K1 1))
                                   (Qplus (Qplus (Qmult 3 S) Mc) 1))))
             K1)
      (1 # 256).
Proof.
  intros S Mc K1 HS HMc HK1.
  set (D := Qmult (Qmult 1024 (Qplus K1 1)) (Qplus (Qplus (Qmult 3 S) Mc) 1)).
  apply (Qle_trans (Qmult (Qmult 4 (Qinv D)) K1)
                   (Qinv 256)
                   (1 # 256)).
  { apply (Qle_trans (Qmult (Qmult 4 (Qinv D)) K1)
                     (Qmult (Qmult K1 4) (Qinv D))
                     (Qinv 256)).
    { apply qeq_imp_qle. ring. }
    { apply (b5n_xinv_le (Qmult K1 4) D 256).
      { unfold D. nra. }
      { unfold Qlt. simpl. lia. }
      { unfold D. nra. } } }
  { apply qeq_imp_qle. unfold Qinv. reflexivity. }
Qed.

(* B7：正因子消去：c>0、a·c ≤ b·c ⟹ a ≤ b *)
Lemma b5n_qle_mult_cancel : forall (a b c : Q), Qlt 0 c ->
  Qle (Qmult a c) (Qmult b c) -> Qle a b.
Proof. intros. nra. Qed.

(* B8：2a ≤ b ⟹ a ≤ b·(1#2) *)
Lemma b5n_half_le : forall (a b : Q), Qle (Qmult 2 a) b -> Qle a (Qmult (1 # 2) b).
Proof. intros. nra. Qed.

(* B6b：8k2p·K1 ≤ 1（crude 强制 K1 ≤ en'/2 的替代界） *)
Lemma b5n_8k2p_K1_le : forall (S Mc K1 : Q), Qlt 0 S -> Qle 0 Mc -> Qle 0 K1 ->
  Qle (Qmult (Qmult 8 (Qinv (Qmult (Qmult 1024 (Qplus K1 1))
                                   (Qplus (Qplus (Qmult 3 S) Mc) 1))))
             K1)
      1.
Proof.
  intros S Mc K1 HS HMc HK1.
  set (D := Qmult (Qmult 1024 (Qplus K1 1)) (Qplus (Qplus (Qmult 3 S) Mc) 1)).
  apply (Qle_trans (Qmult (Qmult 8 (Qinv D)) K1)
                   (Qmult K1 (Qmult 8 (Qinv D)))
                   1).
  { apply qeq_imp_qle. ring. }
  { apply (Qle_trans (Qmult K1 (Qmult 8 (Qinv D)))
                     (Qinv 1)
                     1).
    { apply (Qle_trans (Qmult K1 (Qmult 8 (Qinv D)))
                       (Qmult (Qmult K1 8) (Qinv D))
                       (Qinv 1)).
      { apply qeq_imp_qle. ring. }
      { apply (b5n_xinv_le (Qmult K1 8) D 1).
        { unfold D. nra. }
        { unfold Qlt. simpl. lia. }
        { unfold D. nra. } } }
    { apply qeq_imp_qle. unfold Qinv. simpl. reflexivity. } }
Qed.

(* crude 强制：E2 = 2k2p·en' ≥ 1/2 且 8k2p·K1 ≤ 1、4k2p·en' > 1
   ⟹ K1 ≤ (1#2)·en' *)
Lemma b5n_force_half : forall (K1 k2p en' : Q),
  Qlt 0 k2p ->
  Qle (Qmult (Qmult 8 k2p) K1) 1 ->
  Qlt 1 (Qmult (Qmult 4 k2p) en') ->
  Qle K1 (Qmult (1 # 2) en').
Proof.
  intros K1 k2p en' Hk2p Hbud Hbig.
  (* 8k2p·K1 ≤ 1 < 4k2p·en' ⟹ 8k2pK1 ≤ 4k2p·en' *)
  assert (Hc : Qle (Qmult (Qmult 8 k2p) K1) (Qmult (Qmult 4 k2p) en')).
  { apply (Qle_trans (Qmult (Qmult 8 k2p) K1) 1 (Qmult (Qmult 4 k2p) en')).
    { exact Hbud. }
    { apply Qlt_le_weak. exact Hbig. } }
  (* (2K1)·(4k2p) == 8k2p·K1；cancel 4k2p *)
  assert (Hc2 : Qle (Qmult (Qmult 4 k2p) (Qmult 2 K1))
                    (Qmult (Qmult 4 k2p) en')).
  { apply (Qle_trans (Qmult (Qmult 4 k2p) (Qmult 2 K1))
                     (Qmult (Qmult 8 k2p) K1)
                     (Qmult (Qmult 4 k2p) en')).
    { apply qeq_imp_qle. ring. }
    { exact Hc. } }
  assert (H4p : Qlt 0 (Qmult 4 k2p)).
  { apply (Qmult_lt_0_compat 4 k2p).
    { unfold Qlt. simpl. lia. }
    { exact Hk2p. } }
  assert (H2K1 : Qle (Qmult 2 K1) en').
  { apply (b5n_qle_mult_cancel (Qmult 2 K1) en' (Qmult 4 k2p)).
    { exact H4p. }
    { apply (Qle_trans (Qmult (Qmult 2 K1) (Qmult 4 k2p))
                       (Qmult (Qmult 4 k2p) (Qmult 2 K1))
                       (Qmult en' (Qmult 4 k2p))).
      { apply qeq_imp_qle. ring. }
      { apply (Qle_trans (Qmult (Qmult 4 k2p) (Qmult 2 K1))
                         (Qmult (Qmult 4 k2p) en')
                         (Qmult en' (Qmult 4 k2p))).
        { exact Hc2. }
        { apply qeq_imp_qle. ring. } } } }
  apply (b5n_half_le K1 en').
  exact H2K1.
Qed.

(* 逐点三角：|v| ≤ |v−dh| + |dh|（dh 任意 Q 原子） *)
Lemma b5n_abs_sub_add : forall (v dh : Q),
  Qle (Qabs v) (Qplus (Qabs (Qminus v dh)) (Qabs dh)).
Proof.
  intros v dh.
  apply (Qle_trans (Qabs v)
                   (Qabs (Qplus (Qminus v dh) dh))
                   (Qplus (Qabs (Qminus v dh)) (Qabs dh))).
  { apply qeq_imp_qle. apply Qabs_wd. ring. }
  { apply Qabs_triangle. }
Qed.


(* crude E2 强制：|v|>1、|v|≤|w|+|h|、|h|≤1/4、|w|≤enk2h+E2、enk2h≤1/4
   ⟹ E2 ≥ 1/2 *)
Lemma b5n_forceE2 : forall (av aw ah enk2ah E2 : Q),
  Qlt 1 av -> Qle av (Qplus aw ah) ->
  Qle ah (1 # 4) ->
  Qle aw (Qplus enk2ah E2) ->
  Qle enk2ah (1 # 4) ->
  Qle (1 # 2) E2.
Proof. intros. nra. Qed.

(* E2 = 2k2p·en' 且 E2 ≥ 1/2 ⟹ 4k2p·en' ≥ 1 *)
Lemma b5n_forceE2en : forall (E2 k2p en' : Q),
  Qle (1 # 2) E2 ->
  E2 == Qmult (Qmult 2 k2p) en' ->
  Qle 1 (Qmult (Qmult 4 k2p) en').
Proof. intros. nra. Qed.

(* 8k2p·K1 ≤ 1、4k2p·en' ≥ 1 ⟹ 2K1 ≤ en' ⟹ K1 ≤ en'/2 *)
Lemma b5n_forceK1 : forall (K1 k2p en' : Q),
  Qlt 0 k2p ->
  Qle (Qmult (Qmult 8 k2p) K1) 1 ->
  Qle 1 (Qmult (Qmult 4 k2p) en') ->
  Qle K1 (Qmult (1 # 2) en').
Proof.
  intros K1 k2p en' Hk2p Hbud Hbig.
  assert (H4p : Qlt 0 (Qmult 4 k2p)) by nra.
  assert (Hc : Qle (Qmult (Qmult 8 k2p) K1) (Qmult (Qmult 4 k2p) en')).
  { apply (Qle_trans (Qmult (Qmult 8 k2p) K1) 1 (Qmult (Qmult 4 k2p) en')).
    { exact Hbud. }
    { exact Hbig. } }
  assert (Hc2 : Qle (Qmult (Qmult 2 K1) (Qmult 4 k2p))
                    (Qmult en' (Qmult 4 k2p))).
  { apply (Qle_trans (Qmult (Qmult 2 K1) (Qmult 4 k2p))
                     (Qmult (Qmult 8 k2p) K1)
                     (Qmult en' (Qmult 4 k2p))).
    { apply qeq_imp_qle. ring. }
    { apply (Qle_trans (Qmult (Qmult 8 k2p) K1)
                       (Qmult (Qmult 4 k2p) en')
                       (Qmult en' (Qmult 4 k2p))).
      { exact Hc. }
      { apply qeq_imp_qle. ring. } } }
  assert (H2K1 : Qle (Qmult 2 K1) en').
  { apply (b5n_qle_mult_cancel (Qmult 2 K1) en' (Qmult 4 k2p)).
    { exact H4p. }
    { exact Hc2. } }
  apply (b5n_half_le K1 en').
  exact H2K1.
Qed.

(* 吸收（quad）：coef·X ≤ X 且 colQ ≤ en'/8、cE·E2 ≤ en'/32
   ⟹ colQ + coef·X + cE·E2 ≤ X + (5/32)en' ≤ X + (3/4)en' *)
Lemma b5n_absorbQ : forall (colQ coef X cE E2 en' : Q),
  Qle 0 X -> Qle 0 en' -> Qle coef 1 ->
  Qle colQ (Qmult (1 # 8) en') ->
  Qle (Qmult cE E2) (Qmult (1 # 32) en') ->
  Qle (Qplus colQ (Qplus (Qmult coef X) (Qmult cE E2)))
      (Qplus X (Qmult (3 # 4) en')).
Proof. intros. nra. Qed.

(* 吸收（crude）：Mc·k2·X ≤ X（k2·Mc ≤ 1）且 colQ ≤ en'/8、
   K1 ≤ en'/2、Mc·E2 ≤ en'/32 ⟹ 全式 ≤ X + (3/4)en' *)
Lemma b5n_absorbC : forall (colQ K1 Mc E2 X en' : Q) (k2 : Q),
  Qle 0 X -> Qle 0 en' -> Qle (Qmult Mc k2) 1 ->
  Qle colQ (Qmult (1 # 8) en') ->
  Qle K1 (Qmult (1 # 2) en') ->
  Qle (Qmult Mc E2) (Qmult (1 # 32) en') ->
  Qle (Qplus colQ (Qplus K1 (Qplus (Qmult (Qmult Mc k2) X) (Qmult Mc E2))))
      (Qplus X (Qmult (3 # 4) en')).
Proof. intros. nra. Qed.

(* margin：D ≤ A + (3/4)e' 且 eta < (1/4)e' ⟹ eta < (A+e') − D *)
Lemma b5n_close : forall (D hn en en' eta : Q),
  Qle D (Qplus (Qmult en hn) (Qmult (3 # 4) en')) ->
  Qlt eta (Qmult (1 # 4) en') ->
  Qlt eta (Qminus (Qplus (Qmult en hn) en') D).
Proof. intros. nra. Qed.

(* eps1' > 0、en' > eps1' ⟹ (1/8)eps1' < (1/4)en' *)
Lemma b5n_quarter_gt : forall (e1 e : Q),
  Qlt 0 e1 -> Qlt e1 e -> Qlt (Qmult (1 # 8) e1) (Qmult (1 # 4) e).
Proof. intros. nra. Qed.

(* |h_n| 的 |dh| 界与 |v−dh| 界给出 av ≤ aw+ah 的副产品（供 crude）不另需 *)
(* ============================================================ *)
(* Part B：逐点提取 X：给定 |h| < eps·rkδ、|h| < const(1#2)、    *)
(*   |h| < (1#4)·inv_pos(1+eps2)（eps2 := eps·rk2），           *)
(*   ⟹ ∃N ∀n≥N：|h_n| ≤ en·kδ ∧ |h_n| ≤ 1/2 ∧                  *)
(*              (1+en·k2)·|h_n| ≤ 1/4                          *)
(* ============================================================ *)
Lemma b5n_h_pts : forall (h eps : Real) (kδ k2 : Q)
  (Heps : real_lt real_zero eps),
  QltT 0 kδ -> forall (Hk2 : QltT 0 k2),
  real_lt (real_abs h) (real_mult eps (real_const kδ)) ->
  real_lt (real_abs h) (real_const (1 # 2)) ->
  real_lt (real_abs h)
          (real_mult (real_const (1 # 4))
                     (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                   (b5i_one_plus_eps2_pos eps k2 Heps Hk2))) ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    And (QleT' (Qabs (projT1 h n)) (Qmult (projT1 eps n) kδ))
    (And (QleT' (Qabs (projT1 h n)) (1 # 2))
         (QleT' (Qmult (Qplus 1 (Qmult (projT1 eps n) k2)) (Qabs (projT1 h n))) (1 # 4)))).
Proof.
  intros h eps kδ k2 Heps Hkδ Hk2 Hhδ Hh12 Hhq.
  destruct (b5i_h_le_enk h eps kδ Hhδ Hkδ) as [N1 HN1].
  assert (Hc12 : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5i_h_le_const h (1 # 2) Hh12 Hc12) as [N2 HN2].
  destruct (b5i_h_inv_quarter h (real_mult eps (real_const k2))
             (b5i_one_plus_eps2_pos eps k2 Heps Hk2) Hhq) as [N3 HN3].
  exists (Nat.max (Nat.max N1 N2) N3).
  intros n Hn.
  apply NatLe_drop in Hn.
  assert (Hn1 : NatLe N1 n) by (apply NatLe_lift; lia).
  assert (Hn2 : NatLe N2 n) by (apply NatLe_lift; lia).
  assert (Hn3 : NatLe N3 n) by (apply NatLe_lift; lia).
  split.
  - exact (Qle_to_QleT' _ _ (HN1 n Hn1)).
  - split.
    + exact (Qle_to_QleT' _ _ (HN2 n Hn2)).
    + apply Qle_to_QleT'. apply (Qle_trans (Qmult (Qplus 1 (Qmult (projT1 eps n) k2)) (Qabs (projT1 h n)))
                       (Qmult (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
                              (Qabs (projT1 h n)))
                       (1 # 4)).
      * apply qeq_imp_qle.
        apply Qmult_comp.
        -- setoid_rewrite (real_plus_proj real_one (real_mult eps (real_const k2)) n).
           setoid_rewrite (real_mult_proj eps (real_const k2) n).
           rewrite (real_const_proj k2 n).
           cbn [projT1 real_one].
           ring.
        -- reflexivity.
      * exact (HN3 n Hn3).
Qed.

(* ============================================================ *)
(* Part C：逐点提取 Y：arctan'-Var 于 eps2 := eps·rk2、          *)
(*   eps2' := eps'·rk2p 实例化 ⟹ ∃δa 0<δa：                    *)
(*   ∀h |h|<δa → ∀Hxh ∀eps' 0<eps'：∃N ∀n≥N：                   *)
(*   |v_n − d_n·h_n| ≤ (en·k2)·|h_n| + 2·k2p·en'                 *)
(*   （b5i_abs_le_pointwise + b5i_vdh_absV + 投影 ring）          *)
(* ============================================================ *)
Lemma b5n_vdh_pts : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (eps : Real) (Heps : real_lt real_zero eps)
  (k2 k2p : Q) (Hk2 : QltT 0 k2) (Hk2p : QltT 0 k2p),
  sigT (fun δa : Real => And (real_lt real_zero δa)
    (forall (h : Real), real_lt (real_abs h) δa ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      sigT (fun N : nat => forall n : nat, NatLe N n ->
        Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
            (Qplus (Qmult (Qmult (projT1 eps n) k2) (Qabs (projT1 h n)))
                   (Qmult (Qmult 2 k2p) (projT1 eps' n)))))).
Proof.
  intros x Hx eps Heps k2 k2p Hk2 Hk2p.
  set (eps2 := real_mult eps (real_const k2)).
  assert (Heps2 : real_lt real_zero eps2).
  { unfold eps2. apply real_mult_positive.
    - exact Heps.
    - apply real_const_pos. exact Hk2. }
  destruct (real_arctan_deriv x Hx eps2 Heps2) as [δa [Hδa0 Hδa]].
  exists δa.
  split.
  - exact Hδa0.
  - intros h Hhδ Hxh eps' Heps'.
    set (eps2' := real_mult eps' (real_const k2p)).
    assert (Heps2' : real_lt real_zero eps2').
    { unfold eps2'. apply real_mult_positive.
      - exact Heps'.
      - apply real_const_pos. exact Hk2p. }
    set (V := real_plus (cauchy_real_arctan (real_plus x h) Hxh)
                (real_opp (real_plus (cauchy_real_arctan x Hx)
                           (real_mult (real_inv_pos (real_plus real_one (real_mult x x))
                                                     (b5a_one_plus_sq_pos x)) h)))).
    assert (Habs : real_le (real_abs V)
                    (real_plus (real_mult eps2 (real_abs h)) eps2')).
    { unfold V, eps2, eps2'.
      exact (Hδa h Hhδ Hxh (real_mult eps' (real_const k2p)) Heps2'). }
    destruct (b5i_abs_le_pointwise V (real_plus (real_mult eps2 (real_abs h)) eps2')
               Habs eps2' Heps2') as [N HN].
    exists N.
    intros n Hn.
    set (en := projT1 eps n).
    set (en' := projT1 eps' n).
    set (hn := projT1 h n).
    assert (Hpt : Qle (Qabs (projT1 V n))
                      (Qplus (Qmult (Qmult en k2) (Qabs hn))
                             (Qmult (Qmult 2 k2p) en'))).
    { apply (Qle_trans (Qabs (projT1 V n))
                       (Qplus (projT1 (real_plus (real_mult eps2 (real_abs h)) eps2') n)
                              (projT1 eps2' n))
                       (Qplus (Qmult (Qmult en k2) (Qabs hn))
                              (Qmult (Qmult 2 k2p) en'))).
      - exact (HN n Hn).
      - apply qeq_imp_qle.
        setoid_rewrite (real_plus_proj (real_mult eps2 (real_abs h)) eps2' n).
        setoid_rewrite (real_mult_proj eps2 (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        unfold eps2, eps2'.
        setoid_rewrite (real_mult_proj eps (real_const k2) n).
        rewrite (real_const_proj k2 n).
        setoid_rewrite (real_mult_proj eps' (real_const k2p) n).
        rewrite (real_const_proj k2p n).
        cbn [projT1].
        unfold en, en', hn.
        ring. }
    (* V 的 proj 与 b5i_vdh_absV 的 proj 定义性同（b5a_atan_d 展开） *)
    apply (b5i_vdh_absV x Hx h Hxh n
             (Qplus (Qmult (Qmult en k2) (Qabs hn))
                    (Qmult (Qmult 2 k2p) en'))).
    unfold b5a_atan_d, V in Hpt.
    exact Hpt.
Qed.



(* ============================================================ *)
(* Part D：per-n 双分支主界（Z）                                 *)
(*   外层谓词输入：每 n 的逐点事实与预算（由 W 用 X/Y/根件填入）  *)
(*   结论：|D_n| ≤ en·|h_n| + (3/4)·en'                         *)
(* ============================================================ *)
Lemma b5n_pern_main : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1)
  (h : Real) (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1)
  (n : nat)
  (Ms Mc C4 colQ kδ k2 k2p : Q) (en en' : Q),
  Qle (Qabs (sin_partial n (b5i_An x n))) Ms ->
  Qle (Qabs (cos_partial n (b5i_An x n))) Mc ->
  (forall j : nat, QleT' (exp_series j 4) C4) -> Qle 0 C4 ->
  QltT (b5i_addcol_sin x h Hxh n) colQ ->
  Qle (Qabs (projT1 h n)) (Qmult en kδ) ->
  Qle (Qabs (projT1 h n)) (1 # 2) ->
  Qle (Qmult (Qplus 1 (Qmult en k2)) (Qabs (projT1 h n))) (1 # 4) ->
  Qle (Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n))))
      (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n)))
             (Qmult (Qmult 2 k2p) en')) ->
  Qle (Qabs (b5i_dn x n)) 1 ->
  Qle 0 en -> Qle 0 en' -> Qle 0 k2 -> Qlt 0 k2p ->
  Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1 ->
  Qle (Qmult Mc k2) 1 ->
  Qle colQ (Qmult (1 # 8) en') ->
  Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
             (Qmult (Qmult 2 k2p) en')) (Qmult (1 # 32) en') ->
  Qle (Qmult Mc (Qmult (Qmult 2 k2p) en')) (Qmult (1 # 32) en') ->
  Qle (Qmult (Qmult 8 k2p)
             (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1 ->
  Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
      (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en')).
Proof.
  intros x Hx h Hxh n Ms Mc C4 colQ kδ k2 k2p en en'
         HMs HMc HC4 HC40 Hcol Hhδ Hh12 Hq Hw Hd1
         Hen0 Hen'0 Hk20 Hk2p HcoefQ HcoefC HcolQ8
         HaddQ32 HaddC32 Hk2pK1.
  set (E2 := Qmult (Qmult 2 k2p) en').
  set (S := Qplus Ms Mc).
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  set (X := Qmult en (Qabs (projT1 h n))).
  assert (HX0 : Qle 0 X).
  { unfold X. apply (Qmult_le_0_compat en (Qabs (projT1 h n)) Hen0 (Qabs_nonneg (projT1 h n))). }
  assert (HE20 : Qle 0 E2).
  { unfold E2. apply (Qmult_le_0_compat (Qmult 2 k2p) en').
    { apply (Qmult_le_0_compat 2 k2p).
      { unfold Qle. simpl. lia. }
      { apply Qlt_le_weak. exact Hk2p. } }
    { exact Hen'0. } }
  destruct (b5i_qle_dec (Qabs (b5i_vn x h n)) 1) as [Hv1 | Hvbig].
  { apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                     (Qplus colQ
                            (Qplus (Qmult (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                                                 (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                                          (Qmult en (Qabs (projT1 h n))))
                                   (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) E2)))
                     (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
    { apply (b5i_pern_quad x Hx h Hxh n Ms Mc colQ kδ k2 en
               (Qmult (Qmult 2 k2p) en')).
      { exact HMs. }
      { exact HMc. }
      { exact Hcol. }
      { exact Hv1. }
      { exact Hhδ. }
      { exact Hh12. }
      { exact Hd1. }
      { exact Hw. }
      { exact Hen0. }
      { exact Hk20. }
      { exact HE20. } }
    { apply (b5n_absorbQ colQ
             (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                    (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
             X (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) E2 en').
      { exact HX0. }
      { exact Hen'0. }
      { exact HcoefQ. }
      { exact HcolQ8. }
      { unfold X, S, E2. exact HaddQ32. } } }
  { (* 分支 B：|v_n| > 1 → crude（强制 K1 ≤ en'/2） *)
    set (av := Qabs (b5i_vn x h n)).
    set (aw := Qabs (Qminus (b5i_vn x h n) (Qmult (b5i_dn x n) (projT1 h n)))).
    set (ah := Qabs (projT1 h n)).
    assert (Hq4 : Qle ah (1 # 4)).
    { apply (Qle_trans ah (Qmult (Qplus 1 (Qmult en k2)) ah) (1 # 4)).
      { apply (Qle_trans ah (Qmult 1 ah) (Qmult (Qplus 1 (Qmult en k2)) ah)).
        { apply qeq_imp_qle. ring. }
        { apply (Qmult_le_compat_r 1 (Qplus 1 (Qmult en k2)) ah).
          { apply Qle_plus_nonneg_r. apply (Qmult_le_0_compat en k2 Hen0 Hk20). }
          { exact (Qabs_nonneg (projT1 h n)). } } }
      { unfold ah. exact Hq. } }
    assert (Hq5 : Qle (Qmult (Qmult en k2) ah) (1 # 4)).
    { apply (Qle_trans (Qmult (Qmult en k2) ah)
                       (Qmult (Qplus 1 (Qmult en k2)) ah)
                       (1 # 4)).
      { apply (Qmult_le_compat_r (Qmult en k2) (Qplus 1 (Qmult en k2)) ah).
        { nra. }
        { exact (Qabs_nonneg (projT1 h n)). } }
      { unfold ah. exact Hq. } }
    assert (Hav : Qle av (Qplus aw ah)).
    { apply (Qle_trans av (Qplus aw (Qabs (Qmult (b5i_dn x n) (projT1 h n)))) (Qplus aw ah)).
      { unfold av, aw.
        apply (Qle_trans (Qabs (b5i_vn x h n))
                         (Qabs (Qplus (Qminus (b5i_vn x h n)
                                              (Qmult (b5i_dn x n) (projT1 h n)))
                                      (Qmult (b5i_dn x n) (projT1 h n))))
                         (Qplus (Qabs (Qminus (b5i_vn x h n)
                                              (Qmult (b5i_dn x n) (projT1 h n))))
                                (Qabs (Qmult (b5i_dn x n) (projT1 h n))))).
        { apply qeq_imp_qle. apply Qabs_wd. ring. }
        { apply Qabs_triangle. } }
      { apply Qplus_le_compat.
        { apply Qle_refl. }
        { apply (b5i_dh_abs_le_h (b5i_dn x n) (projT1 h n) Hd1). } } }
    assert (Haw : Qle aw (Qplus (Qmult (Qmult en k2) ah) E2)).
    { unfold aw, ah, E2. exact Hw. }
    assert (HE2h : Qle (1 # 2) E2).
    { apply (b5n_forceE2 av aw ah (Qmult (Qmult en k2) ah) E2).
      { unfold av. exact Hvbig. }
      { exact Hav. }
      { exact Hq4. }
      { exact Haw. }
      { exact Hq5. } }
    assert (H4en : Qle 1 (Qmult (Qmult 4 k2p) en')).
    { apply (b5n_forceE2en E2 k2p en' HE2h).
      unfold E2. reflexivity. }
    assert (HK1h : Qle K1e (Qmult (1 # 2) en')).
    { apply (b5n_forceK1 K1e k2p en' Hk2p).
      { unfold K1e. exact Hk2pK1. }
      { exact H4en. } }
    apply (Qle_trans (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                     (Qplus colQ
                            (Qplus K1e
                                   (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                     (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
    { apply (b5i_pern_crude x Hx h Hxh n Ms Mc C4 colQ k2 en
               (Qmult (Qmult 2 k2p) en')).
      { exact HMs. }
      { exact HMc. }
      { exact HC4. }
      { exact HC40. }
      { exact Hcol. }
      { exact Hw. }
      { exact Hen0. }
      { exact Hk20. }
      { exact HE20. } }
    { apply (Qle_trans (Qplus colQ
                               (Qplus K1e
                                      (Qmult Mc (Qplus (Qmult (Qmult en k2) (Qabs (projT1 h n))) E2))))
                       (Qplus colQ
                              (Qplus K1e
                                     (Qplus (Qmult (Qmult Mc k2) X) (Qmult Mc E2))))
                       (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply Qplus_le_compat.
        { apply Qle_refl. }
        { apply Qplus_le_compat.
          { apply Qle_refl. }
          { apply qeq_imp_qle. unfold X. ring. } } }
      { apply (b5n_absorbC colQ K1e Mc E2 X en' k2).
        { exact HX0. }
        { exact Hen'0. }
        { exact HcoefC. }
        { exact HcolQ8. }
        { exact HK1h. }
        { unfold E2. exact HaddC32. } } } }
Qed.

(* ============================================================ *)
(* Part E：b5a_sin_atan_diff 主装配（W）                         *)
(*   δ := min(min(min δa (1/2)) (eps·kδ)) (1/4 · inv(1+eps·k2)) *)
(*   预算：colQ = eta = (1#8)·e1'；en/en' 逐点非负；margin 证毕  *)
(* ============================================================ *)

(* eps 见证的逐点提取：0 < e 且 ∀ n ≥ N：e < projT1 eps n *)
Lemma b5n_eps_proj_lt : forall (eps : Real), real_lt real_zero eps ->
  sigT (fun e : Q => And (QltT 0 e) (sigT (fun N : nat =>
    forall n : nat, NatLe N n -> Qlt e (projT1 eps n)))).
Proof.
  intros eps Heps.
  destruct Heps as [e [He [N HN]]].
  exists e. split.
  { exact He. }
  { exists N. intros n Hn.
    assert (Hsub : Qlt e (Qminus (projT1 eps n) (projT1 real_zero n))).
    { apply QltT_to_Qlt. exact (HN n Hn). }
    apply (Qlt_le_trans e (Qminus (projT1 eps n) (projT1 real_zero n)) (projT1 eps n)).
    { exact Hsub. }
    { apply qeq_le. cbn [projT1 real_zero]. ring. } }
Qed.

Lemma b5a_sin_atan_diff : forall (x : Real)
  (Hx : forall n : nat, QleT' (Qabs (projT1 x n)) 1),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (h : Real), real_lt (real_abs h) delta ->
      forall (Hxh : forall n : nat, QleT' (Qabs (projT1 (real_plus x h) n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (b5a_comp_err_sin x Hx h Hxh))
              (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros x Hx eps Heps.
  destruct (b5i_sinA_bounded x Hx) as [Ms [HMs_pos HMs_all]].
  destruct (b5i_cosA_bounded x Hx) as [Mc [HMc_pos HMc_all]].
  destruct b5i_exp_arch4 as [C4 [HC4ge1 HC4]].
  destruct (b5c_d_proj_le_one x) as [Nd Hd].
  destruct (b5n_eps_proj_lt eps Heps) as [e0 [He0T [Ne0 He0lt]]].
  assert (HMsQ : Qlt 0 Ms). { apply QltT_to_Qlt. exact HMs_pos. }
  assert (HMcQ : Qlt 0 Mc). { apply QltT_to_Qlt. exact HMc_pos. }
  assert (HMs0 : Qle 0 Ms). { apply Qlt_le_weak. exact HMsQ. }
  assert (HMc0 : Qle 0 Mc). { apply Qlt_le_weak. exact HMcQ. }
  assert (HC4le1 : Qle 1 C4). { apply QleT'_to_Qle. exact HC4ge1. }
  assert (HC40 : Qle 0 C4).
  { apply (Qle_trans 0 1 C4).
    { unfold Qle. simpl. lia. }
    { exact HC4le1. } }
  set (S := Qplus Ms Mc).
  assert (HSlt : Qlt 0 S). { unfold S. nra. }
  set (K1e := Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                    (Qmult Mc (Qplus (Qmult 4 C4) 4))).
  assert (HK1_0 : Qle 0 K1e). { unfold K1e. nra. }
  set (kδ := Qinv (Qmult 512 (Qplus S 1))).
  set (k2 := Qinv (Qmult (Qmult 512 (Qplus S 1))
                         (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  set (k2p := Qinv (Qmult (Qmult 1024 (Qplus K1e 1))
                          (Qplus (Qplus (Qmult 3 S) Mc) 1))).
  assert (HkδT : QltT 0 kδ).
  { unfold kδ. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2T : QltT 0 k2).
  { unfold k2. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2pT : QltT 0 k2p).
  { unfold k2p. apply Qlt_to_QltT. apply Qinv_lt_0_compat. nra. }
  assert (Hk2Q : Qle 0 k2). { apply Qlt_le_weak. apply QltT_to_Qlt. exact Hk2T. }
  assert (Hk2pQ : Qlt 0 k2p). { apply QltT_to_Qlt. exact Hk2pT. }
  (* 全局预算：coef（quad）、coefC（crude）、8k2p·K1（crude 强制） *)
  assert (HcoefQ : Qle (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2)) 1).
  { apply (Qle_trans (Qplus (Qmult (Qmult 2 (Qplus Ms Mc)) kδ)
                             (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc) k2))
                     (Qplus (1 # 2) (1 # 2))
                     1).
    { apply Qplus_le_compat.
      { apply (b5n_2S_kδ_le S HSlt). }
      { apply (b5n_3S_Mc_k2_le S Mc HSlt HMc0). } }
    { nra. } }
  assert (HcoefC : Qle (Qmult Mc k2) 1).
  { apply (Qle_trans (Qmult Mc k2) (1 # 2) 1).
    { apply (b5n_Mc_k2_le S Mc HSlt HMc0). }
    { unfold Qle. simpl. lia. } }
  assert (Hk2pK1 : Qle (Qmult (Qmult 8 k2p)
                              (Qplus (Qmult Ms (Qplus (Qmult 4 C4) 2))
                                     (Qmult Mc (Qplus (Qmult 4 C4) 4)))) 1).
  { apply (b5n_8k2p_K1_le S Mc K1e HSlt HMc0 HK1_0). }
  (* δ 组装：0 < 各分量 *)
  assert (H12T : QltT 0 (1 # 2)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (H14T : QltT 0 (1 # 4)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  destruct (b5n_vdh_pts x Hx eps Heps k2 k2p Hk2T Hk2pT) as [δa [Hδa0 Hδa]].
  assert (Hc12r : real_lt real_zero (real_const (1 # 2))).
  { apply real_const_pos. exact H12T. }
  assert (Hepskδ : real_lt real_zero (real_mult eps (real_const kδ))).
  { apply real_mult_positive.
    { exact Heps. }
    { apply real_const_pos. exact HkδT. } }
  assert (Hqtr : real_lt real_zero
            (real_mult (real_const (1 # 4))
                       (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                     (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  { apply real_mult_positive.
    { apply real_const_pos. exact H14T. }
    { apply real_inv_pos_pos. } }
  set (delta := real_min
        (real_min (real_min δa (real_const (1 # 2)))
                  (real_mult eps (real_const kδ)))
        (real_mult (real_const (1 # 4))
                   (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                 (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
  assert (Hdpos : real_lt real_zero delta).
  { unfold delta.
    apply real_min_pos.
    { apply real_min_pos.
      { apply real_min_pos.
        { exact Hδa0. }
        { exact Hc12r. } }
      { exact Hepskδ. } }
    { exact Hqtr. } }
  exists delta.
  split.
  { exact Hdpos. }
  { intros h Hh Hxh eps' Heps'.
    destruct (b5n_eps_proj_lt eps' Heps') as [e1 [He1T [Ne1 He1lt]]].
    set (eta := Qmult (1 # 8) e1).
    assert (HetaT : QltT 0 eta).
    { unfold eta. apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1 # 8) e1).
      { unfold Qlt. simpl. lia. }
      { apply QltT_to_Qlt. exact He1T. } }
    (* h 相对 δ 的四层 min 提取 *)
    assert (HhA : real_lt (real_abs h)
             (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))).
    { apply (real_min_lt_l h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhE : real_lt (real_abs h)
             (real_mult (real_const (1 # 4))
                        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                      (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
    { apply (real_min_lt_r h
               (real_min (real_min δa (real_const (1 # 2))) (real_mult eps (real_const kδ)))
               (real_mult (real_const (1 # 4))
                          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
                                        (b5i_one_plus_eps2_pos eps k2 Heps Hk2T)))).
      exact Hh. }
    assert (HhAA : real_lt (real_abs h) (real_min δa (real_const (1 # 2)))).
    { apply (real_min_lt_l h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhlr : real_lt (real_abs h) (real_mult eps (real_const kδ))).
    { apply (real_min_lt_r h (real_min δa (real_const (1 # 2)))
                           (real_mult eps (real_const kδ))).
      exact HhA. }
    assert (Hhda : real_lt (real_abs h) δa).
    { apply (real_min_lt_l h δa (real_const (1 # 2))). exact HhAA. }
    assert (Hh12 : real_lt (real_abs h) (real_const (1 # 2))).
    { apply (real_min_lt_r h δa (real_const (1 # 2))). exact HhAA. }
    (* X：b5n_h_pts *)
    destruct (b5n_h_pts h eps kδ k2 Heps HkδT Hk2T Hhlr Hh12 HhE) as [Nh HNh].
    (* Y：arctan' 于 eps2 := eps·k2 / eps2' := eps'·k2p *)
    destruct (Hδa h Hhda Hxh eps' Heps') as [Nw HNw].
    (* 列误差列 *)
    destruct (b5i_rs_addcol x Hx h Hxh eta HetaT) as [Nc HNc].
    (* 逐点预算（对 eps' 见证） *)
    assert (Hen'g : forall n : nat, NatLe Ne1 n -> Qle 0 (projT1 eps' n)).
    { intros n Hn.
      apply (Qle_trans 0 e1 (projT1 eps' n)).
      { apply Qlt_le_weak. apply QltT_to_Qlt. exact He1T. }
      { apply Qlt_le_weak. exact (He1lt n Hn). } }
    assert (HcolQ8_all : forall n : nat, NatLe Ne1 n ->
            Qle eta (Qmult (1 # 8) (projT1 eps' n))).
    { intros n Hn.
      unfold eta.
      apply (sc_qmult_le_l e1 (projT1 eps' n) (1 # 8)).
      { apply Qlt_le_weak. exact (He1lt n Hn). }
      { unfold Qle. simpl. lia. } }
    assert (HaddQ_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                       (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult (Qplus (Qmult 3 (Qplus Ms Mc)) Mc)
                      (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                      (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. unfold S. ring. }
      { apply (Qmult_le_compat_r
                 (Qmult (Qplus (Qmult 3 S) Mc) (Qmult 2 k2p))
                 (1 # 32) (projT1 eps' n)).
        { apply (b5n_3S_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    assert (HaddC_all : forall n : nat, NatLe Ne1 n ->
            Qle (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
                (Qmult (1 # 32) (projT1 eps' n))).
    { intros n Hn.
      apply (Qle_trans
               (Qmult Mc (Qmult (Qmult 2 k2p) (projT1 eps' n)))
               (Qmult (Qmult Mc (Qmult 2 k2p)) (projT1 eps' n))
               (Qmult (1 # 32) (projT1 eps' n))).
      { apply qeq_imp_qle. ring. }
      { apply (Qmult_le_compat_r (Qmult Mc (Qmult 2 k2p)) (1 # 32)
                                 (projT1 eps' n)).
        { apply (b5n_Mc_2k2p_le S Mc K1e HSlt HMc0 HK1_0). }
        { exact (Hen'g n Hn). } } }
    (* 主装配：real_le → real_lt（左支），见证 eta *)
    set (Nmax := Nat.max (Nat.max Ne0 Ne1) (Nat.max (Nat.max Nh Nw) (Nat.max Nc Nd))).
    left.
    exists eta.
    split.
    { exact HetaT. }
    { exists Nmax.
      intros n Hn.
      apply NatLe_drop in Hn.
      set (en := projT1 eps n).
      set (en' := projT1 eps' n).
      set (hn := Qabs (projT1 h n)).
      set (Dn := Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n)).
      assert (HnNe0 : NatLe Ne0 n) by (apply NatLe_lift; lia).
      assert (HnNe1 : NatLe Ne1 n) by (apply NatLe_lift; lia).
      assert (HnNh : NatLe Nh n) by (apply NatLe_lift; lia).
      assert (HnNw : NatLe Nw n) by (apply NatLe_lift; lia).
      assert (HnNc : NatLe Nc n) by (apply NatLe_lift; lia).
      assert (HnNd : (Nd <= n)%nat) by lia.
      assert (Hen0 : Qle 0 en).
      { unfold en. apply (Qle_trans 0 e0 (projT1 eps n)).
        { apply Qlt_le_weak. apply QltT_to_Qlt. exact He0T. }
        { apply Qlt_le_weak. exact (He0lt n HnNe0). } }
      assert (Hen'0 : Qle 0 en').
      { unfold en'. exact (Hen'g n HnNe1). }
      destruct (HNh n HnNh) as [Hhδn [Hh12n Hhqn]].
      (* Z：per-n 主界 *)
      assert (Hmain : Qle (Qabs (projT1 (b5a_comp_err_sin x Hx h Hxh) n))
                          (Qplus (Qmult en (Qabs (projT1 h n))) (Qmult (3 # 4) en'))).
      { apply (b5n_pern_main x Hx h Hxh n Ms Mc C4 eta kδ k2 k2p en en').
        { exact (HMs_all n). }
        { exact (HMc_all n). }
        { exact HC4. }
        { exact HC40. }
        { exact (HNc n HnNc). }
        { exact (QleT'_to_Qle _ _ Hhδn). }
        { exact (QleT'_to_Qle _ _ Hh12n). }
        { exact (QleT'_to_Qle _ _ Hhqn). }
        { exact (HNw n HnNw). }
        { unfold b5i_dn. exact (Hd n HnNd). }
        { exact Hen0. }
        { exact Hen'0. }
        { exact Hk2Q. }
        { exact Hk2pQ. }
        { exact HcoefQ. }
        { exact HcoefC. }
        { exact (HcolQ8_all n HnNe1). }
        { exact (HaddQ_all n HnNe1). }
        { exact (HaddC_all n HnNe1). }
        { exact Hk2pK1. } }
      (* margin：eta < (1/4)en'；Hfin：eta < (en·hn + en') − Dn *)
      assert (Hq4e : Qlt eta (Qmult (1 # 4) en')).
      { unfold eta, en'. apply (b5n_quarter_gt e1 (projT1 eps' n)).
        { apply QltT_to_Qlt. exact He1T. }
        { exact (He1lt n HnNe1). } }
      assert (Hfin : Qlt eta (Qminus (Qplus (Qmult en hn) en') Dn)).
      { apply (b5n_close Dn hn en en' eta).
        { unfold Dn. exact Hmain. }
        { unfold en'. exact Hq4e. } }
      assert (Hrepl : Qeq (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                                  (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))
                          (Qminus (Qplus (Qmult en hn) en') Dn)).
      { unfold en, en', hn, Dn.
        setoid_rewrite (real_plus_proj (real_mult eps (real_abs h)) eps' n).
        setoid_rewrite (real_mult_proj eps (real_abs h) n).
        setoid_rewrite (real_abs_proj h n).
        setoid_rewrite (real_abs_proj (b5a_comp_err_sin x Hx h Hxh) n).
        ring. }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans eta
             (Qminus (Qplus (Qmult en hn) en') Dn)
             (Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
                     (projT1 (real_abs (b5a_comp_err_sin x Hx h Hxh)) n))).
      { exact Hfin. }
      { apply qeq_imp_qle. apply Qeq_sym. exact Hrepl. } } }
Qed.

End B5A_Item1B.

(* ToyR 系替换定理假设面打印（零新增依赖验证锚） *)
Print Assumptions b3_one_minus_q_pos.

Print Assumptions atan_odd_nonneg.

Print Assumptions atan_odd_neq.
Print Assumptions b3_abs_sq.
Print Assumptions b3_one_plus_sq_neq.
Print Assumptions b3_inv_sq_r.
