(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* PintPosGrid.v — 位切片代理（组 E-STAGING-D024）                                   *)
(* 目的：P1b 残面「段上逐点正 ⟹ 积分正」判定件。数学预判先行：一期 pint_integral =     *)
(*   Σ a_k/(k+1) 恰为 [0,1] 上多项式真积分（线性泛函），「系数任意但段上逐点正⟹积分正」  *)
(*   对线性泛函一般不真——本件给出显式二次反例的构造性否定性见证，把 P1b 从「缺网格机器」 *)
(*   改判为「命题需强化」。反例（n=2，手算定性后机器定型）：pg_counterex(x) = −x² + x −    *)
(*   11/64 = 1/64 + (3/4−x)(x−1/4)。肢1（段上逐点正，带显式下界）：x ∈ [1/4,3/4] ⟹ 两因子  *)
(*   非负，pg_counterex(x) ≥ 1/64 > 0——平方差因式分解 1/16−(x−1/2)² = (3/4−x)(x−1/4) 使    *)
(*   全程免 ε-网格/有限和机器；肢2（积分负）：∫₀¹ = −11/64 + 1/2 − 1/3 = −1/192 < 0。       *)
(* 结论（工程图 v2 §五 ②/④ 的改判依据）：① P1b 原命题（段逐点正⟹全积分正）假，否定性     *)
(*   见证 = 本件双肢；P5 ④「同一台 P1b 机器」路线注销，改走：(a) 系数级分解路线：f = g + h、 *)
(*   h 系数全非负 ⟹ ∫f ≥ ∫g（一期 pint_integral_nonneg + P1 pm_pointwise_le_integral 已全  *)
(*   量覆盖，一行可达）；(b) Beta 闭式路线：I_n = ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} 的下界取        *)
(*   ∫₀¹ tⁿ(1−t)ⁿ = (n!)²/(2n+1)! 闭式后纯阶乘不等式，免段上逐点化；② 修正命题面（真方向）：  *)
(*   「全 [0,1] 逐点正⟹积分正」仍真（连续+紧）但构造性需 ε-网格有限和下界机（原残面本体，    *)
(*   另案）；「Bernstein 系数全正(+某系数正)⟹积分正」为可机器检验的充分条件面                *)
(*   （∫ΣbᵢBᵢ = (1/(n+1))Σbᵢ），需 mono↔Bern 基变换机——对任意系数多项式是 P1 件的真扩面。    *)
(* 四要素逐件声明：语句面全 Set（QleT'/QltT + Type 积，零 Prop 语句、零 Prop 前提）；         *)
(*   前提面仅 QleT' 段端点；证明面 Q 层结构化（Qle_trans/Qplus_le_compat/                     *)
(*   Qmult_le_compat_r 双肢 + Qeq setoid 换形，数值件 vm_compute 信任缓存快测）；提取面       *)
(*   eval/int 纯函数。红线：零假公理位、零未证闭合、零经典逻辑；一期 pint_ 全部只依存不重编。  *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.

(* ============================================================ *)
(* §1 内部支撑小件（Q 层，仅证内）                                    *)
(* ============================================================ *)

(* 非负两数之积非负（Qle 层；Qle_trans 过 0·b + Qmult_le_compat_r，
   复刻 PintMono pm_mult_r0_le 先例手法） *)
Lemma pg_mult0 : forall a b : Q, Qle 0 a -> Qle 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb. apply (Qle_to_QleT' 0 (a * b)).
  apply (Qle_trans 0 (0 * b) (a * b)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_r 0 a b).
    + exact Ha.
    + exact Hb.
Qed.

(* 右减端换形：x ≤ y ⟹ 0 ≤ y − x（Qplus_le_compat 双边件配 Qplus_opp_r
   折叠左端；绕开 stdlib 本轨缺单边 le_compat_r 的坑） *)
Lemma pg_qle_minus_r : forall x y : Q, Qle x y -> QleT' 0 (y - x).
Proof.
  intros x y H. apply (Qle_to_QleT' 0 (y - x)).
  apply (Qle_trans 0 (x + (- x)) (y + (- x))).
  - rewrite Qplus_opp_r. apply Qle_refl.
  - apply (Qplus_le_compat x y (- x) (- x)).
    + exact H.
    + apply Qle_refl.
Qed.

(* 数值件：0 < 1/64（vm_compute 一步；S02 qltT_0_1 同型先例） *)
Lemma pg_lt_1_64 : QltT 0 (1 # 64).
Proof. apply (Qlt_to_QltT 0 (1 # 64)). vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 反例定义与恒等式肢                                              *)
(* ============================================================ *)

(* 反例多项式（pint 系数列表编码，头 = 常数项）：
   pg_counterex(x) = −11/64 + x·(1 + x·(−1)) = −x² + x − 11/64 *)
Definition pg_counterex : list Q := (- 11 # 64) :: (1 # 1) :: (- 1 # 1) :: nil.

(* 恒等式肢：pg_counterex(x) == 1/64 + (3/4−x)·(x−1/4)
   （平方差分解 1/16 − (x−1/2)² = (3/4−x)(x−1/4) 的承载形） *)
Lemma pg_counterex_eval_eq : forall x : Q,
  QeqT (pint_eval pg_counterex x) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
Proof.
  intros x. apply qeq_imp_qeqT. unfold pg_counterex. cbn [pint_eval]. ring.
Qed.

(* ============================================================ *)
(* §3 肢1：段上逐点正（带显式正下界 1/64——强于「严格正」原命题）        *)
(* ============================================================ *)

(* 主件：x ∈ [1/4,3/4] ⟹ pg_counterex(x) ≥ 1/64（QleT' Set 面） *)
Theorem pg_counterex_seg_ge : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QleT' (1 # 64) (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HP : Qle 0 (((3 # 4) - x) * (x - (1 # 4)))).
  { apply (QleT'_to_Qle 0 (((3 # 4) - x) * (x - (1 # 4)))). apply pg_mult0.
    - apply (QleT'_to_Qle 0 ((3 # 4) - x)). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hhi.
    - apply (QleT'_to_Qle 0 (x - (1 # 4))). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hlo. }
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qle_to_QleT'.
  rewrite HE.
  apply (Qle_trans (1 # 64) ((1 # 64) + 0) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4)))).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (1 # 64) (1 # 64) 0
                           (((3 # 4) - x) * (x - (1 # 4)))).
    + apply Qle_refl.
    + exact HP.
Qed.

(* 原命题同形件：x ∈ [1/4,3/4] ⟹ pg_counterex(x) > 0（QltT Set 面） *)
Theorem pg_counterex_seg_pos : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QltT 0 (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qlt_to_QltT.
  rewrite HE.
  apply (Qplus_lt_le_compat 0 (1 # 64) 0 (((3 # 4) - x) * (x - (1 # 4)))).
  - apply (QltT_to_Qlt 0 (1 # 64)). apply pg_lt_1_64.
  - apply (QleT'_to_Qle 0 (((3 # 4) - x) * (x - (1 # 4)))). apply pg_mult0.
    + apply (QleT'_to_Qle 0 ((3 # 4) - x)). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hhi.
    + apply (QleT'_to_Qle 0 (x - (1 # 4))). apply pg_qle_minus_r.
      apply QleT'_to_Qle. exact Hlo.
Qed.

(* ============================================================ *)
(* §4 肢2：积分负（数值封闭计算：∫ = −1/192 < 0）                      *)
(* ============================================================ *)

Theorem pg_counterex_int_neg : QltT (pint_integral pg_counterex) 0.
Proof.
  unfold pg_counterex, pint_integral. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §5 否定性见证封装（Set 面 Type 积：双肢并列即 P1b 原命题已证结论件）        *)
(*                                                               *)
(*   pg_P1b_counterexample 的存在 ⟹ 「段上逐点正 ⟹ 积分正」原命题     *)
(*   不可能获得全量证明——任何如此机器作用于 pg_counterex 即与肢2 矛盾。 *)
(*   P1b 从「缺网格机器」改判为「命题需强化」（修正方向见文件头结论）。  *)
(* ============================================================ *)

Definition pg_P1b_death_certificate : Set :=
  (forall x : Q, QleT' (1 # 4) x -> QleT' x (3 # 4) ->
     QltT 0 (pint_eval pg_counterex x))
  * QltT (pint_integral pg_counterex) 0.

Theorem pg_P1b_counterexample : pg_P1b_death_certificate.
Proof.
  exact (pair pg_counterex_seg_pos pg_counterex_int_neg).
Qed.

(* ============================================================ *)
(* 提取检验 + 假设审计留痕（编译期 stdout，verify 复核）               *)
(* ============================================================ *)

Extraction "pintposgrid_extract.ml"
  pg_counterex pg_counterex_seg_ge pg_counterex_seg_pos
  pg_counterex_int_neg pg_P1b_counterexample.

Print Assumptions pg_counterex_seg_ge.
Print Assumptions pg_counterex_seg_pos.
Print Assumptions pg_counterex_int_neg.
Print Assumptions pg_P1b_counterexample.
