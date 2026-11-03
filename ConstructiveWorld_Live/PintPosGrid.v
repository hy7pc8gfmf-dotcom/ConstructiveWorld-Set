(* ConstructiveWorld-Set — polynomial segment positivity versus integral sign. *)

(** * PintPosGrid: pointwise positivity on a segment does not imply a positive integral.

    Mission.  For linear functionals the claim is false.  The quadratic
      [pg_counterex] = [-x^2 + x - 11/64] = [1/64 + (3/4 - x)(x - 1/4)] is
      pointwise at least [1/64] on [1/4, 3/4] ([pg_counterex_seg_ge],
      strictly [pg_counterex_seg_pos]), yet its integral is negative
      ([pg_counterex_int_neg], exact value [-1/192]); both arms are packaged
      as [pg_P1b_counterexample], so the statement needs strengthening.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lists.List],
      [Arith.Arith], [ZArith.ZArith], [Lia], [Extraction].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [PolyIntegral] of this
      development.

    References.  This development, [PolyIntegral].v, whose functionals
      [pint_eval] and [pint_integral] are consumed here.  Strengthened
      routes: coefficient-level decomposition f = g + h with h of
      non-negative coefficients, and Bernstein-coefficient conditions.

    Constructivity.  All named statements are carried by [Set]
      ([QleT']/[QltT] faces; the witness pair is a [Type] product); premises
      are [QleT'] segment endpoints only.  Proofs are structured Q-chains
      with numeric facts by [vm_compute].  Statements extract with
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" PintPosGrid.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)


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
