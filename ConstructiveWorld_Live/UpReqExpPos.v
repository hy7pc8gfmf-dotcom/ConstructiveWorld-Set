(* ==========================================================================)
   UpReqExpPos.v — 指数函数正性件
   使命: upreq_exp_pos（指数恒正主定理）与 or_destruct 分支形、upreq_exp_neg_ne_zero（指数非零）、upreq_exp_neg_unit、upreq_real_zero_ne_one。
   依赖: CW_ConstructiveWorld_219；Stdlib QArith、Arith。
   对标: 指数函数正值性（实分析基础件）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqRealLtShiftBridge.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* 件 1：Real 层 0 ≠ 1（五步链步骤 2 的矛盾基础模块）                  *)
(*   证明：引用库内同内容已证结论 rlsb_zero_ne_one                    *)
(*   （UpReqRealLtShiftBridge：real_eq 取 ε := 1 得逐项分离           *)
(*   QltT |0−1| 1，逐点计算化归 Q 层矛盾 discriminate 消去）。        *)
(* ============================================================ *)
Lemma upreq_real_zero_ne_one : Not (real_eq real_zero real_one).
Proof.
  exact rlsb_zero_ne_one.
Qed.

(* ============================================================ *)
(* 件 2（五步链步骤 1）：单位元 eˣ·e⁻ˣ == 1                         *)
(*   eˣ·e⁻ˣ == e^{x+(−x)}（exp_neg_plus 反向）== e^{−0}（参数        *)
(*   real_eq 运输：plus_opp → opp_compat → cauchy_real_exp_wd）     *)
(*   == 1（real_exp_neg_zero）。                                   *)
(* ============================================================ *)
Lemma upreq_exp_neg_unit : forall x : Real,
  real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one.
Proof.
  intro x.
  apply (real_eq_trans
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_exp_neg (real_plus x (real_opp x)))
           real_one).
  - exact (real_eq_sym _ _ (real_exp_neg_plus x (real_opp x))).
  - apply (real_eq_trans
           (real_exp_neg (real_plus x (real_opp x)))
           (real_exp_neg real_zero)
           real_one).
    + unfold real_exp_neg.
      apply cauchy_real_exp_wd.
      apply RealSetoid.real_eq_opp_compat.
      exact (real_plus_opp x).
    + exact real_exp_neg_zero.
Qed.

(* ============================================================ *)
(* 件 3（五步链步骤 2）：eˣ ≠ 0（乘法逆元存在性推论）                *)
(*   eˣ==0 ⟹ eˣ·e⁻ˣ == 0·e⁻ˣ == 0（eq_mult_compat + mult_comm      *)
(*   + mult_zero）⟹ 0 == 1（件 1）⟹ Empty_set 消去。               *)
(* ============================================================ *)
Lemma upreq_exp_neg_ne_zero : forall x : Real,
  Not (real_eq (real_exp_neg x) real_zero).
Proof.
  intro x. intro Hzero.
  assert (Hstep : real_eq
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_mult real_zero (real_exp_neg (real_opp x))))
    by exact (RealSetoid.real_eq_mult_compat (real_exp_neg x) (real_exp_neg (real_opp x))
                                  real_zero (real_exp_neg (real_opp x))
                                  Hzero (real_eq_refl (real_exp_neg (real_opp x)))).
  assert (Hzl : real_eq (real_mult real_zero (real_exp_neg (real_opp x))) real_zero).
  { apply (real_eq_trans
             (real_mult real_zero (real_exp_neg (real_opp x)))
             (real_mult (real_exp_neg (real_opp x)) real_zero)
             real_zero).
    - exact (real_mult_comm real_zero (real_exp_neg (real_opp x))).
    - exact (real_mult_zero (real_exp_neg (real_opp x))). }
  assert (Hunit : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one)
    by exact (upreq_exp_neg_unit x).
  assert (Hm0 : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_zero)
    by exact (real_eq_trans _ _ _ Hstep Hzl).
  exact (upreq_real_zero_ne_one
           (real_eq_sym _ _ (real_eq_trans _ _ _ (real_eq_sym _ _ Hunit) Hm0))).
Qed.

(* ============================================================ *)
(* 件 4（目标定理，主结果）：0 < eˣ 对全部实数 x                     *)
(*   real_exp_neg (real_opp x) = cauchy_real_exp (real_opp          *)
(*   (real_opp x)) = eˣ；库内 real_exp_neg_pos 于 real_opp x 一词    *)
(*   实例化——即 exp_neg_pos 接口字段的 Real 层实例化验证：其 ε 见证   *)
(*   由 S03 幂级数构造（ε := 1/(2C)，构造性 sigT 形态）。        *)
(* ============================================================ *)
Theorem upreq_exp_pos : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof. intro x. exact (real_exp_neg_pos (real_opp x)). Qed.

(* ============================================================ *)
(* 件 5（五步链步骤 5 的 Or 消解形态）：目标定理的 Or 编码演绎        *)
(*   real_le real_zero eˣ = Or (real_lt real_zero eˣ) (real_eq       *)
(*   real_zero eˣ)（S02:460 编码展开）；左支由级数 ε-见证直供（件 4  *)
(*   同源），右支 0==eˣ 经件 3 归谬得 Empty_set、任意 Set 目标消去    *)
(*   ——destruct-Or + 右支归谬的标准构造性结构，纯项式组装。          *)
(* ============================================================ *)
Theorem upreq_exp_pos_or_destruct : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof.
  intro x.
  assert (Hle : real_le real_zero (real_exp_neg (real_opp x))).
  { apply inl. exact (real_exp_neg_pos (real_opp x)). }
  destruct Hle as [Hpos | Heq].
  - exact Hpos.
  - destruct (upreq_exp_neg_ne_zero (real_opp x) (real_eq_sym _ _ Heq)).
Qed.

Print Assumptions upreq_real_zero_ne_one.
Print Assumptions upreq_exp_neg_unit.
Print Assumptions upreq_exp_neg_ne_zero.
Print Assumptions upreq_exp_pos.
Print Assumptions upreq_exp_pos_or_destruct.
