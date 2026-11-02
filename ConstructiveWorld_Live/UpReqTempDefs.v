(* UpReqTempDefs.v —— 使命：本件形式化 FEP 温度族的 Real 层定义件： *) (*   Boltzmann 因子、温度化配分函数、温度化 Boltzmann 分布、能量期望 *)
(*   与分布熵的定义族及正性、归一化定律；并供给求和接口实例层证书。 *) (* 依赖：CW_ConstructiveWorld_219、UpReqConcSoftmax、ConcMixSelFeed。 *)
(* 对标：mathlib 测度论 Boltzmann 分布；stdlib Coq Reals。 *) (* 构造性注记：Set 层承载（语句全 real_eq/real_lt）；零承认件； *)
(*   新增供给段零假设位、全 Qed；可提取。 *) (* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 单道守护。 *)
(*   real_Z_temp / real_entropy_dist / real_energy_exp_temp），定理    *) (*   4.6a entropy_deficit_kl_temp（等式档 real_eq）及其后 4.6b/c 的    *)
(*   Real 层复刻全部卡在定义层缺失。本件新建温度族 Real 层定义件 4 件  *) (* 【Id 层原件对位（逐字段对照表，全 grep 实证）】                     *)
(*   real_Z_temp              <- Id partition_function_temp 参数形       *) (*      (S06 L3339 Variable T/T_pos 形；S04 L3410 Z_temp_spec 的       *)
(*       sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss  *) (*       s))) 展开体)：此处取 Section 固定 T 实例化，配分即求和本体，   *)
(*       Z_temp_spec 恒等式退化为 real_eq_refl（定义性相等）。          *) (*   real_boltzmann_factor_temp <- Id exp_neg (mult (inv_pos t Ht)     *)
(*       (base_loss s)) 分子参数位（S04 L3421 内层）。                      *) (*   real_boltzmann_dist_temp <- Id boltzmann_dist_temp (S04 L3421)：  *)
(*      mult (inv_pos (Z_temp t) (Z_temp_pos t Ht))                    *) (*           (exp_neg (mult (inv_pos t Ht) (base_loss s)))，           *)
(*      因子序（inv 在前 exp 在后）逐字段保留。                         *) (*   real_energy_exp_temp     <- Id energy_exp_temp (S04 L3424)：      *)
(*      sum_over_S (fun s => mult (dist s) (base_loss s))。             *) (*   real_entropy_dist        <- Id entropy_dist (S04 L3150)：         *)
(*      唯一前提位置差：Id log 全值，Real real_log 带正性证人             *) (*      (S07 L7842)，故 Hp : forall s, real_lt real_zero (p s) 前移，   *)
(*      与 req 层先例 reqd_entropy_dist S sumf p Hp 同位。              *)
(*   正性/归一化基础引理对位：real_Z_temp_pos <- Id Z_temp_pos          *)
(*      (S04 L3416，exp 正性 × 和正性)；real_boltzmann_dist_temp_      *)
(*      normalized <- Id boltzmann_dist_temp_normalized (S04 L3433，   *)
(*      linear + inv_pos_correct 两步，既有配方；rfep_boltzmann_      *)
(*      normalized_real（UpReqRealFEP Part 3）同款形态）。              *)
(*   载体裁决：求和载体取抽象 real_sum_over_S + ext/linear/pos 接口     *)
(*      （G02_Debt RealScaleDual/RealAttnGibbsTemp 与 UpReqRealFEP      *)
(*      RFEPMain 既有先例；Id sum_over_S 同轴对位），非 real_list_sum   *)
(*   命名回避：real_softmax_temp / real_softmax_temp_param 已被         *)
(*      real_boltzmann_dist_temp 供货（inv_pos 归一化即温度化 softmax）。*)
(* 【红线】纯构造性四条红线：零承认件、经典实数公理禁；Set 层零 Prop    *)
(*   泄露（语句全 real_eq/real_lt）；T_pos 前提位置照 Id 层 Variable      *)
(*   对位（Section Variable T/T_pos，S06 L3338 同形）；全 Qed 完成。    *)
(* 编译配方（同 _t2_build.cmd）：                                       *)
(*   UpReqTempDefs.v   （秒审先行，再去 -vos 全量 G2）                  *)

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

(* ============================================================ *)
(* 实例层供给段（假设消融：证书位转已证定理，签名保持式） *)
(*   语句面 = 原假设命题（载体换成锚件实例 csm_sumf S0 en）； *)
(*   证明 = 锚件全参显式应用（ConcMixSelFeed cms_sum_* 三件）。 *)
(* ============================================================ *)
From Stdlib Require Import List.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.

(* 求和外延：逐点 real_eq 给出和的 real_eq（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_tempdef_sum_ext_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Qed.

(* 求和线性：常数因子提出（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_tempdef_sum_linear_sup :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    real_eq (csm_sumf S0 en (fun s : S0 => real_mult a (f s)))
            (real_mult a (csm_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Qed.

(* 求和可加：两项和的分解（原假设命题@csm_sumf 实例）。 *)
Theorem w3p_tempdef_sum_add_sup :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    real_eq (csm_sumf S0 en (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (csm_sumf S0 en f) (csm_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Qed.

(* ============================================================ *)
(* Section RealTempDefs：温度族 Real 层定义件（抽象 sumf 载体）         *)
(* ============================================================ *)
Section RealTempDefs.

(* 抽象状态空间与求和接口（G02_Debt RealAttnGibbsTemp 同形先例） *)
Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).

(* 温度（前提位置照 Id 层 Variable 对位：S06 L3338）与能量 *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* ---------------------------------------------------------- *)
(* 定义件 0（分子助手）：Boltzmann 因子                              *)
(*   bf(s) := e^{−e(s)/T}                                           *)
(*   对位 Id S04 L3421 内层 exp_neg (mult (inv_pos t Ht) E_s)。      *)
(* ---------------------------------------------------------- *)
Definition real_boltzmann_factor_temp (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos T T_pos) (energy s)).

(* Boltzmann 因子正性（exp 恒正；对位 Id exp_neg_pos 参数位） *)
Lemma real_boltzmann_factor_temp_pos :
  forall s : S, real_lt real_zero (real_boltzmann_factor_temp s).
Proof.
  intro s.
  unfold real_boltzmann_factor_temp.
  apply real_exp_neg_pos.
Qed.

(* ---------------------------------------------------------- *)
(* 定义件 1：温度化配分函数                                          *)
(*   Z_T := Σ_s e^{−e(s)/T}                                         *)
(*   对位 Id partition_function_temp（S06 L3339 Variable 形）/        *)
(*   S04 Z_temp_spec 展开体；求和本体即配分，spec 恒等式退化为        *)
(*   定义性相等。                                                    *)
(* ---------------------------------------------------------- *)
Definition real_Z_temp : Real :=
  real_sum_over_S real_boltzmann_factor_temp.

(* 基础引理 1（正性件）：Z_T > 0（exp 正性 × 和正性；对位 Id       *)
(* Z_temp_pos S04 L3416）。                                          *)
Theorem real_Z_temp_pos : real_lt real_zero real_Z_temp.
Proof.
  unfold real_Z_temp.
  apply real_sum_pos_preserved.
  intro s.
  apply real_boltzmann_factor_temp_pos.
Qed.

(* ---------------------------------------------------------- *)
(* 定义件 2：温度化 Boltzmann 分布（inv_pos 归一化，即温度化 softmax）*)
(*   p_T(s) := inv(Z_T)·e^{−e(s)/T}                                 *)
(*   对位 Id boltzmann_dist_temp（S04 L3421），因子序逐字段保留      *)
(*   （inv 在前 exp 在后）。                                          *)
(* ---------------------------------------------------------- *)
Definition real_boltzmann_dist_temp (s : S) : Real :=
  real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
            (real_boltzmann_factor_temp s).

(* 分布逐点正性（inv 正 × 因子正；对位 Id boltzmann_dist_temp_pos） *)
Lemma real_boltzmann_dist_temp_pos :
  forall s : S, real_lt real_zero (real_boltzmann_dist_temp s).
Proof.
  intro s.
  unfold real_boltzmann_dist_temp.
  apply (real_mult_pos_compat
           (real_inv_pos real_Z_temp real_Z_temp_pos)
           (real_boltzmann_factor_temp s)).
  - apply real_inv_pos_pos.
  - apply real_boltzmann_factor_temp_pos.
Qed.

(* 基础引理 2（归一化件）：Σ_s p_T(s) == 1                          *)
(*   对位 Id boltzmann_dist_temp_normalized（S04 L3433）；两步链：    *)
(*   逐 s 乘子交换（sum_ext）→ 线性提取（sum_linear）→               *)
(*   inv(Z_T)·Z_T == 1（inv_pos_correct）。既有配方固定两步走，      *)
(*   rfep_boltzmann_normalized_real（UpReqRealFEP Part 3）同款形态。  *)
Theorem real_boltzmann_dist_temp_normalized :
  real_eq (real_sum_over_S real_boltzmann_dist_temp) real_one.
Proof.
  apply (real_eq_trans
           (real_sum_over_S real_boltzmann_dist_temp)
           (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
           real_one).
  - (* 步 1：Σ p_T ≡ inv(Z_T)·Z_T（交换 + 线性 + 配分定义性收敛） *)
    apply (real_eq_trans
             (real_sum_over_S real_boltzmann_dist_temp)
             (real_sum_over_S
                (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                        (real_boltzmann_factor_temp s)))
             (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)).
    + apply (real_sum_over_S_ext real_boltzmann_dist_temp
               (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                       (real_boltzmann_factor_temp s))).
      intro s. apply real_eq_refl.
    + apply (real_eq_trans
               (real_sum_over_S
                  (fun s : S => real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                          (real_boltzmann_factor_temp s)))
               (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                          (real_sum_over_S real_boltzmann_factor_temp))
               (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)).
      * apply real_sum_over_S_linear.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                 (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_sum_over_S real_boltzmann_factor_temp)
                 real_Z_temp
                 (real_eq_refl (real_inv_pos real_Z_temp real_Z_temp_pos))
                 (real_eq_refl real_Z_temp)).
  - (* 步 2：inv(Z_T)·Z_T ≡ 1（交换 + inv_pos_correct） *)
    apply (real_eq_trans
             (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
             (real_mult real_Z_temp (real_inv_pos real_Z_temp real_Z_temp_pos))
             real_one).
    + apply real_mult_comm.
    + apply real_inv_pos_correct.
Qed.

(* ---------------------------------------------------------- *)
(* 定义件 3：温度化能量期望                                          *)
(*   E_T := Σ_s p_T(s)·e(s)                                         *)
(*   对位 Id energy_exp_temp（S04 L3424）逐字段。                    *)
(* ---------------------------------------------------------- *)
Definition real_energy_exp_temp : Real :=
  real_sum_over_S (fun s : S => real_mult (real_boltzmann_dist_temp s) (energy s)).

(* ---------------------------------------------------------- *)
(* 定义件 4：分布熵（信息熵分布版）                                  *)

(*   对位 Id entropy_dist（S04 L3150）逐字段；唯一前提位置差：          *)

(*   （req 层先例 reqd_entropy_dist 同位）。                          *)
(* ---------------------------------------------------------- *)
Definition real_entropy_dist
  (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)) : Real :=
  real_sum_over_S (fun s : S => real_mult (p s) (real_opp (real_log (p s) (Hp s)))).

(* ============================================================ *)
(* 加做件：real_entropy_temp_explicit（Id entropy_temp_explicit        *)
(*   @L17271 的 Real 层同构副本；req 先例 req_entropy_temp_explicit  *)
(*   UpReqTempEntropy 件 1/5 同语句档）：                              *)



(*   → sum_add 分和 → β 线性提取 + logZ 常数提取（归一化完成）。        *)
(* ============================================================ *)


(* real_log_wd + real_inv_pos_correct + real_log_one + real_plus 群）  *)
Lemma real_log_inv_Z_aux :
  real_eq (real_log (real_inv_pos real_Z_temp real_Z_temp_pos)
                    (real_inv_pos_pos real_Z_temp real_Z_temp_pos))
          (real_opp (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  set (X := real_log (real_inv_pos real_Z_temp real_Z_temp_pos)
                     (real_inv_pos_pos real_Z_temp real_Z_temp_pos)).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  assert (Hsum : real_eq (real_plus X LZ) real_zero).
  { apply (real_eq_trans (real_plus X LZ)
             (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                       (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                          real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                          real_Z_temp_pos))
             real_zero).
    - apply real_eq_sym.
      exact (real_log_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp
              (real_inv_pos_pos real_Z_temp real_Z_temp_pos) real_Z_temp_pos).
    - apply (real_eq_trans
               (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                         (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                            real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                            real_Z_temp_pos))
               (real_log real_one real_lt_zero_one)
               real_zero).
      + apply (real_log_wd
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                 real_one
                 (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                    real_Z_temp (real_inv_pos_pos real_Z_temp real_Z_temp_pos)
                    real_Z_temp_pos)
                 real_lt_zero_one).
        apply (real_eq_trans
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp)
                 (real_mult real_Z_temp (real_inv_pos real_Z_temp real_Z_temp_pos))
                 real_one).
        * exact (real_mult_comm (real_inv_pos real_Z_temp real_Z_temp_pos) real_Z_temp).
        * exact (real_inv_pos_correct real_Z_temp real_Z_temp_pos).
      + exact (real_log_one real_lt_zero_one). }
  apply (real_eq_trans X (real_plus X real_zero) (real_opp LZ)).
  - apply real_eq_sym. exact (real_plus_zero X).
  - apply (real_eq_trans
             (real_plus X real_zero)
             (real_plus X (real_plus LZ (real_opp LZ)))
             (real_opp LZ)).
    + apply (RealSetoid.real_eq_plus_compat_adapt X X real_zero
               (real_plus LZ (real_opp LZ)) (real_eq_refl X)).
      apply real_eq_sym. exact (real_plus_opp LZ).
    + apply (real_eq_trans
             (real_plus X (real_plus LZ (real_opp LZ)))
             (real_plus (real_plus X LZ) (real_opp LZ))
             (real_opp LZ)).
      * exact (real_plus_assoc X LZ (real_opp LZ)).
      * apply (real_eq_trans
                 (real_plus (real_plus X LZ) (real_opp LZ))
                 (real_plus real_zero (real_opp LZ))
                 (real_opp LZ)).
        -- apply (RealSetoid.real_eq_plus_compat_adapt
                    (real_plus X LZ) real_zero (real_opp LZ) (real_opp LZ)
                    Hsum (real_eq_refl (real_opp LZ))).
        -- apply (real_eq_trans
                    (real_plus real_zero (real_opp LZ))
                    (real_plus (real_opp LZ) real_zero)
                    (real_opp LZ)).
           ++ exact (real_plus_comm real_zero (real_opp LZ)).
           ++ exact (real_plus_zero (real_opp LZ)).
Qed.


Lemma real_neg_log_boltzmann_point :
  forall s : S,
    real_eq (real_opp (real_log (real_boltzmann_dist_temp s)
                                (real_boltzmann_dist_temp_pos s)))
            (real_plus (real_mult (real_inv_pos T T_pos) (energy s))
                       (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  intro s.
  set (bta := real_inv_pos T T_pos).
  set (Hi := real_inv_pos_pos real_Z_temp real_Z_temp_pos).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  apply (real_eq_trans
           (real_opp (real_log (real_boltzmann_dist_temp s)
                               (real_boltzmann_dist_temp_pos s)))
           (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
           (real_plus (real_mult bta (energy s)) LZ)).
  - apply (RealSetoid.real_eq_opp_compat
             (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    apply (real_eq_trans
             (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
             (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                        (real_log (real_exp_neg (real_mult bta (energy s)))
                                  (real_exp_neg_pos (real_mult bta (energy s)))))
             (real_opp (real_plus LZ (real_mult bta (energy s))))).
    + apply (real_eq_trans
               (real_log (real_boltzmann_dist_temp s) (real_boltzmann_dist_temp_pos s))
               (real_log (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                                    (real_exp_neg (real_mult bta (energy s))))
                         (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                            (real_exp_neg (real_mult bta (energy s))) Hi
                            (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))).
      * exact (real_log_wd
                 (real_boltzmann_dist_temp s)
                 (real_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                            (real_exp_neg (real_mult bta (energy s))))
                 (real_boltzmann_dist_temp_pos s)
                 (real_mult_positive (real_inv_pos real_Z_temp real_Z_temp_pos)
                    (real_exp_neg (real_mult bta (energy s))) Hi
                    (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_eq_refl (real_boltzmann_dist_temp s))).
      * exact (real_log_mult (real_inv_pos real_Z_temp real_Z_temp_pos)
                 (real_exp_neg (real_mult bta (energy s))) Hi
                 (real_exp_neg_pos (real_mult bta (energy s)))).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                          (real_log (real_exp_neg (real_mult bta (energy s)))
                                    (real_exp_neg_pos (real_mult bta (energy s)))))
               (real_plus (real_opp LZ) (real_opp (real_mult bta (energy s))))
               (real_opp (real_plus LZ (real_mult bta (energy s))))).
      * apply (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos real_Z_temp real_Z_temp_pos) Hi)
                 (real_opp LZ)
                 (real_log (real_exp_neg (real_mult bta (energy s)))
                           (real_exp_neg_pos (real_mult bta (energy s))))
                 (real_opp (real_mult bta (energy s)))
                 real_log_inv_Z_aux
                 (real_log_exp_neg (real_mult bta (energy s)))).
      * apply real_eq_sym.
        exact (real_opp_plus LZ (real_mult bta (energy s))).
  - apply (real_eq_trans
             (real_opp (real_opp (real_plus LZ (real_mult bta (energy s)))))
             (real_plus LZ (real_mult bta (energy s)))
             (real_plus (real_mult bta (energy s)) LZ)).
    + exact (real_opp_opp (real_plus LZ (real_mult bta (energy s)))).
    + apply real_plus_comm.
Qed.


Theorem real_entropy_temp_explicit :
  real_eq (real_entropy_dist real_boltzmann_dist_temp real_boltzmann_dist_temp_pos)
          (real_plus (real_mult (real_inv_pos T T_pos) real_energy_exp_temp)
                     (real_log real_Z_temp real_Z_temp_pos)).
Proof.
  unfold real_entropy_dist.
  set (bta := real_inv_pos T T_pos).
  set (p := real_boltzmann_dist_temp).
  set (Hp := real_boltzmann_dist_temp_pos).
  set (LZ := real_log real_Z_temp real_Z_temp_pos).
  apply (real_eq_trans
           (real_sum_over_S (fun s : S => real_mult (p s) (real_opp (real_log (p s) (Hp s)))))
           (real_sum_over_S (fun s : S => real_mult (p s)
                              (real_plus (real_mult bta (energy s)) LZ)))
           (real_plus (real_mult bta real_energy_exp_temp) LZ)).
  - (* 步 1：逐点换形（点引理显式应用） *)
    apply real_sum_over_S_ext.
    intro s.
    apply (RealSetoid.real_eq_mult_compat_adapt (p s) (p s)
             (real_opp (real_log (p s) (Hp s)))
             (real_plus (real_mult bta (energy s)) LZ)
             (real_eq_refl (p s))
             (real_neg_log_boltzmann_point s)).
  - (* 步 2-4：distrib 逐点拆和 → add 分和 → β 提取 + logZ 提取 *)
    apply (real_eq_trans
             (real_sum_over_S (fun s : S => real_mult (p s)
                                (real_plus (real_mult bta (energy s)) LZ)))
             (real_plus
                (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                (real_sum_over_S (fun s : S => real_mult (p s) LZ)))
             (real_plus (real_mult bta real_energy_exp_temp) LZ)).
    + apply (real_eq_trans
               (real_sum_over_S (fun s : S => real_mult (p s)
                                  (real_plus (real_mult bta (energy s)) LZ)))
               (real_sum_over_S (fun s : S =>
                  real_plus (real_mult (p s) (real_mult bta (energy s)))
                            (real_mult (p s) LZ)))
               (real_plus
                  (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                  (real_sum_over_S (fun s : S => real_mult (p s) LZ)))).
      * apply real_sum_over_S_ext.
        intro s. apply real_distrib.
      * apply (real_sum_over_S_add
                 (fun s : S => real_mult (p s) (real_mult bta (energy s)))
                 (fun s : S => real_mult (p s) LZ)).
    + (* β 提取 + logZ 提取（两支） *)
      apply (RealSetoid.real_eq_plus_compat_adapt
               (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
               (real_mult bta real_energy_exp_temp)
               (real_sum_over_S (fun s : S => real_mult (p s) LZ))
               LZ).
      * (* β 支：Σ p·(β·e) ≡ β·E_T（逐点重排 → 线性提取 → 定义性收敛） *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                 (real_mult bta (real_sum_over_S (fun s : S => real_mult (p s) (energy s))))
                 (real_mult bta real_energy_exp_temp)).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (p s) (real_mult bta (energy s))))
                    (real_sum_over_S (fun s : S => real_mult bta (real_mult (p s) (energy s))))
                    (real_mult bta (real_sum_over_S (fun s : S => real_mult (p s) (energy s))))).
           ++ apply real_sum_over_S_ext.
              intro s.
              apply (real_eq_trans
                       (real_mult (p s) (real_mult bta (energy s)))
                       (real_mult (real_mult (p s) bta) (energy s))
                       (real_mult bta (real_mult (p s) (energy s)))).
              ** exact (real_mult_assoc (p s) bta (energy s)).
              ** apply (real_eq_trans
                          (real_mult (real_mult (p s) bta) (energy s))
                          (real_mult (real_mult bta (p s)) (energy s))
                          (real_mult bta (real_mult (p s) (energy s)))).
                 --- apply (RealSetoid.real_eq_mult_compat_adapt
                              (real_mult (p s) bta) (real_mult bta (p s))
                              (energy s) (energy s)
                              (real_mult_comm (p s) bta) (real_eq_refl (energy s))).
                 --- apply real_eq_sym.
                     exact (real_mult_assoc bta (p s) (energy s)).
           ++ apply (real_sum_over_S_linear bta
                       (fun s : S => real_mult (p s) (energy s))).
        -- exact (real_eq_refl (real_mult bta real_energy_exp_temp)).
      * (* logZ 支：Σ p·LZ ≡ LZ·Σ p ≡ LZ·1 ≡ LZ *)
        apply (real_eq_trans
                 (real_sum_over_S (fun s : S => real_mult (p s) LZ))
                 (real_mult LZ (real_sum_over_S p))
                 LZ).
        -- apply (real_eq_trans
                    (real_sum_over_S (fun s : S => real_mult (p s) LZ))
                    (real_sum_over_S (fun s : S => real_mult LZ (p s)))
                    (real_mult LZ (real_sum_over_S p))).
           ++ apply real_sum_over_S_ext.
              intro s. apply real_mult_comm.
           ++ apply (real_sum_over_S_linear LZ p).
        -- apply (real_eq_trans
                    (real_mult LZ (real_sum_over_S p))
                    (real_mult LZ real_one)
                    LZ).
           ++ apply (RealSetoid.real_eq_mult_compat_adapt LZ LZ
                       (real_sum_over_S p) real_one
                       (real_eq_refl LZ) real_boltzmann_dist_temp_normalized).
           ++ exact (real_mult_one LZ).
Qed.

End RealTempDefs.
