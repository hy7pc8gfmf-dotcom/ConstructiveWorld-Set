(* ============================================================
   UpReqSteadyThermo —— 使命行：本件形式化定理 4.9 steady_state_boltzmann
   的 Real 层构造：稳态分布的 Boltzmann 形（热力学侧载体），
   主件 real_steady_state_boltzmann：Σ_{s'} p(s')·T(s',s) == p(s)。
   依赖：CW_ConstructiveWorld_219；求和前提位供给节另引
   UpReqConcSoftmax（csm_sumf 有限和载体）与 ConcMixSelFeed
   （cms_sum_ext/cms_sum_linear 供给锚）。
   构造性注记：语句面全 Set 层（real_eq/real_lt/real_le 全 Set 载体，零 Prop
   泄露）；零承认、零经典逻辑；全件 Qed 闭合、可提取；
   抽象求和算子两位（real_sum_over_S_ext/real_sum_over_S_linear）的证书供给
   见文尾消解节（载体代换 real_sum_over_S := csm_sumf S0 enum）。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)
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
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.

(* ============================================================ *)
(* Section RealThermoSteady：与 Id 层 BoltzmannSteadyState 同构         *)
(* ============================================================ *)
Section RealThermoSteady.

(* 求和载体（Real 层平行接口，S08 RealAttnSteady 同位） *)
Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* Id 位：base_loss / D / D_pos / Z / Z_pos *)
Variable energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_r : Real.
Variable Z_r_pos : real_lt real_zero Z_r.

(* Id 位：partition_condition（real_eq 载体，rfep_boltzmann_normalized_real 同款轴向） *)
Variable real_partition_condition :
  real_eq Z_r
          (real_sum_over_S
             (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).

(* Id 位：boltzmann_unnorm / boltzmann_prob（热力学侧载体） *)
Definition real_boltzmann_unnorm (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).
Definition real_boltzmann_prob (s : S) : Real :=
  real_mult (real_inv_pos Z_r Z_r_pos) (real_boltzmann_unnorm s).

(* Id 位：transition / transition_nonneg / transition_normalization / detailed_balance *)
Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall (s s' : S),
  real_le real_zero (real_transition s s').
Variable real_transition_normalization : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_transition s s')) real_one.
Variable real_detailed_balance : forall (s s' : S),
  real_eq (real_mult (real_boltzmann_prob s) (real_transition s s'))
          (real_mult (real_boltzmann_prob s') (real_transition s' s)).

(* ============================================================ *)
(* 主定理：稳态方程（定理 4.9 Real 层等式复刻）                           *)
(*   Σ_{s'} p(s')·T(s',s) == p(s)                                      *)
(*   五步链：①detailed balance 逐点 → ②ext 求和外延 → ③linear 提取     *)
(*   → ④核归一化（mult_compat）→ ⑤mult_one 完成                        *)
(* ============================================================ *)
Theorem real_steady_state_boltzmann : forall s : S,
  real_eq (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s)))
          (real_boltzmann_prob s).
Proof.
  intro s.
  (* 步②：求和外延壳（real_sum_over_S_ext）——逐点前提即步① *)
  apply (real_eq_trans _
           (real_sum_over_S (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s')))
           _).
  - apply (real_sum_over_S_ext
             (fun s' : S => real_mult (real_boltzmann_prob s') (real_transition s' s))
             (fun s' : S => real_mult (real_boltzmann_prob s) (real_transition s s'))).
    (* 步①：逐点 detailed balance 替换（实参序 (s' s)，Id 原证同款） *)
    intro s'. exact (real_detailed_balance s' s).
  - (* 步③：线性提取 p(s)（real_sum_over_S_linear） *)
    apply (real_eq_trans _
             (real_mult (real_boltzmann_prob s) (real_sum_over_S (fun s' : S => real_transition s s')))
             _).
    + apply (real_sum_over_S_linear (real_boltzmann_prob s) (fun s' : S => real_transition s s')).
    + (* 步④：核归一化（real_transition_normalization 经 mult_compat 对角入位） *)
      apply (real_eq_trans _ (real_mult (real_boltzmann_prob s) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat (real_boltzmann_prob s)
                 (real_sum_over_S (fun s' : S => real_transition s s'))
                 (real_boltzmann_prob s) real_one
                 (real_eq_refl _) (real_transition_normalization s)).
      * (* 步⑤：p(s)·1 == p(s)（real_mult_one 完成） *)
        exact (real_mult_one (real_boltzmann_prob s)).
Qed.

End RealThermoSteady.

(* ============================================================ *)
(* 求和前提位消解节：real_sum_over_S_ext 与 real_sum_over_S_linear        *)
(*                                                                     *)
(* 两位为抽象求和算子 real_sum_over_S 的接口义务；本节在有限和载体        *)
(* csm_sumf S0 enum（枚举清单折叠，UpReqConcSoftmax）上逐位供给同构语句    *)
(* ——语句与原假设位逐字同型（载体代换 real_sum_over_S := csm_sumf S0       *)
(* enum），供给锚：cms_sum_ext / cms_sum_linear（ConcMixSelFeed）。        *)
(* 原抽象假设位声明与既有定理签名零改动。                                 *)
(* ============================================================ *)
Section SteadyThermoSumSlotsSupply.
Variable S0 : Set.
Variable enum : list S0.

(* 位 real_sum_over_S_ext：求和外延（cms_sum_ext S0 enum 全参直引） *)
Theorem sts_sum_ext_supply : forall (f g : S0 -> Real),
  (forall s : S0, real_eq (f s) (g s)) ->
  real_eq (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_ext S0 enum). Qed.

(* 位 real_sum_over_S_linear：标量提取（cms_sum_linear 全参直引） *)
Theorem sts_sum_linear_supply : forall (a : Real) (f : S0 -> Real),
  real_eq (csm_sumf S0 enum (fun s : S0 => real_mult a (f s)))
          (real_mult a (csm_sumf S0 enum f)).
Proof. exact (cms_sum_linear S0 enum). Qed.

End SteadyThermoSumSlotsSupply.

Print Assumptions sts_sum_ext_supply.
Print Assumptions sts_sum_linear_supply.
