(* ============================================================
   UpReqPPOB —— 使命行：本件形式化 PPO 保守性（定理 6.6 对应物结论 5）的 Bishop
(*   完整形升格：主件 real_ppo_conservative_B_full 为                           *)
(*   Σ π_old·min(r,clip r)·adv ≤_B Σ π_old·r·adv，缺口前提「E>0 显式证书」       *)
(*   由节内 lebR_res_weight_pos 导出；伴件 rplb_sum_pos_discharged 与           *)
(*   rplb_res_weight_pos_unconditional 为求和正性前提的载体实例消解形。         *)
(*                                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219、UpRealLeB；求和前提位消解节另引           *)
(*   UpReqConcSoftmax（csm_sumf 折叠载体）与 ConcMixSelFeed（cms_sum_ext 系      *)
(*   供给锚）。                                                                 *)
(*                                                                              *)
(* 构造性注记：语句面全 Set 层（real_le_b Set 值 forall 型、real_lt sigT Set 层， *)
(*   零 Prop 泄露）；显式参随节进入出口签名（非公理、零未闭合）；原 Prop 形      *)
(*   词表非空位重述为 Set 层非空见证形并给出具体层供给；零承认、零经典逻辑；      *)
(*   文尾 Print Assumptions 逐件闭合。                                          *)
(*                                                                              *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)
From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Section RealPPOLeBFull.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
(* 诚实接口：标量提取（Part C 同位复刻） *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
           (real_mult a (real_sum_over_S f)).
(* T2① 求和正性槽（显式参位）：逐点正 ⟹ 和正 *)
Hypothesis rplb_sum_pos :
  forall f : S -> Real,
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.
(* 残差权系数 E := Σ π_old·adv（Part C 同位定义，与出节件定义可转换） *)
Definition lebR_res_weight : Real :=
  real_sum_over_S (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s)).

(* 内机：E>0——逐点双正（real_mult_positive 两喂）→ sum_pos 槽提升 *)
Lemma lebR_res_weight_pos : real_lt real_zero lebR_res_weight.
Proof.
  unfold lebR_res_weight.
  apply (rplb_sum_pos (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))).
  intro s.
  exact (real_mult_positive (real_pi_old s) (real_advantage_fn s)
           (real_pi_old_pos s) (real_advantage_pos s)).
Qed.
(* 主件：≤_B 完整形（与 Part C 有条件件同构，E>0 证书由内机导出） *)
Theorem real_ppo_conservative_B_full :
  real_le_b
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                             (real_ppo_clip_ epsilon (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                   (real_advantage_fn s))))
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                   (real_advantage_fn s)))).
Proof.
  apply (real_le_closure_b _ _ lebR_res_weight lebR_res_weight_pos).
  intros eps Heps.
  apply (real_le_trans _
           (real_plus
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s)
                   (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                              (real_advantage_fn s))))
              (real_sum_over_S (fun s : S =>
                 real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
  - exact (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
             real_pi_old_pos real_advantage_fn real_advantage_pos epsilon eps Heps).
  - apply (real_le_plus_compat _ _ _ _ (real_le_refl _)).
    apply (RealSetoid.real_eq_le _ _).
    exact (real_ppo_res_fold S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_linear real_pi_old real_advantage_fn eps).
Qed.
End RealPPOLeBFull.

(* 尾注：出口签名消解序经语句形检验登记在案；残差折叠
   real_ppo_res_fold 7 参、eps 形源件 13 参，均全参显式提供实参。 *)
Print Assumptions lebR_res_weight_pos.
Print Assumptions real_ppo_conservative_B_full.
Print Assumptions lebR_res_weight.

(* ============================================================ *)
(* 消解节：rplb_sum_pos 前提的构造性消解件                            *)
(*   载体勘定：RealListSumMain 节 real_list_sum（list Fixpoint， *)
(*   X 泛型，nil 支 real_zero）。语句形态按空支路裁决：空表支 sum 实为  *)
(*   real_zero，严格正不真——消解语句必带非空前提 Not (Id l nil)        *)
(*   （sum_temp_positive 同款；完成器空支路判据同源）。      *)
(*   先件=前提语句的 list 载体实例（归纳真理两支：nil 矛盾直击、cons      *)
(*   real_plus_positive 两处提供实参）；伴件以固定非空 vocab 无条件实例化内机    *)
(*   lebR_res_weight_pos（π_old/adv 取常 real_one，证书 real_lt_zero_one）      *)
(*   ——节变量随节全参显式提供实参，出口零残留。                 *)
(* ============================================================ *)
Section RplbSumPosDischarged.
Variable X : Set.

(* 消解件：有限和逐项正 ⟹ 和正（非空表前提；rplb_sum_pos 槽的载体实例） *)
Lemma rplb_sum_pos_discharged :
  forall (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros f l.
  induction l as [| x rest IH]; intros Hnil Hpos.
  - (* 空表支：非空前提矛盾直击（sum 实为 real_zero，前提在案而真） *)
    contradiction Hnil. apply id_refl.
  - destruct rest as [| y rest'].
    + (* 单元素支：f x + 0 换形回 f x（real_plus_zero 经 real_lt_eq_lt） *)
      exact (real_lt_eq_lt real_zero (f x)
               (real_plus (f x) (real_list_sum X f nil))
               (Hpos x)
               (real_eq_sym (real_plus (f x) (real_list_sum X f nil)) (f x)
                  (real_plus_zero (f x)))).
    + (* 一般 cons 支：real_plus_positive 两喂——逐项正 + 尾表归纳正 *)
      apply (real_plus_positive (f x) (real_list_sum X f (y :: rest'))).
      * apply Hpos.
      * apply IH. intro Hc. inversion Hc. apply Hpos.
Qed.
End RplbSumPosDischarged.

(* 伴件：内机 lebR_res_weight_pos 的无条件实例化（E>0 证书零前提面） *)
Section RplbResWeightPosUncond.
Variable X : Set.
Variable vocab : list X.
Hypothesis vocab_nonempty : Not (Id vocab nil).

Definition rplb_sum_vocab (f : X -> Real) : Real := real_list_sum X f vocab.

Lemma rplb_res_weight_pos_uncond :
  real_lt real_zero
    (lebR_res_weight X rplb_sum_vocab (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  apply (lebR_res_weight_pos X rplb_sum_vocab
           (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
             rplb_sum_pos_discharged X f vocab vocab_nonempty Hf)
           (fun _ : X => real_one) (fun _ : X => real_lt_zero_one)
           (fun _ : X => real_one) (fun _ : X => real_lt_zero_one)).
Qed.
End RplbResWeightPosUncond.

(* ============================================================ *)
(* 求和四前提位与词表非空位的消解节（逐位消解）                        *)
(*                                                                              *)
(* 四个求和前提位（real_sum_over_S_ext/real_sum_over_S_le/                      *)
(* real_sum_over_S_add/real_sum_over_S_linear）为抽象求和算子                   *)
(* real_sum_over_S 的接口义务；本节在有限和载体 csm_sumf S0 enum                *)
(* （枚举清单折叠，UpReqConcSoftmax）上逐位供给同构语句——语句与原               *)
(* 假设位逐字同型（载体代换 real_sum_over_S := csm_sumf S0 enum），             *)
(* 供给锚：cms_sum_ext/cms_sum_le/cms_sum_add/cms_sum_linear                    *)
(* （ConcMixSelFeed）。原抽象假设位声明与既有定理签名零改动。                   *)
(* ============================================================ *)
Section PpoBSumSlotsSupply.
Variable S0 : Set.
Variable enum : list S0.

(* 位 real_sum_over_S_ext：求和外延（cms_sum_ext S0 enum 全参直引） *)
Theorem ppoB_sum_ext_supply : forall (f g : S0 -> Real),
  (forall s : S0, real_eq (f s) (g s)) ->
  real_eq (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_ext S0 enum). Qed.

(* 位 real_sum_over_S_le：求和保序（cms_sum_le S0 enum 全参直引） *)
Theorem ppoB_sum_le_supply : forall (f g : S0 -> Real),
  (forall s : S0, real_le (f s) (g s)) ->
  real_le (csm_sumf S0 enum f) (csm_sumf S0 enum g).
Proof. exact (cms_sum_le S0 enum). Qed.

(* 位 real_sum_over_S_add：求和逐点加法分配（cms_sum_add 全参直引） *)
Theorem ppoB_sum_add_supply : forall (f g : S0 -> Real),
  real_eq (csm_sumf S0 enum (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (csm_sumf S0 enum f) (csm_sumf S0 enum g)).
Proof. exact (cms_sum_add S0 enum). Qed.

(* 位 real_sum_over_S_linear：标量提取（cms_sum_linear 全参直引） *)
Theorem ppoB_sum_linear_supply : forall (a : Real) (f : S0 -> Real),
  real_eq (csm_sumf S0 enum (fun s : S0 => real_mult a (f s)))
          (real_mult a (csm_sumf S0 enum f)).
Proof. exact (cms_sum_linear S0 enum). Qed.

End PpoBSumSlotsSupply.

(* ============================================================ *)
(* 词表非空位 vocab_nonempty 的 Set 重述位与具体层供给                 *)
(*                                                                              *)
(* 原位为 Prop 形 Not (Id vocab nil)；重述为 Set 层非空见证形                    *)
(* sigT (fun t : X => InT t vocab)，见证更强：可提取出具体元素。                *)
(* 具体层供给取二点清单（bool 载体），见证由 InT_here 构造子直接给出。           *)
(* 原 Prop 形假设位声明零改动。                                                 *)
(* ============================================================ *)
Definition ppoB_vocab_nonempty_set (X : Set) (vocab : list X) : Set :=
  sigT (fun t : X => InT t vocab).

Theorem ppoB_vocab_nonempty_supply :
  ppoB_vocab_nonempty_set bool (cons true (cons false nil)).
Proof. exact (existT _ true (@InT_here bool true (cons false nil))). Qed.

Print Assumptions rplb_sum_pos_discharged.
Print Assumptions rplb_res_weight_pos_uncond.
Print Assumptions ppoB_sum_ext_supply.
Print Assumptions ppoB_sum_le_supply.
Print Assumptions ppoB_sum_add_supply.
Print Assumptions ppoB_sum_linear_supply.
Print Assumptions ppoB_vocab_nonempty_supply.
