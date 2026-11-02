(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpSigMigrate2.v *)
(* *)
(* 目的： 签名迁移第二段：指数/对数接口与配分面。 *)
(* 主件： boltzmann_dist_m2 / free_energy_m2 定义族与 req_exp_neg_ext / req_log_inv_one_inv 接口。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 承第一段载体约定；指数与对数接口为显式前提面。 *)
(* ============================================================ *)

(* UpSigMigrate2.v — ：论文 1 §4 RLHF 核心链（定理 4.1–4.4）
   的 req 系（setoid 层）重述 + RealEnhancedReal 实例装配 + 端到端主定理。

   结构：
   Part A  §4.1 通用出口 req 系重述（对 Id 系 CW L15759-16440 FreeEnergyMinimization 节）
           —— 相对试点 UpSigMigrate.v 的升级：试点把 Id 上游已证件
              energy_in_log_boltzmann / free_energy_boltzmann 作桥假设给出，
              此处全部内部真证（req_log_inv_one_inv / req_boltzmann_log_decomp /
              Real 实例由 real_log_exp_neg CW L42231 消解）。
   Part B  对齐层 req 系重述（对 Id 系 CW L18734-19158 Alignment 节）：
             req_rlhf_optimal        —— J(pi) <= J(pi_star)           （Id L19049）
             req_rlhf_optimal_eps    —— Bishop 逐 eps 形态（Real 层 real_rlhf_optimal_eps
                                        L43804 同构，端到端可消解）
             req_rlhf_free_energy_kl —— F[pi] == F[pi*] + beta·KL （Id L20290 间隙恒等）
             req_dpo_optimal         —— Id L19096
             req_rlhf_optimal_unique —— Id L19128
           桥假设 = Id 免费件的 req 签名给出：b_gibbs_pos / b_gibbs_sum_eps
           （Id 已证 gibbs_inequality L16629；Real 层 real_gibbs_inequality_eps
           b_mult_cancel / b_gibbs_eq（Id 字段 mult_cancel_l / log_eq_linear 使用链，
           setoid 层 log_eq_linear 为构造性诚实边界）。
   Part C  两状态具体实例（S := bool + real_list_sum）装配消解 +
           端到端主定理定理（供提取检验使用，Obj.magic=0）。

   纪律：纯构造性；Set 层语句零 Prop；全 Qed；无 Id 消去（全 req_trans 链 +
   compat 桥）；禁词面与试点一致。

   ------------------------------------------------------------------
   （括号层中断）+ L1001 陈述句多右括号 + L1034 起深度失衡到文件尾，
   且缺 End ReqAlignCore；a_KL_ext_r / a_fe_kl_decomp / a_min_free_energy_eps
   三件按既有模板重写已证明。潜伏错 6 处一并已证明：a_partition 的 req_sym
   方向/因子缺失、a_pi_star_normalized 的被积函数错形、Part B 误用 Part A
   求和假设名 sum_linear、a_fe_ext 陈述 Hg 未绑定、req_mult_compat 元数
   缺位、a_pb_pos 以 Qed 不透明件阻断与 Part A 出口的 conversion（改透明
   Definition 直取 req_boltzmann_positive）。
   [续建 §4.2-4.4] a_pb_normalized / a_fe_boltzmann_pistar / a_add_cancel_r
   （右消去引擎）+ 4.2 a_rlhf_optimal（Id L19049 对位）+ 4.2
   a_rlhf_optimal_eps（Bishop 逐 eps，real_rlhf_optimal_eps L43804 对位，
   环收尾 A+oppX<=B ⟹ A<=B+X）+ 4.3b a_dpo_optimal（Id L19096 对位）+
   4.4 a_rlhf_optimal_unique（Id L19128 对位；加法消去 + b_mult_cancel +
   b_gibbs_eq 桥使用链，req 世界无 destruct 注入消去的构造性替代）。
   [Part C 端到端] R:=Real（RealEnhancedReal 消解）+ S:=bool（两状态）+
   sumf:=real_list_sum[true;false]；三性质消解使用基座 real_list_sum 三件；
   c_partition 逐项消解；主定理 #1 two_state_free_energy_boltzmann（F[p_b]==
   p_u=(1/2,1/2) 的自由能-KL 分解）各以核心定理一次性 exact 使用；
   c_mult_cancel_l = (c.2) 左乘消去引擎实例。G3 提取检验
   upsigmigrate2_probe（Obj.magic=0，验后删）。
   ------------------------------------------------------------------
   [分段点已证明] 幸存稿 Part C 三处实例-evar 易碎位（apply 类字段投影
   于具体 Real 层统一失败：c_partition L1355 / c_mult_cancel_l /
   c_pu_normalized）→ 全显式参数 exact 形态已证明（c_exp_neg_zero 先例）。
   [卸载元数实证] 主定理使用件 13/16 元 exact 调用经依赖闭包分析确证：
   section 卸载 = 语句 ∪ 证明项传递使用变量（req_free_energy_boltzmann
   经 p_times_energy_decomp→boltzmann_log_decomp→{log_compat,log_exp_neg}
   且经 sum_pb_cancel→boltzmann_normalized→partition_condition，15 槽全满）。
   8/8 Closed + 全称多态件提取 upsigmigrate2_core.ml Obj.magic=0
   （具体实例闭包 81 magic = 依赖记录擦除恒等伪影，非 Prop 泄露）；
   ------------------------------------------------------------------
   [核对修正] 权威对应矩阵（论文1-220基态-论文代码对应矩阵.md §4）实证
   定理 4.1–4.4 = rlhf_optimal / rlhf_optimal_unique / rlhf_suboptimality_gap
   dpo_optimal 记为 4.3b/4.4，实为定理 5.2 对位，dpo 件保留不删）。
   [续建 §4.3] a_rlhf_suboptimality_gap（Id L20554 对位）：J*−J == β·KL
   前向 KL 显式值；4.1 KL 分解 + pb==pistar 双换元（a_fe_boltzmann_pistar /
   a_KL_ext_r）+ A+opp(A+X)==X 环收尾，全 req_trans 链。
   [续建 §4.4] a_rlhf_policy_improvement（Id L20591 对位）：KL_new <= KL_old
   ⟹ J_old <= J_new；4.3 ×2 换元 + β>0 左乘保序（le_mult_compat 经
   mult_comm 双换元）+ le_plus_compat 两侧加 opp J* + 消去串 Hsimpl
   + opp_le_compat 双负完成。
   [端到端主定理复核] Part C 主定理 #1/#2 复跑 G3 提取（upsigmigrate2r_probe）：
   多态核 Obj.magic=0 + ocamlopt 可执行 + Print Assumptions 全 Closed；
   ------------------------------------------------------------------ *)

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
Import RealInterfaceEnhancedMod.

(* S07 世系适配：本世界 RealInterfaceEnhancedSetoid 为零参类
   （S07_RealSetoidExpLog L8075，字段全由全局 Real 承载；全局实例
   RealEnhancedReal L8740）。有参绑定面 Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R} 系异树形，移除；承载集 R 以
   记号绑定全局 Real（UpAblT6_UpReqAlign2 先例同款）。
   述语面绑定（UpSigMigrate 先例同款）：类字段声明面即全局实面
   （req/lt/le 字段类型直书 real_eq/real_lt/real_le），语句取实面记号
   与字段声明面对齐，提取面免 Obj.magic 强转；实例字段
   req:=real_eq / lt:=real_lt / le:=real_le，两读可互转。 *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ============================================================ *)
(* Part A：§4.1 通用出口的 req 系重述                            *)
(*   Id 模板：CW L15759-16440（Context {RI : RealInterfaceEnhanced}） *)
(* ============================================================ *)
Section ReqFECore.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（Id 系 SumOver 类的 setoid 对偶规格） ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- 节参数（对齐 Id 系 L15778-15791） ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- 诚实缺口桥（setoid 类真缺字段；Real 实例消解见 Part C） ---- *)
(* log ∘ exp_neg 消去：Id 系 log_exp_neg（CW L592 已证引理）的 req 给出 *)
Hypothesis req_log_exp_neg :
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).

Hypothesis req_log_compat :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).

(* ---- 节内定义（setoid 惯例形态；log 族带正性前提） ---- *)
Definition positive_dist_m2 (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition normalized_m2 (p : S -> R) : Set := req (sumf p) one.
Definition rminus_m2 (a b : R) : R := plus a (opp b).
Definition boltzmann_dist_m2 : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Definition free_energy_m2 (p : S -> R) (Hp : positive_dist_m2 p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).

(* ============================================================ *)
(* A0. req 代数前奏（试点 UpSigMigrate.v 已证模板；仅使用接口字段） *)
(* ============================================================ *)

Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
Qed.

(* 乘积交换三步链（Id 系 mult swap 模板）：a·(b·c) == b·(a·c) *)
Lemma req_mult_swap : forall a b c : R, req (mult a (mult b c)) (mult b (mult a c)).
Proof.
  intros a b c.
  apply (req_trans (mult a (mult b c)) (mult (mult a b) c) (mult b (mult a c))).
  - apply mult_assoc.
  - apply (req_trans (mult (mult a b) c) (mult (mult b a) c) (mult b (mult a c))).
    + apply (req_mult_compat (mult a b) (mult b a) c c).
      * apply mult_comm.
      * apply req_refl.
    + apply (req_sym (mult b (mult a c)) (mult (mult b a) c)). apply mult_assoc.
Qed.

(* ============================================================ *)
(* A1. exp_neg 的 req 兼容（Id 系 id_cong exp_neg 免费件；        *)
(*     经 le_antisym + exp_neg_le_decr 字段派生——B1 先例形态）    *)
(* ============================================================ *)
Lemma req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply le_antisym.
  - apply exp_neg_le_decr. apply (lt_le_iff y x). apply (inr (req_sym x y Hxy)).
  - apply exp_neg_le_decr. apply (lt_le_iff x y). apply (inr Hxy).
Qed.

(* ============================================================ *)
(* A2. log_inv_one_inv 的 req 化（Id 系 log_inv_one_inv 免费件）  *)
(* ============================================================ *)
Lemma req_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x),
    req (log (inv_pos x Hx) (inv_pos_pos x Hx)) (opp (log x Hx)).
Proof.
  intros x Hx.
  assert (Hone : req (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx))) zero).
  { apply (req_trans (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                     (log one one_pos) zero).
    - apply (req_log_compat (mult x (inv_pos x Hx)) one
                            (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)) one_pos).
      apply inv_pos_correct.
    - apply log_one. }
  assert (Htot : req (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) zero)
    by exact (req_trans (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                        (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                        zero
                        (req_sym (log (mult x (inv_pos x Hx)) (mult_positive x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                                 (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                                 (log_mult x (inv_pos x Hx) Hx (inv_pos_pos x Hx)))
                        Hone).
  apply (req_trans (log (inv_pos x Hx) (inv_pos_pos x Hx))
                   (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                   (opp (log x Hx))).
  - apply (req_sym (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                   (log (inv_pos x Hx) (inv_pos_pos x Hx))). apply plus_zero.
  - apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) zero)
                     (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (plus (log x Hx) (opp (log x Hx))))
                     (opp (log x Hx))).
    + apply (req_plus_compat (log (inv_pos x Hx) (inv_pos_pos x Hx))
                             (log (inv_pos x Hx) (inv_pos_pos x Hx))
                             zero (plus (log x Hx) (opp (log x Hx)))).
      * apply req_refl.
      * exact (req_sym (plus (log x Hx) (opp (log x Hx))) zero (plus_opp (log x Hx))).
    + apply (req_trans (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (plus (log x Hx) (opp (log x Hx))))
                       (plus (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)) (opp (log x Hx)))
                       (opp (log x Hx))).
      * apply plus_assoc.
      * apply (req_trans (plus (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx)) (opp (log x Hx)))
                         (plus (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) (opp (log x Hx)))
                         (opp (log x Hx))).
        -- apply (req_plus_compat (plus (log (inv_pos x Hx) (inv_pos_pos x Hx)) (log x Hx))
                                  (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx)))
                                  (opp (log x Hx)) (opp (log x Hx))).
           ++ apply plus_comm.
           ++ apply req_refl.
        -- apply (req_trans (plus (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) (opp (log x Hx)))
                            (plus zero (opp (log x Hx)))
                            (opp (log x Hx))).
           ++ apply (req_plus_compat (plus (log x Hx) (log (inv_pos x Hx) (inv_pos_pos x Hx))) zero
                                     (opp (log x Hx)) (opp (log x Hx)) Htot (req_refl (opp (log x Hx)))).
           ++ apply req_plus_zero_r.
Qed.

(* ============================================================ *)
(* A3. Boltzmann 三件套（Id 系 boltzmann_pos/normalized/         *)
(*     boltzmann_log_decomp 的 req 化；log_decomp 为本件新增真证） *)
(* ============================================================ *)
Lemma req_boltzmann_positive : positive_dist_m2 boltzmann_dist_m2.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

Lemma req_boltzmann_normalized : req (sumf boltzmann_dist_m2) one.
Proof.
  apply (req_trans (sumf boltzmann_dist_m2)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.


Lemma req_boltzmann_log_decomp :
  forall (s : S) (Hpb : lt zero (boltzmann_dist_m2 s)),
    req (log (boltzmann_dist_m2 s) Hpb)
        (plus (opp (log Z Z_pos))
              (opp (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intros s Hpb.
  apply (req_trans (log (boltzmann_dist_m2 s) Hpb)
                   (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                         (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                   (plus (opp (log Z Z_pos))
                         (opp (mult (inv_pos D D_pos) (base_loss s))))).
  - (* 正性前提换形桥：log 的依赖证据经 req_log_compat 自反换形 *)
    apply (req_trans (log (boltzmann_dist_m2 s) Hpb)
                     (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                          (mult_positive (inv_pos Z Z_pos)
                                         (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                     (plus (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                           (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))).
    + exact (req_sym (log (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                          (mult_positive (inv_pos Z Z_pos)
                                         (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))))
                     (log (boltzmann_dist_m2 s) Hpb)
                     (req_log_compat (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))
                                     (boltzmann_dist_m2 s)
                                     (mult_positive (inv_pos Z Z_pos)
                                                    (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                                     Hpb
                                     (req_refl (mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))))))).
    + exact (log_mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (inv_pos_pos Z Z_pos) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_plus_compat (log (inv_pos Z Z_pos) (inv_pos_pos Z Z_pos))
                           (opp (log Z Z_pos))
                           (log (exp_neg (mult (inv_pos D D_pos) (base_loss s))) (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))))
                           (opp (mult (inv_pos D D_pos) (base_loss s)))).
    + exact (req_log_inv_one_inv Z Z_pos).
    + exact (req_log_exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* 能量对数恒等：E == opp(D·(log p_b + log Z))（Id 系 L16116 上游件的 req 内部真证） *)
Lemma req_energy_in_log :
  forall (s : S) (Hpb : lt zero (boltzmann_dist_m2 s)),
    req (base_loss s)
        (opp (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))).
Proof.
  intros s Hpb.
  assert (Hld : req (log (boltzmann_dist_m2 s) Hpb)
                    (plus (opp (log Z Z_pos))
                          (opp (mult (inv_pos D D_pos) (base_loss s)))))
    by exact (req_boltzmann_log_decomp s Hpb).
  (* 肢 1：lgb + lgZ == opp m，m := E/D *)
  assert (H1 : req (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                   (opp (mult (inv_pos D D_pos) (base_loss s)))).
  { apply (req_trans (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                     (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                     (opp (mult (inv_pos D D_pos) (base_loss s)))).
    - apply (req_plus_compat (log (boltzmann_dist_m2 s) Hpb)
                             (plus (opp (log Z Z_pos))
                                   (opp (mult (inv_pos D D_pos) (base_loss s))))
                             (log Z Z_pos) (log Z Z_pos) Hld (req_refl (log Z Z_pos))).
    - (* 环代数：(opp lgZ + opp m) + lgZ == opp m *)
      apply (req_trans (plus (plus (opp (log Z Z_pos))
                                 (opp (mult (inv_pos D D_pos) (base_loss s))))
                           (log Z Z_pos))
                       (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                             (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                       (opp (mult (inv_pos D D_pos) (base_loss s)))).
      + apply (req_trans (plus (plus (opp (log Z Z_pos))
                                     (opp (mult (inv_pos D D_pos) (base_loss s))))
                               (log Z Z_pos))
                         (plus (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (opp (log Z Z_pos)))
                               (log Z Z_pos))
                         (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))).
        * apply (req_plus_compat (plus (opp (log Z Z_pos))
                                       (opp (mult (inv_pos D D_pos) (base_loss s))))
                                 (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                       (opp (log Z Z_pos)))
                                 (log Z Z_pos) (log Z Z_pos)).
          -- apply plus_comm.
          -- apply (req_refl (log Z Z_pos)).
        * apply (req_sym (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                         (plus (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                                     (opp (log Z Z_pos)))
                               (log Z Z_pos))).
          apply plus_assoc.
      + apply (req_trans (plus (opp (mult (inv_pos D D_pos) (base_loss s)))
                               (plus (opp (log Z Z_pos)) (log Z Z_pos)))
                         (plus (opp (mult (inv_pos D D_pos) (base_loss s))) zero)
                         (opp (mult (inv_pos D D_pos) (base_loss s)))).
        * apply (req_plus_compat (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (opp (mult (inv_pos D D_pos) (base_loss s)))
                                 (plus (opp (log Z Z_pos)) (log Z Z_pos)) zero
                                 (req_refl (opp (mult (inv_pos D D_pos) (base_loss s))))
                                 (req_trans (plus (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus (log Z Z_pos) (opp (log Z Z_pos)))
                                            zero
                                            (plus_comm (opp (log Z Z_pos)) (log Z Z_pos))
                                            (plus_opp (log Z Z_pos)))).
        * apply plus_zero. }
  (* 肢 2/3：D·(lgb + lgZ) == D·(opp m) == opp(D·m) == opp(loss) *)
  assert (Hchain : req (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                       (opp (base_loss s))).
  { apply (req_trans (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                     (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))
                     (opp (base_loss s))).
    - apply (req_trans (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                       (mult D (opp (mult (inv_pos D D_pos) (base_loss s))))
                       (opp (mult D (mult (inv_pos D D_pos) (base_loss s))))).
      + apply (req_mult_compat D D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))
                               (opp (mult (inv_pos D D_pos) (base_loss s))) (req_refl D) H1).
      + apply req_mult_opp_l.
    - apply (req_opp_compat (mult D (mult (inv_pos D D_pos) (base_loss s)))
                            (base_loss s)).
      apply (req_trans (mult D (mult (inv_pos D D_pos) (base_loss s)))
                       (mult (mult D (inv_pos D D_pos)) (base_loss s))
                       (base_loss s)).
      + apply mult_assoc.
      + apply (req_trans (mult (mult D (inv_pos D D_pos)) (base_loss s))
                         (mult one (base_loss s))
                         (base_loss s)).
        * apply (req_mult_compat (mult D (inv_pos D D_pos)) one (base_loss s) (base_loss s)
                                 (inv_pos_correct D D_pos) (req_refl (base_loss s))).
        * apply req_mult_one_l. }
  apply (req_trans (base_loss s)
                   (opp (opp (base_loss s)))
                   (opp (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos))))).
  - apply (req_sym (opp (opp (base_loss s))) (base_loss s)). apply req_double_neg.
  - apply (req_opp_compat (opp (base_loss s))
                          (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))).
    exact (req_sym (mult D (plus (log (boltzmann_dist_m2 s) Hpb) (log Z Z_pos)))
                   (opp (base_loss s)) Hchain).
Qed.

(* ============================================================ *)
(* A4. 求和层：Σ opp f == opp Σ f（Id 系 L15801 sum_opp 的 req 版） *)
(* ============================================================ *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Σ u·opp v == opp Σ u·v（mult-opp 求和直引） *)
Lemma req_sum_mult_opp :
  forall u v : S -> R,
    req (sumf (fun s => mult (u s) (opp (v s))))
        (opp (sumf (fun s => mult (u s) (v s)))).
Proof.
  intros u v.
  apply (req_trans (sumf (fun s => mult (u s) (opp (v s))))
                   (sumf (fun s => opp (mult (u s) (v s))))
                   (opp (sumf (fun s => mult (u s) (v s))))).
  - apply (sum_ext (fun s => mult (u s) (opp (v s)))
                   (fun s => opp (mult (u s) (v s)))).
    intro s. apply req_mult_opp_l.
  - apply req_sum_opp.
Qed.

(* ============================================================ *)

(*     （Id 系 L16198 p_times_energy_decomp 的 req 版；能量对数     *)
(*      恒等已内部真证，试点此处为桥假设——本件升级点）             *)
(* ============================================================ *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    (req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
Proof.
  intros p s.
  assert (HlegA : (req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      apply req_refl.
      exact (req_energy_in_log s (req_boltzmann_positive s)).
    apply req_mult_opp_l.
  }
  assert (Hswap : (req (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { exact (req_mult_swap (p s) D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))).
  }
  assert (Hdist2 : (req (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos)))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    apply (req_mult_compat D D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      apply req_refl.
      apply distrib.
    apply distrib.
  }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    apply (req_opp_compat (mult (p s) (mult D (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    exact Hswap.
    apply (req_trans (opp (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    apply (req_opp_compat (mult D (mult (p s) (plus (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    exact Hdist2.
    apply req_opp_plus.
Qed.

(* Σ p_b·u == u（u 任意；归一化直推） *)
Lemma req_sum_pb_cancel :
  forall u : R,
    req (sumf (fun s => mult (boltzmann_dist_m2 s) u)) u.
Proof.
  intro u.
  apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) u))) (mult u (sumf boltzmann_dist_m2)) u).
  - apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) u))) (sumf (fun s => (mult u (boltzmann_dist_m2 s)))) (mult u (sumf boltzmann_dist_m2))).
      apply (sum_ext (fun s => (mult (boltzmann_dist_m2 s) u)) (fun s => (mult u (boltzmann_dist_m2 s)))).
        intro s0. apply mult_comm.
      apply (sum_linear u boltzmann_dist_m2).
  - apply (req_trans (mult u (sumf boltzmann_dist_m2)) (mult u one) u).
      apply (req_mult_compat u u (sumf boltzmann_dist_m2) one (req_refl u) req_boltzmann_normalized).
      apply mult_one.
Qed.

Lemma req_free_energy_boltzmann :
  req (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
      (opp (mult D (log Z Z_pos))).
Proof.
  unfold free_energy_m2.
  assert (Hsum1 : (req (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))))).
  { apply (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (sumf (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))))).
      apply (sum_ext (fun s => (mult (boltzmann_dist_m2 s) (base_loss s))) (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
        intro s0. exact (req_p_times_energy_decomp boltzmann_dist_m2 s0).
      apply (req_trans (sumf (fun s => (plus (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))) (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))))).
        apply sum_add.
        apply (req_plus_compat (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
          apply (req_trans (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
            apply req_sum_opp.
            apply (req_opp_compat (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
              apply (sum_linear D (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))).
          apply (req_trans (sumf (fun s => (opp (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))).
            apply req_sum_opp.
            apply (req_opp_compat (sumf (fun s => (mult D (mult (boltzmann_dist_m2 s) (log Z Z_pos))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))).
              apply (sum_linear D (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))).
  }
  assert (Hsum2 : (req (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))))).
  { apply (req_plus_compat (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))))) (opp (mult D (log Z Z_pos)))).
      apply (req_refl (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
      apply (req_opp_compat (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))) (mult D (log Z Z_pos))).
        apply (req_mult_compat D D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos)))) (log Z Z_pos) (req_refl D) (req_sum_pb_cancel (log Z Z_pos))).
  }
  assert (Hsum : (req (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))))).
  { exact (req_trans (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log Z Z_pos))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) Hsum1 Hsum2). }
  apply (req_trans (plus (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))).
  - apply (req_plus_compat (sumf (fun s => (mult (boltzmann_dist_m2 s) (base_loss s)))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      exact Hsum.
      apply (req_refl (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
  - apply (req_trans (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) (opp (mult D (log Z Z_pos)))).
      apply (req_sym _ _ (plus_assoc (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
      apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))) (opp (mult D (log Z Z_pos)))).
        apply (req_plus_compat (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (opp (mult D (log Z Z_pos))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))).
          apply (req_refl (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
          apply plus_comm.
        apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos))))) (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (opp (mult D (log Z Z_pos)))).
          apply plus_assoc.
          apply (req_trans (plus (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (opp (mult D (log Z Z_pos)))) (plus zero (opp (mult D (log Z Z_pos)))) (opp (mult D (log Z Z_pos)))).
            apply (req_plus_compat (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) zero (opp (mult D (log Z Z_pos))) (opp (mult D (log Z Z_pos)))).
              apply (req_trans (plus (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (plus (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (sumf (fun s => (mult (boltzmann_dist_m2 s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))) zero).
                apply plus_comm.
                apply plus_opp.
              apply (req_refl (opp (mult D (log Z Z_pos)))).
            apply req_plus_zero_r.
Qed.

Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : normalized_m2 p) (p0 : positive_dist_m2 p),
    req (free_energy_m2 p p0)
        (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus_m2 (log (p s) (p0 s))
                                   (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* 桥：F[p_b] == mult (opp D) lgZ == opp (D·lgZ)（Id 系步骤 2 的 req 形态） *)
  assert (Hfb' : req (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { exact req_free_energy_boltzmann. }
  (* 步骤 1：Σ p·E == opp A + opp DlgZ（Id 原件 Hse） *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. exact (req_p_times_energy_decomp p s). }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* Σ opp(D·p·lgpb) == opp(D·Σ p·lgpb)：sum_opp + D 线性提取 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))). } }
        - (* Σ opp(D·p·lgZ) == opp(D·lgZ)：sum_opp + D 线性 + Σ p·lgZ = lgZ·Σp = lgZ 归一化链 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* 步骤 3：D·KL == B + opp A（Id 原件 Hkl） *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus_m2.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* 步骤 4：环代数坍缩（Id 原件 Hfin：(opp A + opp DlgZ) + B → opp DlgZ + (B + opp A)） *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* 装配：Hleg1（free_energy_m2 p 定义展开 conversion + Hse 于 compat 槽）；Hleg2（Hfin + Hfb'/Hkl 反向收尾槽） *)
  assert (Hleg1 : req (free_energy_m2 p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))))
                      (plus (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s))))))).
      { apply (req_sym (free_energy_m2 boltzmann_dist_m2 req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus_m2 (log (p s) (p0 s)) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (boltzmann_dist_m2 s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFECore.
(* ============================================================ *)
(* Part B：对齐层 req 系重述（Id 模板：CW L18734-19158 Alignment）  *)
(*   权威矩阵对位（论文1-220基态-论文代码对应矩阵 §4）：              *)
(*   4.1 rlhf_optimal ↔ a_rlhf_optimal(_eps)；4.2 optimal_unique      *)
(*   ↔ a_rlhf_optimal_unique；4.3 suboptimality_gap@L20554 ↔          *)
(*   a_rlhf_suboptimality_gap；4.4 policy_improvement@L20591 ↔        *)
(*   a_rlhf_policy_improvement；另有 dpo_optimal（定理 5.2 对位）       *)
(*   与 a_fe_kl_decomp（§8 统一视角锚 rlhf_free_energy_kl@L20290 对位）。 *)
(*   诚实桥（req 签名给出 Id 免费件）：                              *)
(*     b_gibbs_pos/b_gibbs_sum_eps（Id 已证 gibbs_inequality L16629；*)
(*        Real 层 real_gibbs_inequality_eps L41704 逐 eps 消解）     *)
(*     b_log_exp_neg（real_log_exp_neg 消解）/ b_log_compat（        *)
(*        real_log_wd 消解）/ b_mult_cancel+b_gibbs_eq（Id 字段       *)
(*        mult_cancel_l/log_eq_linear 使用链，G6 遗留）。             *)
(* ============================================================ *)
Section ReqAlignCore.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis asum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis asum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis asum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Hypothesis api_ref_pos : forall s : S, lt zero (pi_ref s).
Hypothesis api_ref_norm : req (sumf pi_ref) one.
Definition Z_align_a_sum : R :=
  sumf (fun s => mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Variable Z_align_a_pos : lt zero Z_align_a_sum.
Definition pdist_a (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition nrm_a (p : S -> R) : Set := req (sumf p) one.
Definition rminus_a (a b : R) : R := plus a (opp b).
Definition align_energy_a (s : S) : R :=
  rminus_a (opp (reward s)) (mult beta (log (pi_ref s) (api_ref_pos s))).
Definition pi_star_a (s : S) : R :=
  mult (inv_pos Z_align_a_sum Z_align_a_pos)
       (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Definition kl_a (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q) : R :=
  sumf (fun s => mult (p s) (rminus_a (log (p s) (Hp s)) (log (q s) (Hq s)))).
Definition fe_a (p : S -> R) (Hp : pdist_a p) : R :=
  plus (sumf (fun s => mult (p s) (align_energy_a s)))
       (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition J_a (p : S -> R) (Hp : pdist_a p) : R := opp (fe_a p Hp).

(* 诚实桥 *)
Hypothesis b_log_exp_neg :
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Hypothesis b_log_compat :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Hypothesis b_gibbs_pos :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q),
    nrm_a p -> nrm_a q -> le zero (kl_a p q Hp Hq).
Hypothesis b_gibbs_sum_eps :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q) (eps : R),
    lt zero eps -> le zero (plus (kl_a p q Hp Hq) eps).
Hypothesis b_mult_cancel :
  forall (a x : R), lt zero a -> req (mult a x) zero -> req x zero.
Hypothesis b_gibbs_eq :
  forall (p q : S -> R) (Hp : pdist_a p) (Hq : pdist_a q),
    req (kl_a p q Hp Hq) zero -> forall s : S, req (p s) (q s).

(* exp_neg 的 req 兼容（le_antisym 派生，B1 先例） *)
Lemma a_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply le_antisym.
  - apply exp_neg_le_decr. apply (lt_le_iff y x). apply (inr (req_sym x y Hxy)).
  - apply exp_neg_le_decr. apply (lt_le_iff x y). apply (inr Hxy).
Qed.

(* 对齐能量-闭式解指数恒等（Id L18858 的 req 版） *)
Lemma a_align_energy_exp :
  forall s : S, (req (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Proof.
  intro s.
  unfold align_energy_a, rminus_a.
  assert (Hs1 : (req (mult (inv_pos beta beta_pos) (plus (opp (reward s)) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s)))))).
  { apply (req_trans (mult (inv_pos beta beta_pos) (plus (opp (reward s)) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (mult (inv_pos beta beta_pos) (opp (reward s))) (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s)))))) (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s))))).
      apply distrib.
      apply (req_plus_compat (mult (inv_pos beta beta_pos) (opp (reward s))) (opp (mult (inv_pos beta beta_pos) (reward s))) (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (log (pi_ref s) (api_ref_pos s)))).
        apply req_mult_opp_l.
        apply (req_trans (mult (inv_pos beta beta_pos) (opp (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s))))) (opp (log (pi_ref s) (api_ref_pos s)))).
          apply req_mult_opp_l.
          apply (req_opp_compat (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s)))) (log (pi_ref s) (api_ref_pos s))).
            apply (req_trans (mult (inv_pos beta beta_pos) (mult beta (log (pi_ref s) (api_ref_pos s)))) (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
              apply mult_assoc.
              apply (req_trans (mult (mult (inv_pos beta beta_pos) beta) (log (pi_ref s) (api_ref_pos s))) (mult (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
                apply (req_mult_compat (mult (inv_pos beta beta_pos) beta) (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s)) (log (pi_ref s) (api_ref_pos s))).
                  apply mult_comm.
                  apply req_refl.
                apply (req_trans (mult (mult beta (inv_pos beta beta_pos)) (log (pi_ref s) (api_ref_pos s))) (mult one (log (pi_ref s) (api_ref_pos s))) (log (pi_ref s) (api_ref_pos s))).
                  apply (req_mult_compat (mult beta (inv_pos beta beta_pos)) one (log (pi_ref s) (api_ref_pos s)) (log (pi_ref s) (api_ref_pos s))).
                    apply inv_pos_correct.
                    apply req_refl.
                  apply req_mult_one_l.
  }
  apply (req_trans (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s))))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
    apply (req_trans (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (exp_neg (plus (opp (mult (inv_pos beta beta_pos) (reward s))) (opp (log (pi_ref s) (api_ref_pos s))))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))))).
      apply a_exp_neg_ext.
      exact Hs1.
      apply exp_neg_plus.
      assert (Hexpo : (req (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (pi_ref s))).
      { apply (req_trans (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (exp_neg (log_inv (pi_ref s) (api_ref_pos s))) (pi_ref s)).
          apply a_exp_neg_ext.
          apply (req_sym (log_inv (pi_ref s) (api_ref_pos s)) (opp (log (pi_ref s) (api_ref_pos s)))).
            apply log_inv_log.
          apply exp_neg_log_inv.
      }
      apply (req_trans (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s))))) (mult (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (pi_ref s)) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
        exact (req_mult_compat (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))) (exp_neg (opp (log (pi_ref s) (api_ref_pos s)))) (pi_ref s) (req_refl (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) Hexpo).
        apply mult_comm.
Qed.

(* ---- B2：对齐装配件（boltzmann 装配 / partition / pi_star_pos / 归一化） ---- *)
(* 对齐帧 Boltzmann 装配 = Part A 出口 boltzmann_dist_m2 于对齐参数处实例
   （Part A 段已 End，出口带显式 S 参数——幸存基线缺 S 位为本件修复点） *)
Definition pb_a : S -> R :=
  boltzmann_dist_m2 S align_energy_a beta beta_pos Z_align_a_sum Z_align_a_pos.

(* 透明件：直接取 Part A 出口 req_boltzmann_positive（Qed 不透明件之间的
   conversion 桥——语句层使用 Part A 结论时正性证明位必须 δ 相同） *)
Definition a_pb_pos : pdist_a pb_a :=
  req_boltzmann_positive S align_energy_a beta beta_pos
                         Z_align_a_sum Z_align_a_pos.

Lemma a_partition : (req Z_align_a_sum (sumf (fun s => (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s)))))).
Proof.
  apply (asum_ext (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))) (fun s => (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))))).
    intro s. exact (req_sym (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))) (a_align_energy_exp s)).
Qed.

Lemma a_pi_star_pos : forall s : S, lt zero (pi_star_a s).
Proof.
  intro s. unfold pi_star_a. apply mult_positive.
    apply inv_pos_pos.
    apply mult_positive.
      apply api_ref_pos.
      apply exp_neg_pos.
Qed.

Lemma a_boltzmann_is_pi_star : forall s : S, (req (pb_a s) (pi_star_a s)).
Proof.
  intro s. unfold pb_a, pi_star_a, boltzmann_dist_m2.
  apply (req_mult_compat (inv_pos Z_align_a_sum Z_align_a_pos) (inv_pos Z_align_a_sum Z_align_a_pos) (exp_neg (mult (inv_pos beta beta_pos) (align_energy_a s))) (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
    apply req_refl.
    exact (a_align_energy_exp s).
Qed.

Lemma a_pi_star_normalized : (req (sumf (fun s => (pi_star_a s))) one).
Proof.
  apply (req_trans (sumf (fun s => (pi_star_a s))) (mult (inv_pos Z_align_a_sum Z_align_a_pos) (sumf (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))))) one).
    apply (asum_linear (inv_pos Z_align_a_sum Z_align_a_pos) (fun s => (mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
    apply (req_trans (mult (inv_pos Z_align_a_sum Z_align_a_pos) Z_align_a_sum) (mult Z_align_a_sum (inv_pos Z_align_a_sum Z_align_a_pos)) one).
      apply mult_comm.
      apply inv_pos_correct.
Qed.

Lemma a_pb_normalized : nrm_a pb_a.
Proof.
  apply (req_trans (sumf pb_a) (sumf (fun s => (pi_star_a s))) one).
    apply (asum_ext pb_a (fun s => (pi_star_a s))).
      intro s. exact (a_boltzmann_is_pi_star s).
    exact a_pi_star_normalized.
Qed.

(* ---- B3：fe_a 外延 + KL 外延 ---- *)
Lemma a_fe_ext :
  forall (f g : S -> R) (Hf : pdist_a f) (Hfg : forall s : S, req (f s) (g s)) (Hg : pdist_a g),
    req (fe_a f Hf) (fe_a g Hg).
Proof.
  intros f g Hf Hfg Hg.
  unfold fe_a.
  apply (req_plus_compat (sumf (fun s => (mult (f s) (align_energy_a s)))) (sumf (fun s => (mult (g s) (align_energy_a s)))) (mult beta (sumf (fun s => (mult (f s) (log (f s) (Hf s)))))) (mult beta (sumf (fun s => (mult (g s) (log (g s) (Hg s))))))).
    apply (asum_ext (fun s => (mult (f s) (align_energy_a s))) (fun s => (mult (g s) (align_energy_a s)))).
      intro s. exact (req_mult_compat (f s) (g s) (align_energy_a s) (align_energy_a s) (Hfg s) (req_refl (align_energy_a s))).
    apply (req_mult_compat beta beta (sumf (fun s => (mult (f s) (log (f s) (Hf s))))) (sumf (fun s => (mult (g s) (log (g s) (Hg s)))))).
      apply req_refl.
      apply (asum_ext (fun s => (mult (f s) (log (f s) (Hf s)))) (fun s => (mult (g s) (log (g s) (Hg s))))).
        intro s. exact (req_mult_compat (f s) (g s) (log (f s) (Hf s)) (log (g s) (Hg s)) (Hfg s)
                                        (b_log_compat (f s) (g s) (Hf s) (Hg s) (Hfg s))).
Qed.

Lemma a_KL_ext_r :
  forall (p q1 q2 : S -> R) (Hp : pdist_a p) (Hq1 : pdist_a q1) (Hq2 : pdist_a q2),
    (forall s : S, req (q1 s) (q2 s)) ->
    req (kl_a p q1 Hp Hq1) (kl_a p q2 Hp Hq2).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hqq.
  apply (asum_ext (fun s => (mult (p s) (rminus_a (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))))
                  (fun s => (mult (p s) (rminus_a (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
                         (rminus_a (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))
                         (rminus_a (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))).
    apply req_refl.
    apply (req_plus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                           (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))).
      apply req_refl.
      apply (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))).
        apply b_log_compat.
        exact (Hqq s).
Qed.

(* fe_a(pb) == fe_a(pistar)：装配桥（4.2/4.3/4.4 共用） *)
Lemma a_fe_boltzmann_pistar :
  req (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos).
Proof.
  exact (a_fe_ext pb_a (fun s : S => pi_star_a s) a_pb_pos
           (fun s : S => a_boltzmann_is_pi_star s) a_pi_star_pos).
Qed.

(* ---- 4.1 对齐实例：F_a[p] == F_a[p_b] + beta·KL_a(p‖p_b) ---- *)
(* 使用 Part A 主定理 req_free_energy_kl_decomp 于对齐参数处实例化
   （base_loss := align_energy_a，D := beta，Z := Z_align_a_sum） *)
Lemma a_fe_kl_decomp :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (fe_a p Hp)
        (plus (fe_a pb_a a_pb_pos)
              (mult beta (kl_a p pb_a Hp a_pb_pos))).
Proof.
  intros p Hn Hp.
  exact (req_free_energy_kl_decomp S sumf asum_ext asum_add asum_linear
           align_energy_a beta beta_pos Z_align_a_sum Z_align_a_pos
           a_partition b_log_exp_neg b_log_compat p Hn Hp).
Qed.

(* ---- 4.2 前置（逐 eps，F 形）：fe_a[p_b] <= fe_a[p] + beta·eps ---- *)
Lemma a_min_free_energy_eps :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p) (eps : R),
    lt zero eps ->
    le (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps)).
Proof.
  intros p Hn Hp eps Heps.
  assert (Hdec : (req (fe_a p Hp) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (a_fe_kl_decomp p Hn Hp).
  assert (Hg : (le zero (plus (kl_a p pb_a Hp a_pb_pos) eps)))
    by exact (b_gibbs_sum_eps p pb_a Hp a_pb_pos eps Heps).
  assert (Hd : (le zero (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))).
  { apply (le_trans zero (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                     (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
    - apply (le_id_r zero (mult (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                     (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                     (mult_comm (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                     (le_id_l zero (mult zero beta)
                              (mult (plus (kl_a p pb_a Hp a_pb_pos) eps) beta)
                              (req_trans zero (mult beta zero) (mult zero beta)
                                         (req_sym (mult beta zero) zero (mult_zero beta))
                                         (mult_comm beta zero))
                              (le_mult_compat zero (plus (kl_a p pb_a Hp a_pb_pos) eps) beta beta_pos Hg))).
    - apply (lt_le_iff (mult beta (plus (kl_a p pb_a Hp a_pb_pos) eps))
                       (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
      apply (inr (distrib beta (kl_a p pb_a Hp a_pb_pos) eps)). }
  assert (Hstart : (le (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero))).
  { apply (lt_le_iff (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)).
    apply (inr (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                        (plus_zero (fe_a pb_a a_pb_pos)))). }
  apply (le_trans (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)
                  (plus (fe_a p Hp) (mult beta eps))).
    exact Hstart.
    apply (le_trans (plus (fe_a pb_a a_pb_pos) zero)
                    (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                    (plus (fe_a p Hp) (mult beta eps))).
      apply (le_plus_compat (fe_a pb_a a_pb_pos) (fe_a pb_a a_pb_pos) zero
                            (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))).
        apply le_refl.
        exact Hd.
      apply (lt_le_iff (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                       (plus (fe_a p Hp) (mult beta eps))).
        apply (inr (req_trans
                      (plus (fe_a pb_a a_pb_pos) (plus (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps)))
                      (plus (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos))) (mult beta eps))
                      (plus (fe_a p Hp) (mult beta eps))
                      (plus_assoc (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)) (mult beta eps))
                      (req_plus_compat (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos))) (fe_a p Hp)
                                       (mult beta eps) (mult beta eps)
                                       (req_sym (fe_a p Hp)
                                                (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                                                Hdec)
                                       (req_refl (mult beta eps))))).
Qed.

(* ---- 4.2 主定理（精确形，Id rlhf_optimal@L19049 对位）：J(p) <= J(pistar) ---- *)
(* 证明结构沿 Id 原件：KL 分解 ⟹ F(pb) <= F(p)（KL>=0 桥）⟹ F(pb)==F(pistar)
   ⟹ req_le_compat 换元 ⟹ opp_le_compat 取负。 *)
Theorem a_rlhf_optimal :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    le (J_a p Hp) (J_a pi_star_a a_pi_star_pos).
Proof.
  intros p Hn Hp.
  unfold J_a.
  assert (Hkl0 : (le zero (kl_a p pb_a Hp a_pb_pos)))
    by exact (b_gibbs_pos p pb_a Hp a_pb_pos Hn a_pb_normalized).
  assert (Hklb : (le zero (mult beta (kl_a p pb_a Hp a_pb_pos)))).
  { apply (le_id_r zero (mult (kl_a p pb_a Hp a_pb_pos) beta)
                   (mult beta (kl_a p pb_a Hp a_pb_pos))
                   (mult_comm (kl_a p pb_a Hp a_pb_pos) beta)
                   (le_id_l zero (mult zero beta) (mult (kl_a p pb_a Hp a_pb_pos) beta)
                            (req_trans zero (mult beta zero) (mult zero beta)
                                       (req_sym (mult beta zero) zero (mult_zero beta))
                                       (mult_comm beta zero))
                            (le_mult_compat zero (kl_a p pb_a Hp a_pb_pos) beta beta_pos Hkl0))). }
  assert (Hmin : (le (fe_a pb_a a_pb_pos) (fe_a p Hp))).
  { apply (le_id_r (fe_a pb_a a_pb_pos)
                   (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                   (fe_a p Hp)
                   (req_sym (fe_a p Hp)
                            (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                            (a_fe_kl_decomp p Hn Hp))
                   (le_id_l (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) zero)
                            (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                            (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                                     (plus_zero (fe_a pb_a a_pb_pos)))
                            (le_plus_compat (fe_a pb_a a_pb_pos) (fe_a pb_a a_pb_pos) zero
                                            (mult beta (kl_a p pb_a Hp a_pb_pos))
                                            (le_refl (fe_a pb_a a_pb_pos)) Hklb))). }
  apply (opp_le_compat (fe_a (fun s : S => pi_star_a s) a_pi_star_pos) (fe_a p Hp)).
  apply (req_le_compat (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)
                       (fe_a p Hp) (fe_a p Hp)
                       a_fe_boltzmann_pistar (req_refl (fe_a p Hp)) Hmin).
Qed.

(* ---- 4.2 主定理（Bishop 逐 eps 形，real_rlhf_optimal_eps@L43804 对位）：
   J(p) <= J(pistar) + beta·eps ---------------------------------------------- *)
(* 环收尾恒等：A + opp X <= B ⟹ A <= B + X（Real 层同构步骤的 req 版） *)
Theorem a_rlhf_optimal_eps :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p) (eps : R),
    lt zero eps ->
    le (J_a p Hp) (plus (J_a pi_star_a a_pi_star_pos) (mult beta eps)).
Proof.
  intros p Hn Hp eps Heps.
  unfold J_a.
  assert (Hmin : (le (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps))))
    by exact (a_min_free_energy_eps p Hn Hp eps Heps).
  assert (Hopp : (le (opp (plus (fe_a p Hp) (mult beta eps))) (opp (fe_a pb_a a_pb_pos))))
    by exact (opp_le_compat (fe_a pb_a a_pb_pos) (plus (fe_a p Hp) (mult beta eps)) Hmin).
  assert (H3a : (le (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (opp (fe_a pb_a a_pb_pos)))).
  { apply (le_id_l (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                   (opp (plus (fe_a p Hp) (mult beta eps)))
                   (opp (fe_a pb_a a_pb_pos))).
    - exact (req_sym (opp (plus (fe_a p Hp) (mult beta eps)))
                     (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                     (req_opp_plus (fe_a p Hp) (mult beta eps))).
    - exact Hopp. }
  assert (H3b : (le (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))
                    (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps)))).
  { apply (le_plus_compat (plus (opp (fe_a p Hp)) (opp (mult beta eps)))
                          (opp (fe_a pb_a a_pb_pos))
                          (mult beta eps) (mult beta eps)).
    - exact H3a.
    - apply le_refl. }
  assert (H3c : (req (opp (fe_a p Hp)) (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps)))).
  { apply (req_trans (opp (fe_a p Hp)) (plus (opp (fe_a p Hp)) zero)
                     (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))).
    - exact (req_sym (plus (opp (fe_a p Hp)) zero) (opp (fe_a p Hp)) (plus_zero (opp (fe_a p Hp)))).
    - apply (req_trans (plus (opp (fe_a p Hp)) zero)
                       (plus (opp (fe_a p Hp)) (plus (opp (mult beta eps)) (mult beta eps)))
                       (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))).
      + apply (req_plus_compat (opp (fe_a p Hp)) (opp (fe_a p Hp)) zero (plus (opp (mult beta eps)) (mult beta eps))).
        * apply req_refl.
        * apply (req_sym (plus (opp (mult beta eps)) (mult beta eps)) zero).
          apply (req_trans (plus (opp (mult beta eps)) (mult beta eps)) (plus (mult beta eps) (opp (mult beta eps))) zero).
          -- apply plus_comm.
          -- apply plus_opp.
      + apply plus_assoc. }
  assert (Hs3 : (le (opp (fe_a p Hp)) (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps)))).
  { apply (le_id_l (opp (fe_a p Hp))
                   (plus (plus (opp (fe_a p Hp)) (opp (mult beta eps))) (mult beta eps))
                   (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps))).
    - exact H3c.
    - exact H3b. }
  apply (le_id_r (opp (fe_a p Hp))
                 (plus (opp (fe_a pb_a a_pb_pos)) (mult beta eps))
                 (plus (opp (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)) (mult beta eps))).
    - apply (req_plus_compat (opp (fe_a pb_a a_pb_pos))
                             (opp (fe_a (fun s : S => pi_star_a s) a_pi_star_pos))
                             (mult beta eps) (mult beta eps)).
      + apply (req_opp_compat (fe_a pb_a a_pb_pos) (fe_a (fun s : S => pi_star_a s) a_pi_star_pos)).
        exact a_fe_boltzmann_pistar.
      + apply req_refl.
    - exact Hs3.
Qed.

(* ---- 4.3b DPO 最优性（Id dpo_optimal@L19096 对位）----
   DPO 隐式奖励具体化：dpo 损失 = -J(pi)，由 a_rlhf_optimal 直接推出。 *)
Definition dpo_loss_a (p : S -> R) (Hp : pdist_a p) : R := opp (J_a p Hp).

Theorem a_dpo_optimal :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    le (dpo_loss_a pi_star_a a_pi_star_pos) (dpo_loss_a p Hp).
Proof.
  intros p Hn Hp. unfold dpo_loss_a.
  apply (opp_le_compat (J_a p Hp) (J_a pi_star_a a_pi_star_pos)).
    exact (a_rlhf_optimal p Hn Hp).
Qed.

(* ---- 4.4 唯一性（Id rlhf_optimal_unique@L19128 对位）----
   J(p) == J(pistar) ⟹ p == pistar（逐点）。
   消去链：目标相等 ⟹ F 相等 ⟹ beta·KL == 0（加法消去）⟹ KL == 0
   （b_mult_cancel）⟹ 逐点（b_gibbs_eq）⟹ pi* 换元。req 世界无 destruct+eq_ind
   注入消去，此链为 (c.2) 消去引擎的 b 桥使用形态。 *)
Lemma a_add_cancel_r : forall (u v w : R), req (plus u v) (plus u w) -> req v w.
Proof.
  intros u v w H.
  apply (req_add_cancel_l v u w).
  apply (req_trans (plus v u) (plus u v) (plus w u)).
    apply plus_comm.
    apply (req_trans (plus u v) (plus u w) (plus w u)).
      exact H.
      apply plus_comm.
Qed.

Theorem a_rlhf_optimal_unique :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (J_a p Hp) (J_a pi_star_a a_pi_star_pos) ->
    forall s : S, req (p s) (pi_star_a s).
Proof.
  intros p Hn Hp HJ s.
  unfold J_a in HJ.
  assert (Hfe : (req (fe_a p Hp) (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos))).
  { exact (req_trans (fe_a p Hp) (opp (opp (fe_a p Hp)))
                     (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                     (req_sym (opp (opp (fe_a p Hp))) (fe_a p Hp) (req_double_neg (fe_a p Hp)))
                     (req_trans (opp (opp (fe_a p Hp)))
                                (opp (opp (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)))
                                (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                                (req_opp_compat (opp (fe_a p Hp))
                                                (opp (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos))
                                                HJ)
                                (req_double_neg (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)))). }
  assert (Hfe0 : (req (fe_a p Hp) (fe_a pb_a a_pb_pos)))
    by exact (req_trans (fe_a p Hp) (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                        (fe_a pb_a a_pb_pos) Hfe
                        (req_sym (fe_a pb_a a_pb_pos)
                                 (fe_a (fun s0 : S => pi_star_a s0) a_pi_star_pos)
                                 a_fe_boltzmann_pistar)).
  assert (Hdec : (req (fe_a p Hp) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (a_fe_kl_decomp p Hn Hp).
  assert (H1 : (req (fe_a pb_a a_pb_pos) (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))))
    by exact (req_trans (fe_a pb_a a_pb_pos) (fe_a p Hp)
                        (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                        (req_sym (fe_a p Hp) (fe_a pb_a a_pb_pos) Hfe0) Hdec).
  assert (H2 : (req (mult beta (kl_a p pb_a Hp a_pb_pos)) zero)).
  { apply (a_add_cancel_r (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)) zero).
    exact (req_trans (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                     (fe_a pb_a a_pb_pos)
                     (plus (fe_a pb_a a_pb_pos) zero)
                     (req_sym (fe_a pb_a a_pb_pos)
                              (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
                              H1)
                     (req_sym (plus (fe_a pb_a a_pb_pos) zero) (fe_a pb_a a_pb_pos)
                              (plus_zero (fe_a pb_a a_pb_pos)))). }
  assert (H3 : (req (kl_a p pb_a Hp a_pb_pos) zero))
    by exact (b_mult_cancel beta (kl_a p pb_a Hp a_pb_pos) beta_pos H2).
  exact (req_trans (p s) (pb_a s) (pi_star_a s)
                   (b_gibbs_eq p pb_a Hp a_pb_pos H3 s)
                   (a_boltzmann_is_pi_star s)).
Qed.

(* ---- 4.3 次优差距（Id rlhf_suboptimality_gap@L20554 对位）----
   J(pistar) − J(p) == beta·KL(p‖pistar)（前向 KL 显式值）。
   链：4.1 对齐实例 KL 分解（a_fe_kl_decomp）+ pb==pistar 双换元
   （F 左元 a_fe_boltzmann_pistar / KL 右元 a_KL_ext_r）
   + J = −F 双负消去（req_double_neg）+ A + opp(A+X) == X 环收尾
   （plus_assoc + plus_comm/plus_opp 消去）。全 req_trans 链，无 destruct。 *)
Theorem a_rlhf_suboptimality_gap :
  forall (p : S -> R) (Hn : nrm_a p) (Hp : pdist_a p),
    req (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp))
        (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)).
Proof.
  intros p Hn Hp.
  assert (Hkl : (req (kl_a p pb_a Hp a_pb_pos)
                     (kl_a p pi_star_a Hp a_pi_star_pos)))
    by exact (a_KL_ext_r p pb_a pi_star_a Hp a_pb_pos a_pi_star_pos
                (fun s0 : S => a_boltzmann_is_pi_star s0)).
  assert (Hdec : (req (fe_a p Hp)
                      (plus (fe_a pi_star_a a_pi_star_pos)
                            (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))))
    by exact (req_trans (fe_a p Hp)
               (plus (fe_a pb_a a_pb_pos) (mult beta (kl_a p pb_a Hp a_pb_pos)))
               (plus (fe_a pi_star_a a_pi_star_pos)
                     (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
               (a_fe_kl_decomp p Hn Hp)
               (req_plus_compat (fe_a pb_a a_pb_pos)
                                (fe_a pi_star_a a_pi_star_pos)
                                (mult beta (kl_a p pb_a Hp a_pb_pos))
                                (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                                a_fe_boltzmann_pistar
                                (req_mult_compat beta beta
                                   (kl_a p pb_a Hp a_pb_pos)
                                   (kl_a p pi_star_a Hp a_pi_star_pos)
                                   (req_refl beta) Hkl))).
  (* fe 形差距：opp F* + Fp == beta·KL（A + opp(A+X) == X 环收尾） *)
  assert (Hgapfe : (req (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                        (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))).
  { apply (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                     (plus (opp (fe_a pi_star_a a_pi_star_pos))
                           (plus (fe_a pi_star_a a_pi_star_pos)
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))))
                     (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
    - apply (req_plus_compat (opp (fe_a pi_star_a a_pi_star_pos))
                             (opp (fe_a pi_star_a a_pi_star_pos))
                             (fe_a p Hp)
                             (plus (fe_a pi_star_a a_pi_star_pos)
                                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))).
      + apply req_refl.
      + exact Hdec.
    - apply (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                             (plus (fe_a pi_star_a a_pi_star_pos)
                                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))))
                       (plus (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                   (fe_a pi_star_a a_pi_star_pos))
                             (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                       (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
      + apply plus_assoc.
      + apply (req_trans (plus (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                     (fe_a pi_star_a a_pi_star_pos))
                               (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                         (plus zero (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                         (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
        * apply (req_plus_compat (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                       (fe_a pi_star_a a_pi_star_pos))
                                 zero
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                                 (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
          -- exact (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                    (fe_a pi_star_a a_pi_star_pos))
                              (plus (fe_a pi_star_a a_pi_star_pos)
                                    (opp (fe_a pi_star_a a_pi_star_pos)))
                              zero
                              (plus_comm (opp (fe_a pi_star_a a_pi_star_pos))
                                         (fe_a pi_star_a a_pi_star_pos))
                              (plus_opp (fe_a pi_star_a a_pi_star_pos))).
          -- apply req_refl.
        * apply (req_trans (plus zero (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)))
                           (plus (mult beta (kl_a p pi_star_a Hp a_pi_star_pos)) zero)
                           (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))).
          -- apply plus_comm.
          -- apply plus_zero. }
  (* J 形出口：rminus_a J* Jp == opp F* + opp (opp Fp) == opp F* + Fp（δ+双负） *)
  exact (req_trans (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp))
                   (plus (opp (fe_a pi_star_a a_pi_star_pos))
                         (opp (opp (fe_a p Hp))))
                   (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                   (req_refl (rminus_a (J_a pi_star_a a_pi_star_pos) (J_a p Hp)))
                   (req_trans (plus (opp (fe_a pi_star_a a_pi_star_pos))
                                    (opp (opp (fe_a p Hp))))
                              (plus (opp (fe_a pi_star_a a_pi_star_pos)) (fe_a p Hp))
                              (mult beta (kl_a p pi_star_a Hp a_pi_star_pos))
                              (req_plus_compat (opp (fe_a pi_star_a a_pi_star_pos))
                                               (opp (fe_a pi_star_a a_pi_star_pos))
                                               (opp (opp (fe_a p Hp))) (fe_a p Hp)
                                               (req_refl (opp (fe_a pi_star_a a_pi_star_pos)))
                                               (req_double_neg (fe_a p Hp)))
                              Hgapfe)).
Qed.

(* ---- 4.4 策略改进单调性（Id rlhf_policy_improvement@L20591 对位）----
   KL(p_new‖pistar) <= KL(p_old‖pistar) ⟹ J(p_old) <= J(p_new)。
   链：4.3 差距恒等式 ×2（J* − Jq == β·KLq）+ β>0 左乘保序（le_mult_compat
   经 mult_comm 双换元到左乘位）+ 两侧加 opp J*（le_plus_compat）
   + opp J* + (J* + opp Jq) == opp Jq 消去串 + opp_le_compat 双负完成。 *)
Theorem a_rlhf_policy_improvement :
  forall (p_old p_new : S -> R)
         (Hn1 : nrm_a p_old) (Hp1 : pdist_a p_old)
         (Hn2 : nrm_a p_new) (Hp2 : pdist_a p_new),
    le (kl_a p_new pi_star_a Hp2 a_pi_star_pos)
       (kl_a p_old pi_star_a Hp1 a_pi_star_pos) ->
    le (J_a p_old Hp1) (J_a p_new Hp2).
Proof.
  intros p_old p_new Hn1 Hp1 Hn2 Hp2 Hkldec.
  assert (Hbeta : (le (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                      (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos)))).
  { exact (le_id_r (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                   (mult (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                   (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                   (mult_comm (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                   (le_id_l (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                            (mult (kl_a p_new pi_star_a Hp2 a_pi_star_pos) beta)
                            (mult (kl_a p_old pi_star_a Hp1 a_pi_star_pos) beta)
                            (mult_comm beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                            (le_mult_compat (kl_a p_new pi_star_a Hp2 a_pi_star_pos)
                                            (kl_a p_old pi_star_a Hp1 a_pi_star_pos)
                                            beta beta_pos Hkldec))). }
  (* 消去串：opp J* + (J* + opp Jq) == opp Jq（A+opp(A+X)==X 的 J 形） *)
  assert (Hsimpl : forall (q : S -> R) (Hq : pdist_a q),
    req (plus (opp (J_a pi_star_a a_pi_star_pos))
              (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a q Hq))))
        (opp (J_a q Hq))).
  { intros q Hq.
    apply (req_trans (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a q Hq))))
                     (plus (plus (opp (J_a pi_star_a a_pi_star_pos))
                                 (J_a pi_star_a a_pi_star_pos))
                           (opp (J_a q Hq)))
                     (opp (J_a q Hq))).
    - apply plus_assoc.
    - apply (req_trans (plus (plus (opp (J_a pi_star_a a_pi_star_pos))
                                   (J_a pi_star_a a_pi_star_pos))
                             (opp (J_a q Hq)))
                       (plus zero (opp (J_a q Hq)))
                       (opp (J_a q Hq))).
      + apply (req_plus_compat (plus (opp (J_a pi_star_a a_pi_star_pos))
                                     (J_a pi_star_a a_pi_star_pos))
                               zero
                               (opp (J_a q Hq)) (opp (J_a q Hq))).
        * exact (req_trans (plus (opp (J_a pi_star_a a_pi_star_pos))
                                 (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos)
                                 (opp (J_a pi_star_a a_pi_star_pos)))
                           zero
                           (plus_comm (opp (J_a pi_star_a a_pi_star_pos))
                                      (J_a pi_star_a a_pi_star_pos))
                           (plus_opp (J_a pi_star_a a_pi_star_pos))).
        * apply req_refl.
      + apply (req_trans (plus zero (opp (J_a q Hq)))
                         (plus (opp (J_a q Hq)) zero)
                         (opp (J_a q Hq))).
        * apply plus_comm.
        * apply plus_zero. }
  (* J* − J_new <= J* − J_old（4.3 ×2 换元 + β 保序） *)
  assert (Hadd : (le (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))))).
  { apply (le_plus_compat (opp (J_a pi_star_a a_pi_star_pos))
                          (opp (J_a pi_star_a a_pi_star_pos))
                          (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2)))
                          (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                          (le_refl (opp (J_a pi_star_a a_pi_star_pos)))).
    apply (le_id_l (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2)))
                   (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                   (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))).
    - exact (a_rlhf_suboptimality_gap p_new Hn2 Hp2).
    - apply (le_id_r (mult beta (kl_a p_new pi_star_a Hp2 a_pi_star_pos))
                     (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                     (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                     (req_sym (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1)))
                              (mult beta (kl_a p_old pi_star_a Hp1 a_pi_star_pos))
                              (a_rlhf_suboptimality_gap p_old Hn1 Hp1))
                     Hbeta). }
  assert (Hopp : (le (opp (J_a p_new Hp2)) (opp (J_a p_old Hp1)))).
  { apply (le_id_l (opp (J_a p_new Hp2))
                   (plus (opp (J_a pi_star_a a_pi_star_pos))
                         (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                   (opp (J_a p_old Hp1))).
    - exact (req_sym (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (opp (J_a p_new Hp2))
                     (Hsimpl p_new Hp2)).
    - apply (le_id_r (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_new Hp2))))
                     (plus (opp (J_a pi_star_a a_pi_star_pos))
                           (plus (J_a pi_star_a a_pi_star_pos) (opp (J_a p_old Hp1))))
                     (opp (J_a p_old Hp1))
                     (Hsimpl p_old Hp1) Hadd). }
  exact (le_id_l (J_a p_old Hp1)
                 (opp (opp (J_a p_old Hp1)))
                 (J_a p_new Hp2)
                 (req_sym (opp (opp (J_a p_old Hp1))) (J_a p_old Hp1)
                          (req_double_neg (J_a p_old Hp1)))
                 (le_id_r (opp (opp (J_a p_old Hp1)))
                          (opp (opp (J_a p_new Hp2)))
                          (J_a p_new Hp2)
                          (req_double_neg (J_a p_new Hp2))
                          (opp_le_compat (opp (J_a p_new Hp2)) (opp (J_a p_old Hp1)) Hopp))).
Qed.

End ReqAlignCore.
(* ============================================================ *)
(* Part C：两状态具体实例装配消解 + 端到端主定理                    *)
(*   R := Real（Instance RealEnhancedReal 消解；req ≡ real_eq），   *)
(*   S := bool（两状态），sumf := real_list_sum f [true; false]。  *)
(*   链路：具体实例装配 → §4.1 核心定理使用 → G3 提取检验          *)
(*   （upsigmigrate2_probe.ml，Obj.magic=0）。                     *)
(* ============================================================ *)

Definition bsum (f : bool -> Real) : Real :=
  real_list_sum bool f (cons true (cons false nil)).

(* ---- 实例装配：求和三性质消解（使用基座 real_list_sum 三件） ---- *)
Lemma c_sum_ext :
  forall f g : bool -> Real, (forall s : bool, req (f s) (g s)) -> req (bsum f) (bsum g).
Proof.
  intros f g H.
  exact (real_list_sum_ext bool f g (true :: false :: nil) H).
Qed.

Lemma c_sum_add :
  forall f g : bool -> Real,
    req (bsum (fun s : bool => real_plus (f s) (g s)))
        (real_plus (bsum f) (bsum g)).
Proof.
  intros f g.
  exact (real_list_sum_add bool f g (true :: false :: nil)).
Qed.

Lemma c_sum_linear :
  forall (a : Real) (f : bool -> Real),
    req (bsum (fun s : bool => real_mult a (f s))) (real_mult a (bsum f)).
Proof.
  intros a f.
  exact (real_list_sum_linear bool a f (true :: false :: nil)).
Qed.

(* ---- 实例参数：D := 1，Z := 2（全部具体构造） ---- *)
Definition two_state_loss : bool -> Real := fun _ : bool => real_zero.
Definition two_state_Z : Real := real_plus real_one real_one.
Definition two_state_Z_pos : lt zero two_state_Z :=
  real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one.

(* 透明 Def：收拢 tactic 期实例-evar 易碎位（内核层 Definition 转换已验） *)
Definition two_state_inv_one : Real := inv_pos real_one real_lt_zero_one.

Lemma c_exp_neg_zero :
  req (exp_neg (mult (two_state_inv_one) real_zero)) real_one.
Proof.
  exact (req_trans (exp_neg (mult (two_state_inv_one) real_zero))
                   (exp_neg real_zero) real_one
                   (req_exp_neg_ext (mult (two_state_inv_one) real_zero)
                                    real_zero
                                    (mult_zero (two_state_inv_one)))
                   exp_neg_zero).
Qed.

(* partition 消解：e^{-0}+e^{-0} == 1+1 == Z（纯实例代数）
   证明注记：原稿为单体式（19 行全显式参 exact）；本世系零参类字段经全局实例
   投影，单体项的逐节点记录展开代价超线性（-time 实测该命令滞留 >小时级），
   故同链分解为 H1/H2 两步（语句不变，全构造性，无新前提）。 *)
Lemma c_partition :
  req two_state_Z
      (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero))).
Proof.
  set (e := exp_neg (mult (two_state_inv_one) real_zero)).
  assert (H1 : req two_state_Z (real_plus e e)).
  { exact (req_plus_compat real_one e real_one e
             (req_sym e real_one c_exp_neg_zero)
             (req_sym e real_one c_exp_neg_zero)). }
  assert (H2 : req (real_plus e e)
                   (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero)))).
  { exact (req_sym (real_plus e (real_plus e zero)) (real_plus e e)
             (req_plus_compat e e (real_plus e zero) e
                (req_refl e) (plus_zero e))). }
  exact (req_trans two_state_Z (real_plus e e)
                   (bsum (fun s : bool => exp_neg (mult (two_state_inv_one) real_zero)))
                   H1 H2).
Qed.

(* ---- 装配件：Boltzmann 分布及其正性（Part A 出口件实例化） ---- *)
Definition two_state_boltz : bool -> Real :=
  boltzmann_dist_m2 bool two_state_loss real_one real_lt_zero_one
                    two_state_Z two_state_Z_pos.

Definition two_state_boltz_pos : forall s : bool, lt zero (two_state_boltz s) :=
  req_boltzmann_positive bool two_state_loss real_one real_lt_zero_one
                         two_state_Z two_state_Z_pos.

(* ============================================================ *)
(* 端到端主定理 #1：§4.1 核心定理 req_free_energy_boltzmann 使用     *)

(* ============================================================ *)
Theorem two_state_free_energy_boltzmann :
  req (free_energy_m2 bool bsum two_state_loss real_one
           two_state_boltz two_state_boltz_pos)
      (opp (mult real_one (log two_state_Z two_state_Z_pos))).
Proof.
  exact (req_free_energy_boltzmann bool bsum c_sum_ext c_sum_add c_sum_linear
           two_state_loss real_one real_lt_zero_one two_state_Z two_state_Z_pos
           c_partition real_log_exp_neg real_log_wd).
Qed.

(* ---- 均匀策略 p_u = (1/2, 1/2) 及其正性/归一化 ---- *)
Definition two_state_pu : bool -> Real :=
  fun _ : bool => inv_pos two_state_Z two_state_Z_pos.

Lemma two_state_pu_pos : forall s : bool, lt zero (two_state_pu s).
Proof.
  intro s. exact (inv_pos_pos two_state_Z two_state_Z_pos).
Qed.

(* 左乘消去引擎（t > 0，req (t·x) (t·y) ⟹ req x y；req 世界无 destruct
   注入消去，经 inv_pos_correct 环绕链构造——(c.2) 消去引擎实例形态） *)
Lemma c_mult_cancel_l :
  forall (t x y : Real), lt zero t -> req (mult t x) (mult t y) -> req x y.
Proof.
  intros t x y Ht H.
  assert (Hix1 : req (mult (inv_pos t Ht) t) one).
  { exact (req_trans (mult (inv_pos t Ht) t) (mult t (inv_pos t Ht)) one
                     (mult_comm (inv_pos t Ht) t) (inv_pos_correct t Ht)). }
  exact (req_trans x (mult (mult (inv_pos t Ht) t) x) y
           (req_trans x (mult one x) (mult (mult (inv_pos t Ht) t) x)
              (req_sym (mult one x) x (req_mult_one_l x))
              (req_mult_compat one (mult (inv_pos t Ht) t) x x
                 (req_sym (mult (inv_pos t Ht) t) one Hix1) (req_refl x)))
           (req_trans (mult (mult (inv_pos t Ht) t) x) (mult (inv_pos t Ht) (mult t x)) y
              (req_sym (mult (inv_pos t Ht) (mult t x)) (mult (mult (inv_pos t Ht) t) x)
                 (mult_assoc (inv_pos t Ht) t x))
              (req_trans (mult (inv_pos t Ht) (mult t x)) (mult (inv_pos t Ht) (mult t y)) y
                 (req_mult_compat (inv_pos t Ht) (inv_pos t Ht) (mult t x) (mult t y)
                    (req_refl (inv_pos t Ht)) H)
                 (req_trans (mult (inv_pos t Ht) (mult t y)) (mult (mult (inv_pos t Ht) t) y) y
                    (mult_assoc (inv_pos t Ht) t y)
                    (req_trans (mult (mult (inv_pos t Ht) t) y) (mult one y) y
                       (req_mult_compat (mult (inv_pos t Ht) t) one y y Hix1 (req_refl y))
                       (req_mult_one_l y)))))).
Qed.

(* p_u 归一化：1/2 + 1/2 == 1（2·配对 == 2·1 消去引擎实例化）
   证明注记：原稿为单体式（36 行全显式参 exact）；本世系零参类字段经全局实例
   投影，单体项与投影/实面混写的逐节点记录展开代价超线性（-time 实测单项
   264s 量级），故同链改写：中间步全取 real_eq/real_plus/real_mult 实面
   （S02 real_eq_trans/sym/refl、real_distrib、real_plus_zero、real_mult_one、
   S03 real_inv_pos_correct、S07 RealSetoid.real_eq_plus_compat_adapt），
   记录展开只余边界少数位（语句不变，全构造性，无新前提）。 *)
Lemma c_pu_normalized : req (bsum two_state_pu) one.
Proof.
  set (u := real_inv_pos two_state_Z two_state_Z_pos).
  assert (Hd1 : real_eq (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                        (real_mult two_state_Z one)).
  { exact (real_eq_trans (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                         two_state_Z (real_mult two_state_Z one)
             (RealSetoid.real_eq_plus_compat_adapt (real_mult two_state_Z u) real_one
                              (real_mult two_state_Z u) real_one
                              (real_inv_pos_correct two_state_Z two_state_Z_pos)
                              (real_inv_pos_correct two_state_Z two_state_Z_pos))
             (real_eq_sym (real_mult two_state_Z one) two_state_Z
                          (real_mult_one two_state_Z))). }
  assert (Hd : real_eq (real_mult two_state_Z (real_plus u u))
                       (real_mult two_state_Z one)).
  { exact (real_eq_trans (real_mult two_state_Z (real_plus u u))
                         (real_plus (real_mult two_state_Z u) (real_mult two_state_Z u))
                         (real_mult two_state_Z one)
                         (real_distrib two_state_Z u u) Hd1). }
  assert (Hc : real_eq (real_plus u u) real_one).
  { exact (c_mult_cancel_l two_state_Z (real_plus u u) real_one two_state_Z_pos Hd). }
  assert (Hs : real_eq (bsum two_state_pu) (real_plus u u)).
  { exact (RealSetoid.real_eq_plus_compat_adapt u u (real_plus u real_zero) u
             (real_eq_refl u) (real_plus_zero u)). }
  exact (real_eq_trans (bsum two_state_pu) (real_plus u u) real_one Hs Hc).
Qed.

(* ============================================================ *)
(* 端到端主定理 #2：§4.1 核心定理 req_free_energy_kl_decomp 使用     *)
(*   均匀策略 p_u 的自由能-KL 分解（可提取 Set 层语句）            *)
(* ============================================================ *)
Theorem two_state_free_energy_kl_flagship :
  req (free_energy_m2 bool bsum two_state_loss real_one
           two_state_pu two_state_pu_pos)
      (plus (free_energy_m2 bool bsum two_state_loss real_one
                  two_state_boltz two_state_boltz_pos)
            (mult real_one
                  (bsum (fun s : bool =>
                    mult (two_state_pu s)
                         (rminus_m2 (log (two_state_pu s) (two_state_pu_pos s))
                                    (log (two_state_boltz s) (two_state_boltz_pos s))))))).
Proof.
  exact (req_free_energy_kl_decomp bool bsum c_sum_ext c_sum_add c_sum_linear
           two_state_loss real_one real_lt_zero_one two_state_Z two_state_Z_pos
           c_partition real_log_exp_neg real_log_wd
           two_state_pu c_pu_normalized two_state_pu_pos).
Qed.
