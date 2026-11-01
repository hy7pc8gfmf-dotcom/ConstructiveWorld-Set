(* ==========================================================================)
   G01_CoreMicro.v — 微观核心杂件：对数号律、softmax 自由能闭式与组优势方差非负
   使命: hlogz_discharge/hlogz_strict（Za≤1 ⟹ log Za ≤ 0 号律）、free_energy_softmax_eq_neg_T_logZ（F(softmax) == −T·log Z）、ufep_attention_minimizes_free_energy_unique（自由能极小唯一）与双副本枚举反例（indicator2 求和、组相对优势 A2 平方和非负条件）。
   依赖: S01–S15 现役代直挂、AttnDoeblin；Stdlib List、PeanoNat、Extraction
   对标: Boltzmann–Gibbs 自由能变分原理与组相对策略优化（GRPO）优势二阶矩非负性。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   洗形: abl18 闭包实扫——UpLogMono 四引理已由 S14:14708–14741 同名同证晋升、
   UpPPO 六件已由 S15:212–339 同名同证晋升，本件去重回归现役（语句面零损失，名面经
   Require 传递）；boltzmann_dist 新代直展 exp_neg（对齐式去 boltzmann_factor 展开位）。
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

(* ================================================================ *)
(* 主结果 1：HlogZ 证明（log 单调 le 版直推）                          *)
(*   论证：0 < Za、Za ≤ 1 ⟹ real_log Za ≤ real_log 1 == 0。           *)
(*   real_log_le_mono : real_le a b -> real_le (log a) (log b)       *)
(*   （a b 皆正前提由 HZa 与 real_lt_zero_one 供给）。                 *)
(* ================================================================ *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* 经中项 real_log 1 的 le 链合成 *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* 单调 le 版：Za ≤ 1 ⟹ log Za ≤ log 1 *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* log 1 == 0 经 eq → le 桥（inr 支）升 le *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* ================================================================ *)
(* 主结果 2：HlogZ 证明完整版（与 KLProjection 前提对齐）               *)
(*   同型语句，走 UpLogMono 直用形态 real_log_le_zero_of_le_one，      *)
(*   双路互证（单调链合成 / 直用形态殊途同归）。                        *)
(* ================================================================ *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* ================================================================ *)
(* 附加结果 1：严格版——过滤器确实拦截了质量                            *)
(*   0 < Za < 1 ⟹ log Za < log 1 = 0（lt 严格链）。                   *)
(*   real_log_lt_mono 论 cw_log；real_log 定义性展开（:= cw_log）后    *)
(*   逐项对接，尾端经 real_lt_eq_lt 把 log 1 换成 0。                  *)
(* ================================================================ *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* 严格单调：Za < 1 ⟹ cw_log Za < cw_log 1 *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* cw_log 1 == 0 *)
    exact (real_log_one Hone).
Qed.

(* ================================================================ *)
(* 附加结果 2：KL 尾项形态——0 ≤ opp (log Z)                           *)
(*   主定理证明里「尾项 T == opp (log Z_aud) ≥ 0」的直接 Real 层供给：  *)
(*   log Z ≤ 0 经 opp 反变（real_opp_le_compat）→ opp 0 ≤ opp (log Z)，*)
(*   再用 opp 0 == 0 的 eq → le 桥（inl 支？否，inr 支）合成。          *)
(* ================================================================ *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* 0 ≤ opp 0：eq 对称后升 le *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* opp 0 ≤ opp (log Z)：反变 + 主结果 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* 提取检验（Warning 消音：透明度旁路访问清单提示，与 UpGRPO 同法） *)
Set Warnings "-extraction-opaque-accessed".

(* ======== G01_CoreMicro 成员件：UpExtras（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpExtras.v —— 二轮轻包·三件独立小定理                         *)
(*                                                                *)
(* 件1（P5b）：log-sum-exp = 负自由能。以 base_loss := −z、D := T  *)
(*   实例化根内 free_energy_boltzmann（对 base_loss/D/Z 全泛化）， *)
(*   配逐点对齐引理（softmax_temp 逐点 = boltzmann_dist，经        *)
(*   opp_mult_l + exp_pos_fn 展开 + 配分函数定义性）与自由能外延   *)
(*   引理，得：F_attn[softmax_temp(z)] == −T·log Z_T(z)。          *)
(*   论文 2 §5.4(b) interpretation 升格为机器检查恒等式。          *)
(*                                                                *)
(* 件2：GRPO 双副本反例（NoDup 不可去性的构造性见证）。           *)
(*   Group := nat，enum2 := [O; O]（同一元素两份，NoDup 失效）：   *)
(*   indicator 求和 == 1+1 == 2 ≠ 1——均匀均值解读中每份 delta      *)
(*   质量变为 2/G，G=2 时整体质量翻倍。常数奖励版总计 2c ≠ c。     *)
(*                                                                *)
(* 件3：Var ≥ 0 的条件形态（Real 层）。                            *)
(*   real_var_nonneg_cond：若逐项平方非负（接口假设，副本根内      *)
(*   GRPO §7.3 的 square_nonneg Variable——构造性有序域无三分律，   *)
(*   通用平方非负必须诚实接口），则 Σ A_i² ≥ 0（求和保序）。       *)
(*   这正是根内 GRPO §7.3 的求和侧副本，非降级形态。               *)
(*                                                                *)
(* 红线：零公理、零弃证、零接口逃逸、零经典律；Set 层语句； *)
(* 全 Qed。自足：不 Require UpFEP/UpGRPO/AttnDoeblin。              *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
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

(* ################ 件1（P5b）：log-sum-exp = 负自由能 ################ *)

Section FEPLogZ.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let log := @log RI.

(* softmax 配分正性的显式接口假设（同根内 AttentionGibbsBridge 区   *)
(* Variable sum_pos_preserved 的同根形态） *)
Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.

Let base : S -> R := fun s : S => opp (z s).
Let invT := inv_pos T T_pos.
Let Zf := partition_function_temp T T_pos z.
Let Zf_pos := partition_function_temp_pos spp T T_pos z.
Let F_attn (p : S -> R) : R := free_energy base T p.

(* 配分条件：温度配分函数满足 free_energy 三件套的 Z 规范
   Z == Σ_s exp_neg(invT · base s)（exp_pos_fn 定义性展开） *)
Lemma uex_fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.  unfold Zf, partition_function_temp, base.
  exact (sum_over_S_ext _ _
    (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* 对齐引理：Boltzmann 分布（能量 −z、温度 T）逐点 = 温度 softmax *)
Lemma uex_fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.  intro s. unfold boltzmann_dist, softmax_temp, exp_pos_fn.
  exact (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))
           (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s))) (id_refl))).
Qed.

(* F 外延：逐点相等的分布给出相等的自由能（base_loss/T 固定） *)
Lemma uex_fep_F_ext : forall p q : S -> R,
  (forall s : S, Id (p s) (q s)) -> Id (F_attn p) (F_attn q).
Proof.
  intros p q Hpt. unfold F_attn, free_energy.
  apply (id_cong2 plus).
  - apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_refl : Id (base s) (base s)))).
  - apply (id_cong (fun w : R => mult T w)).
    apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_cong log (Hpt s)))).
Qed.

(* ========== P5b 主定理：log-sum-exp = 负自由能 ==========
   F_attn[softmax_temp(z)] == −T · log Z_T(z)：
   softmax 逐点 = boltzmann（uex_fep_align）→ F 外延 →
   根内 free_energy_boltzmann（base_loss := −z, D := T）证明。 *)
Theorem free_energy_softmax_eq_neg_T_logZ :
  Id (F_attn (softmax_temp spp T T_pos z))
     (mult (opp T) (log Zf)).
Proof.  exact (id_trans (uex_fep_F_ext (softmax_temp spp T T_pos z)
                             (boltzmann_dist base T T_pos Zf Zf_pos)
                             (fun s : S => id_sym (uex_fep_align s)))
            (free_energy_boltzmann base T T_pos Zf Zf_pos uex_fep_partition_condition)).
Qed.

End FEPLogZ.

(* ################ 件2：GRPO 双副本反例（NoDup 不可去性） ################ *)

Section GRPOCounterEx.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let lt := @lt RI.

(* 自备组求和（副本根内 GRPO Section 的 list_sum_g；Group 固定 nat—— *)
(* 可判定相等天然，Nat.eq_dec 供 indicator 分支） *)
Fixpoint list_sum_g2 (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => zero
  | i :: rest => plus (f i) (list_sum_g2 f rest)
  end.

(* 常数奖励：任意 c > 0（均值无信息，反例与 c 的取值无关） *)
Variable c : R.
Variable c_pos : lt zero c.
Definition reward2 : nat -> R := fun _ => c.

(* 双副本枚举：同一元素 O 出现两次——NoDup 不成立的合法 list *)
(* indicator：均匀均值解读中「成员 i 是否为组代表」的权重函数      *)
Definition indicator2 : nat -> R :=
  fun i : nat =>
    match Nat.eq_dec i O with
    | left _ => one
    | right _ => zero
    end.

(* ========== 构造性见证：双副本下 indicator 求和 == 2 ≠ 1 ==========
   均匀均值解读失效的机理：单副本下 Σ_i indicator(i) == 1（恰一代表），
   双副本使求和 == plus one one == 2——每个 delta 质量变为 2/G
   （G = 组大小），G=2 时指示质量翻倍，「每元素恰一次」规范被破坏。
   这是数值反例：两条 statement 全由 simpl + plus_zero 组装闭合。 *)
Theorem counter_ex_indicator_sum_two :
  Id (list_sum_g2 indicator2 [O; O])
     (plus one one).
Proof.  simpl.
  exact (id_cong (fun x => plus one x) (plus_zero one)).
Qed.

(* 同根见证：常数奖励在双副本下的总质量 == 2c ≠ c（单副本）， *)
(* 均值 (1/2)·2c 仍为 c——奖励信息不因复制而增，指示质量却翻倍。 *)
Theorem counter_ex_reward_sum_two_c :
  Id (list_sum_g2 reward2 [O; O])
     (plus c c).
Proof.  simpl.
  exact (id_cong (fun x => plus c x) (plus_zero c)).
Qed.

End GRPOCounterEx.

(* ################ 件3：Var ≥ 0 的条件形态（Real 层） ################ *)

Section RealVarNonNeg.
Variable Grp2 : Set.
Variable enum2 : list Grp2.
Variable reward2 : Grp2 -> Real.
(* 组大小正性：enum 非空 ⟹ length ≥ 1 ⟹ of_nat (length) > 0 *)
Variable Hpos : real_lt real_zero (real_of_nat (length enum2)).

(* 组均值 μ = (1/G)·Σ r_i（Real 层，副本根内 GRPO group_mean） *)
Definition mean2 : Real :=
  real_mult (real_inv_pos (real_of_nat (length enum2)) Hpos)
            (real_list_sum_g Grp2 reward2 enum2).

(* 组相对优势 A_i = r_i − μ（Real 层，副本根内 GRPO grpo_advantage） *)
Definition A2 (i : Grp2) : Real := real_plus (reward2 i) (real_opp mean2).

(* 逐项平方非负 ⟹ 求和非负（有限列表归纳 + real_le_plus_compat；
   副本根内 real_list_sum_nonneg 的证明骨架，fold 换 real_list_sum_g） *)
Lemma sq_sum_list_nonneg : forall l : list Grp2,
  (forall i : Grp2, real_le real_zero (real_mult (A2 i) (A2 i))) ->
  real_le real_zero
    (real_list_sum_g Grp2 (fun i : Grp2 => real_mult (A2 i) (A2 i)) l).
Proof.
  intros l Hsq.
  induction l as [| i rest IH]; cbn [real_list_sum_g].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)
             (real_plus (real_mult (A2 i) (A2 i))
                        (real_list_sum_g Grp2
                           (fun i0 : Grp2 => real_mult (A2 i0) (A2 i0)) rest))).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply real_plus_zero.
    + apply (real_le_plus_compat real_zero (real_mult (A2 i) (A2 i))
               real_zero
               (real_list_sum_g Grp2
                  (fun i0 : Grp2 => real_mult (A2 i0) (A2 i0)) rest)).
      * apply Hsq.
      * exact IH.
Qed.

(* ========== Var ≥ 0（条件形态，根内 GRPO §7.3 的求和侧副本） ==========
   逐项平方非负是接口假设（构造性有序域无三分律，通用平方非负需
   接口字段——与根内 GRPO §7.3 的 Variable square_nonneg 同款诚实
   接口纪律）；此处给出其求和侧：给定逐项假设，Σ A_i² ≥ 0 由求和
   保序纯构造性证明。GRPO σ 定理的 Var 前提供即此形态。 *)
Theorem real_var_nonneg_cond :
  (forall i : Grp2, real_le real_zero (real_mult (A2 i) (A2 i))) ->
  real_le real_zero
    (real_list_sum_g Grp2 (fun i : Grp2 => real_mult (A2 i) (A2 i)) enum2).
Proof.
  exact (sq_sum_list_nonneg enum2).
Qed.

End RealVarNonNeg.

(* 提取检验：件1/件2 的计算构造可提取 *)
(* 注：softmax_temp 计算性使用 Qed 引理 partition_function_temp_pos， *)
(* 提取旁路透明度为 Coq 提取的标准信息性警告（UpFEP 同款），显式抑制； *)
(* 提取目录显式设定为当前目录，保持与默认一致的输出位置。 *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upextras.ml" softmax_temp partition_function_temp free_energy
  list_sum_g2 reward2 indicator2.

(* ======== G01_CoreMicro 成员件：UpFEP（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpFEP.v —— 二轮快赢批·P5：attention = 变分自由能的唯一最小点      *)
(*            + 行视图引理（bs_kernel 行 = 单查询 softmax_temp）      *)
(*                                                                *)
(* P5（FEP × Gibbs 桥闭合，纯组装）：以 base_loss := −z、D := T      *)
(*   实例化自由能-KL 分解三件套（free_energy_kl_decomp/             *)
(*   min_free_energy_is_boltzmann/free_energy_min_unique，对        *)
(*   base_loss/D/Z 全泛化），配对齐引理（boltzmann 因子 = softmax    *)
(*   分子，经 opp_mult_l）与 F 外延引理，得：                       *)
(*   softmax_temp z 是 F_T[p] = −E_p[z] + T·Σ p log p 的唯一最小点。  *)
(*   把论文 2 §5.4(b) 的「attention 侧自由能最小化」从 interpretation *)
(*   升格为机器检查定理；§9.1 统一视角补上 FEP-attention 缺环。       *)
(* 行视图：AttnDoeblin 的行 softmax 核 bs_kernel 的每一行与论文      *)
(*   §5.2 的单查询 softmax_temp 是同一对象（经 expf 与 exp_pos_fn    *)
(*   的一致性前提）——论文 2 §10.2 点名的对接件。                     *)
(* 红线：零 公理/承认件；Set 层语句；全 Qed。                    *)
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
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import AttnDoeblin.

(* ################ Part 1：P5 FEP 闭环 ################ *)

Section FEPAttention.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let log := @log RI.

Variable z : S -> R.
Variable T : R.
Variable T_pos : lt zero T.
Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

Let base : S -> R := fun s : S => opp (z s).
Let invT := inv_pos T T_pos.
Let Zf := partition_function_temp T T_pos z.
Let Zf_pos := partition_function_temp_pos spp T T_pos z.
Let F_attn (p : S -> R) : R := free_energy base T p.

(* 配分条件：softmax 配分函数满足 free_energy 三件套的 Z 规范 *)
Lemma ufep_fep_partition_condition :
  Id Zf (sum_over_S (fun s : S => exp_neg (mult invT (base s)))).
Proof.  unfold Zf, partition_function_temp, base.
  exact (sum_over_S_ext _ _ (fun s : S => id_cong exp_neg (id_sym (opp_mult_l invT (z s))))).
Qed.

(* 对齐引理：Boltzmann 分布（能量 −z、温度 T）逐点 = softmax_temp z *)
(* [abl18 洗形] 现役代 S04 boltzmann_dist 直展 exp_neg（不经 boltzmann_factor）， *)
(* 展开位随之去 boltzmann_factor（与件内 uex_fep_align 展开面对齐）。 *)
Lemma ufep_fep_align : forall s : S,
  Id (boltzmann_dist base T T_pos Zf Zf_pos s) (softmax_temp spp T T_pos z s).
Proof.  intro s. unfold boltzmann_dist, softmax_temp, exp_pos_fn.
  exact (id_trans (mult_comm (inv_pos Zf Zf_pos) (exp_neg (mult invT (base s))))
           (id_cong2 mult (id_cong exp_neg (opp_mult_l invT (z s))) (id_refl))).
Qed.

(* F 外延：逐点相等的归一化分布给出相等的自由能 *)
Lemma ufep_fep_F_ext : forall p q : S -> R,
  normalized p -> normalized q -> (forall s : S, Id (p s) (q s)) ->
  Id (F_attn p) (F_attn q).
Proof.
  intros p q Hp Hq Hpt. unfold F_attn, free_energy.
  apply (id_cong2 plus).
  - apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_refl : Id (base s) (base s)))).
  - apply (id_cong (fun w : R => mult T w)).
    apply (sum_over_S_ext _ _
      (fun s : S => id_cong2 mult (Hpt s) (id_cong log (Hpt s)))).
Qed.

(* ========== P5 主定理：attention = 变分自由能的唯一最小点 ========== *)
Theorem ufep_attention_minimizes_free_energy_unique :
  forall p : S -> R, normalized p -> positive_dist p ->
  And (le (F_attn (softmax_temp spp T T_pos z)) (F_attn p))
      (Id (F_attn p) (F_attn (softmax_temp spp T T_pos z)) ->
        forall s : S, Id (p s) (softmax_temp spp T T_pos z s)).
Proof.
  intros p Hp Hpos.
  assert (Hnorms : normalized (softmax_temp spp T T_pos z))
    by exact (softmax_temp_normalized spp T T_pos z).
  assert (HFsb : Id (F_attn (softmax_temp spp T T_pos z))
                     (F_attn (boltzmann_dist base T T_pos Zf Zf_pos)))
    by exact (ufep_fep_F_ext (softmax_temp spp T T_pos z)
               (boltzmann_dist base T T_pos Zf Zf_pos)
               Hnorms (boltzmann_normalized base T T_pos Zf Zf_pos ufep_fep_partition_condition)
               (fun s : S => id_sym (ufep_fep_align s))).
  split.
  - exact (le_id_l _ _ _ HFsb
             (min_free_energy_is_boltzmann base T T_pos Zf Zf_pos
                ufep_fep_partition_condition p Hp Hpos)).
  - intros Heq s.
    exact (id_trans
             (free_energy_min_unique base T T_pos Zf Zf_pos
                ufep_fep_partition_condition p Hp Hpos
                (id_trans Heq HFsb) s)
             (ufep_fep_align s)).
Qed.

End FEPAttention.

(* ################ Part 2：行视图引理 ################ *)

Section RowView.
Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Variable spp : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable z2 : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z2 s s').
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).
Variable expf_agree : forall x : R, Id (expf x) (exp_pos_fn x).

(* ========== 行视图：bs_kernel 的每一行 = 单查询 softmax_temp ========== *)
(* 依存前提：expf 与注意力区的 exp_pos_fn 逐点一致（expf 迷你接口的   *)
(* 实例化通道——real_expf_realizable 证明后取 expf := exp_pos_fn 即    *)
(* 满足，一致性前提退化为 id_refl）。                                 *)
Theorem ufep_bs_kernel_row_is_softmax_temp : forall s s' : S,
  Id (bs_kernel enum enum_nonempty temp temp_pos Delta z2 z_lb
        expf expf_pos expf_mono_le sum_eq_list s s')
     (softmax_temp spp temp temp_pos (fun s0 : S => z2 s s0) s').
Proof.
  intros s s'.
  unfold bs_kernel, softmax_temp.
  assert (HZ : Id (Zrow temp temp_pos z2 expf s)
                   (partition_function_temp temp temp_pos (fun s0 : S => z2 s s0))).
  { unfold Zrow, partition_function_temp.
    apply (sum_over_S_ext _ _
      (fun s0 : S => expf_agree (mult (inv_pos temp temp_pos) (z2 s s0)))). }
  apply (id_cong2 mult
    (expf_agree (mult (inv_pos temp temp_pos) (z2 s s')))
    (inv_pos_ext (Zrow temp temp_pos z2 expf s)
                 (partition_function_temp temp temp_pos (fun s0 : S => z2 s s0))
                 (bs_Zrow_pos enum enum_nonempty temp temp_pos Delta z2 z_lb
                    expf expf_pos expf_mono_le sum_eq_list s)
                 (partition_function_temp_pos spp temp temp_pos
                    (fun s0 : S => z2 s s0))
                 HZ)).
Qed.

End RowView.

(* 提取检验：softmax 核与自由能可提取 *)
From Stdlib Require Import Extraction.
Extraction "upfep.ml" softmax_temp partition_function_temp free_energy.

(* ======== G01_CoreMicro 成员件：UpLogMono（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpLogMono.v —— 二轮快赢批·D 残余：Real 层 log 单调 le 版立役      *)
(*                                                                *)
(* 论文 1 KLProjection（审计=KL投影）主定理的 HlogZ 前提            *)
(* （le (log Z_aud) zero）discharge 的最后一块：Z_aud ≤ 1 ⟹         *)
(* log Z_aud ≤ 0 需要「log 单调 le 版」——交接文档蓝图展望 4 点名项。  *)
(* Real 层（cw_log/real_log）上 Or 编码的 le 逐支证明：              *)
(*   lt 支走 real_log_lt_mono（严格单调，根内已证）；                 *)
(*   eq 支走 real_log_wd（等式替换，根内已证）。                      *)
(* 红线：零 公理/承认件；Set 层语句；全 Qed；可提取。             *)
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
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

(* [abl18 洗形] 本件原并入的 UpLogMono 四引理（real_lt_le_bridge /              *)
(* real_eq_le_bridge / real_log_le_mono / real_log_le_zero_of_le_one，证明体与   *)
(* 本件原稿逐字同）已由 S14_B5BatchBlock.v:14708–14741 顶层同件晋升；去重回归    *)
(* 现役——本件 :41/:43/:57/:93 各取用位经 Require 面直取 S14 版，语句面零损失。   *)

(* 提取检验 *)
From Stdlib Require Import Extraction.
Extraction "uplogmono.ml" real_log cw_log.

(* ======== G01_CoreMicro 成员件：UpPPO（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpPPO.v —— 二轮快赢批·E：PPO clip 单侧误差恒等式（E1–E3）          *)
(*                                                                *)
(* 闭合论文 1 §6.2「三件不齐备」的单侧半边：裁剪代理与价值改进之间    *)
(* 的组合定理——                                                    *)
(*   E1 精确分解：IS 目标 == 裁剪代理 + clip 误差（无前提恒等式）；    *)
(*   E2 误差非负：clip_error ≥ 0（无优势符号前提——min_le_l 在乘积    *)
(*      内部，与定理 6.7 同理）；                                   *)
(*   E3 改进条件：裁剪代理非负 ⟹ 价值改进（三件齐备的单侧闭合）。     *)
(* 诚实边界：反向界（V(π)−V(p_old) ≤ std_ppo + C·eps 型）在无界比率   *)
(* 下为假（反例：比率 ρ → ∞ 时误差 A·(ρ−1−ε) 无界），维持不宣称。    *)
(* 红线：零 公理/承认件；Set 层语句；全 Qed。                    *)
(* ============================================================ *)

(* [abl18 洗形] 本件原并入的 UpPPO Section PPOClipDecomp（clip_error /            *)
(* ppo_pointwise_decomp / ppo_is_decomp / clip_error_nonneg / le_of_minus_nonneg / *)
(* ppo_clipped_improvement，E1–E3 单侧三件）已由 S15_TailFEPUp.v:212–339 顶层同件  *)
(* 晋升（同名同签名；与原稿仅两处证明体排版差——ppo_is_decomp 的 apply 二段与       *)
(* le_of_minus_nonneg 的显式实参，语义等价）。去重回归现役：文件尾 Print            *)
(* Assumptions ppo_is_decomp / le_of_minus_nonneg 与下方提取三元                  *)
(* policy_ratio/ppo_clip/clip_error 均经 Require 面直取 S15 现役面，零损失。       *)

(* 提取检验：clip 误差与代理目标可提取 *)
From Stdlib Require Import Extraction.
Extraction "upppo.ml" policy_ratio ppo_clip clip_error.

Print Assumptions uex_fep_partition_condition.
Print Assumptions uex_fep_align.
Print Assumptions free_energy_softmax_eq_neg_T_logZ.
Print Assumptions counter_ex_indicator_sum_two.
Print Assumptions counter_ex_reward_sum_two_c.
Print Assumptions ufep_fep_partition_condition.
Print Assumptions ufep_fep_align.
Print Assumptions ppo_is_decomp.
Print Assumptions le_of_minus_nonneg.
