(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqAlignRestB.v *)
(* *)
(* 目的： 对齐族剩余段 B：求和接口与 Min-P/马尔可夫核域准备。 *)
(* 主件： rls_ext / rls_linear / rls_nonneg 求和定律与 alb_markov_kernel、alb_minp_threshold 域构造。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqPropLiftShim。 *)
(* 备注： 求和接口为显式前提；词表非空见证与温度配分正性为显式构造。 *)
(* ============================================================ *)

(* UpReqAlignRestB.v — 签名迁移批 3 余量 B ：Top-k/Min-P/熵动力学/逐出四区
   抽象层定理的 req 系（setoid 层）req 化。
   源文件：CW_ConstructiveWorld_219（行号 = 219 基座）四区：
     Min-P 区     Section MinPSampling      L30684-31866（Id 系抽象层）
     Top-k 区     Section TopPSampling      L31872-32542（Id 系抽象层）
     熵动力学区   Section EntropyDiffReal   L46821-51392（Real 层，interface-level 余件）
     逐出区       Section RealKVQuantMain   L53932-54965（Real 层，interface-level 余件）
   模板：UpSigMigrate2.v（形态）+ UpReqAlgebra.v（消去引擎/req_minus 直接使用）。
   ----------------------------------------------------------------
   [Part 0 共享机器] rls_ext/rls_linear/rls_nonneg/rls_single_le/rls_pos/rls_le
     （基座 MinPSampling list_sum 簇 L30710-30768/31104 的 req 化——Id 系
     rewrite/id_cong 链逐处换 req_trans + req_plus_compat 真证）
     + req_lt_zero_le_trans（L31065）+ req_le_mult_le_one_r（L30881）。
   [Part 1 Min-P 区] req_pick_max_minp_keep(L30954) req_minp_temp_sum_pos(L30981)
     req_minp_markov_kernel_nonneg/keep_pos/unfold_keep(L31022/31036/31166)
     req_minp_markov_kernel_normalized(L31050 定理) req_minp_temp_sum_le_partition
     (L31112) req_minp_markov_kernel_keep_ge_full(L31127)
     req_minp_markov_kernel_dropped_zero(L31147) req_minp_kernel_ratio(L31182)
     req_minp_dropped_mass_nonneg(L31261) req_temp_factor_max_eq(L31298)
     req_minp_scaled_sum_ge_max(L31313) req_minp_dropped_mass_le_one_minus_max
     (L31451)——14 件。
   [Part 2 Top-k 区] req_topp_temp_sum_pos(L32014) req_topp_markov_kernel_normalized
     (L32084 定理) req_combined_temp_sum_pos(L32182) req_combined_markov_kernel_
     normalized(L32262 定理) req_combined_topk_temp_sum_pos(L32406)
     req_combined_topk_markov_kernel_normalized(L32481 定理)——6 件。
   [Part 3 熵动力学区 interface-level 余件] req_exp_neg_ext_local(req 化引擎自足)
     req_abs_exp_pos(L48538 对位) req_le_eps_Kone(L47809 对位)
     req_scal_sum_ge(L47998 对位) req_M_inv_absorb(L48130 对位)
     req_Omega_total_pos(L51349 对位) + 熵定义组 3 件
     （req_E_B_ent/req_Omega_total_ent/req_entropy_ent）。
   [Part 4 逐出区] req_epos + req_epos_le_mono(正指数幂 = exp_neg 逆的 req 重建)
     req_exp_neg_diff_abs(L53790 对位) req_energy_lipschitz_scaled(L54461 对位)
     req_boltzmann_upper(L54529 对位) req_abs_diff_prod_bound(L54604 对位)
     req_boltzmann_diff_bound(L54636 对位) req_db_breaking_evicted_l(L54055 对位)
     req_db_breaking_kept_final(L54304 对位) req_db_breaking_bound_eps
     (L54841 定理对位)——8 件 + epos 定义组。
   ----------------------------------------------------------------
   诚实边界登记表（逐件注明，红线 3 之「非平凡真实现」核对）：
   1. [桥假设位（T2①，假设位与基座同构）]
      - req_le_dec：基座 DecidableOrder（DO 类 L331 ord_le_dec）的 req 对偶。
        setoid 类无序判定字段——假设位逐位对应，Real 实例侧由 Q 层可判定序
        消解（基座同源）。
      - req_lt_dec：lt_dec_field_tk（L32385 三分支构造子解构）的 req 对偶，
        中支相等判据 Id→req（签名差异：req 世界 R 上相等 = req）。
      - pick_max_in_vocab / topk_pickmax_head：argmin/list 机器 13 件冻结给出
        （规划书 §1.1 边界 2：nat/bool/list Id 机器不在迁移面）——基座 TopP
        自身即以 topk_pickmax_head 为诚实前提 Variable（L32346），同款。
      - boltzmann_diff_bridge（req_boltzmann_diff_bridge，ReqKVQuantWorld 节
        Variable）：real_exp_neg_diff_bound（L53901）的 req 对偶。
        其引擎 real_exp_abs_minus_one_eps 为 Real/Q 层 exp 分析（LogDiffPhase4
        UpSigMigrate2 唯一诚实缺口 req_log_exp_neg 模式）。P1 以桥假设给出，
        其余 B3a/B3b/B3c/结构恒等/组装各件全部真证。
      - transition_nonneg（ReqKVQuantWorld 节 Variable，Or 分解形）：基座
        real_transition_nonneg（real_le zero T，real_le 实为 Or(real_lt,
        real_eq) 形）的逐位 req 对偶——setoid 接口 le 字段抽象不可分解，
        假设位取 Or 分解形逐位同构；需接口 le zero T 处以 lt_le_iff 消解
        （B4），需 |T|==T 处经 req_abs_nonneg_id_or 消解（B2c）。
      - 逐出区求和面：sum_over_S 仅作 req_evicted_partition 的 opaque 载体
        （Variable，基座 real_sum_over_S 同位）；全部 8 件不使用其 ext/linear
        字段，正性由 req_evicted_partition_pos 单独 Variable 给出（基座同位）。
   2. [冻结（双层并行，本件不迁，理由 = 基座自注）]
      - mp_of_nat_pos / markov_kernel_normalized_mp / minp_max_ge_inv_vocab_size /
        pick_best_optimal_mp（L31545-31834）：nat→R 嵌入（mp_of_nat）与 argmin
        list 机器依赖件——UpReqAlgebra (d)1 冻结条款同款（nat 嵌入跨接口不可
        复用）；argmin 机器为 list-Id 域（规划书 §1.1 边界 2）。
      - EntropyDiffReal 的 RealDifferentiable 族（real_differentiable_* /
        real_exp_differentiable / real_entropy_differentiable L51363）：
        RealDifferentiable 为 Real 层 Record（L44447），非接口字段——实例层
        地基（规划书 §1.1 边界 1「对岸」）；其 interface-level 代数/序余件
        （Part 3）已迁，Q 逐点件（real_abs_le_extract/real_le_pointwise_eps 及
        real_abs_prod_le_eps 的 Q 逐点上游）随 判例绕行条款冻结（基座 L47116
        自注：Real 层无 0 ≤ |a|，乘积界走逐点——setoid plain 形不可导出，同
        UpReqAlgebra (d)3 冻结条款）。
   3. [签名变化] minp_dropped_mass 的 minus → req_minus（= plus a (opp b)，
      UpReqAlgebra 登记表 1 同形重建）；count_kernel_heavier 中支 Id → req；
      Part 1+2 合并单节（基座 TopP 以 12 参闭包显式形式使用 MinP 机器，
      req 同构合并避免调用噪音，定义/语句逐件对应）。
      Part 4 续：接口无 plain exp——e^{·} 全部以 req_epos（:= exp_neg∘opp，
      正指数幂 = exp_neg 逆的 req 重建）陈述，boltzmann_upper/abs_diff_prod_
      bound/boltzmann_diff_bound/bound_eps 的 e^{E_max/D}、e^{|u−v|}、e^{Ulips}
      逐位对应（req_Emax_exp/req_eulips 缩写定义 δ 透明）；real_abs_nonneg_req
      （基座 工具 D，le Or 分解）→ req_abs_nonneg_id_or（Or 形前提）；基座
      real_abs_prod_le_eps（Q 逐点乘积界，依判例冻结）的 B3c 乘积段改走
      le_mult_compat/req_le_mult_compat_r 双段单调 + req_le_zero_mult_pos_l
      （le zero (p·x) 接口级导出：le 字段抽象不可分解下的非负积引理）——
      全部真证，无新增冻结件。
      中断修复 5 处（正向修复，零缩水零掉 Qed）：
      a. req_temp_factor_max_eq：mult_assoc 方向反（外层 req_sym 后需再翻回，
         显式 req_sym + mult_assoc）；
      b. req_minp_scaled_sum_ge_max：assert Hk 块尾多一枚 `}`（盘故障重复写）；
      c. topp/combined/combined_topk 三枚 markov_kernel 定义体：基座节闭名
         req_* 名，Hpmax/HK 前提位补齐（对位基座 L32079/32354/32473 显式形）；
      d. combined_keep_dec/combined_topk_temp_sum_pos 内 conj → pair
         （Set 层 And = prod，非 Prop conj）；
      e. 三处 req_topp/combined_temp_sum_pos 调用缺 (Hpmax prefix) 实参。
      续建：Part 3（熵动力学区 Section ReqEntropyWorld：req_exp_neg_ext_local
      + 4 对位件 + 熵定义组 3 件 + req_Omega_total_pos）与 Part 4（逐出区
      Section ReqKVQuantWorld：epos 定义组 + 环/abs 工具 4 件 + P1 桥位 +
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句（req/lt/le/req_minus 均接口 Set 值；Or/And/
   Id(list/nat)/Not 按 UpKVEv 先例）；核心件 Qed、判定件 Defined；
   纯 term-mode（req_trans 链 + compat 桥），零 rewrite 依赖。
   G3 提取检验 upreqalignrestb_probe（验后删）。 *)

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
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Require Import UpReqPropLiftShim.
(* B6W 实例化（，AA13 显式假设①首批）：pls_ 升面适配引理接入。 *)
(* Pool-build cure (seat_abl19, M43 nw10cure per UpReqAlign3.v precedent): the
   interface class in this tree is unparameterized (S07_RealSetoidExpLog.v:8075
   zero-argument Class RealInterfaceEnhancedSetoid + global Instance
   RealEnhancedReal); the argument-bearing generation binders
   the argument-bearing generation binders Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}. are deleted and the carrier R is bound
   to the global Real by the file-top Notation below. Zero Obj.magic, zero Prop
   casts, statement faces preserved verbatim. *)
Notation R := Real.

(* ============================================================ *)
(* Part 0：req list-sum 机器（基座 MinPSampling L30710-30768/    *)
(*   L31104 list_sum 簇的 req 化；rls_* 节闭合后全泛化，         *)
(*   Min-P/Top-k 两区共享）                                      *)
(* ============================================================ *)
Section ReqListSumTool.
Variable A : Set.

Fixpoint rsum (f : A -> R) (l : list A) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (f w) (rsum f rest)
  end.

(* 基座 list_sum_ext L30734：逐点 req ⟹ 和 req *)
Lemma rls_ext : forall f g : A -> R,
  (forall a : A, req (f a) (g a)) -> forall l : list A, req (rsum f l) (rsum g l).
Proof.
  intros f g Hfg l. induction l as [|w rest IH].
  - apply req_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply req_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

(* 基座 list_sum_linear L30710：Σ a·f == a·Σ f（req_trans + distrib 反向） *)
Lemma rls_linear : forall (a : R) (f : A -> R) (l : list A),
  req (rsum (fun x => mult a (f x)) l) (mult a (rsum f l)).
Proof.
  intros a f l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply req_sym. apply mult_zero.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    apply (req_trans (plus (mult a (f w)) (rsum (fun x => mult a (f x)) rest))
                     (plus (mult a (f w)) (mult a (rsum f rest)))
                     (mult a (plus (f w) (rsum f rest)))).
    + apply (req_plus_compat (mult a (f w)) (mult a (f w))
                             (rsum (fun x => mult a (f x)) rest)
                             (mult a (rsum f rest))).
      * apply req_refl.
      * exact IH.
    + apply (req_sym (mult a (plus (f w) (rsum f rest)))
                     (plus (mult a (f w)) (mult a (rsum f rest)))).
      apply distrib.
Qed.

(* 基座 list_sum_nonneg L30742：逐点 ≥ 0 ⟹ Σ ≥ 0 *)
Lemma rls_nonneg : forall f : A -> R,
  (forall a : A, le zero (f a)) -> forall l : list A, le zero (rsum f l).
Proof.
  intros f Hf l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    apply (le_id_l zero (plus zero zero) (plus (f w) (rsum f rest))).
    + apply (req_sym (plus zero zero) zero). apply plus_zero.
    + apply (le_plus_compat zero (f w) zero (rsum f rest)).
      * apply Hf.
      * exact IH.
Qed.

(* 基座 list_sum_single_le_total L30753：单项 ≤ 全和（对 InT 推导归纳） *)
Lemma rls_single_le : forall (f : A -> R) (x : A) (l : list A),
  InT x l -> (forall y : A, le zero (f y)) -> le (f x) (rsum f l).
Proof.
  intros f x l Hin Hnn.
  induction Hin as [l0 | y l0 Hin IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact (req_le_plus_nonneg_r (f x) (rsum f l0) (rls_nonneg f Hnn l0)).
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply (le_trans (f x) (rsum f l0) (plus (f y) (rsum f l0))).
    + exact IH.
    + exact (le_id_r (rsum f l0) (plus (rsum f l0) (f y))
                     (plus (f y) (rsum f l0)) (plus_comm (rsum f l0) (f y))
                     (req_le_plus_nonneg_r (rsum f l0) (f y) (Hnn y))).
Qed.

(* 基座 sum_temp_positive L30769：非空 + 逐点正 ⟹ 和正 *)
Lemma rls_pos : forall f : A -> R,
  (forall a : A, lt zero (f a)) ->
  forall l : list A, Not (Id l nil) -> lt zero (rsum f l).
Proof.
  intros f Hf l. induction l as [|w rest IH].
  - intro Hnil. exact (match Hnil (@id_refl (list A) nil) with end).
  - destruct rest as [|w' rest'].
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc0. apply (lt_id_r zero (f w) (plus (f w) zero)).
      * apply (req_sym (plus (f w) zero) (f w)). apply plus_zero.
      * apply Hf.
    + cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. intro Hc1. apply (lt_id_l zero (plus zero zero)
                                             (plus (f w) (plus (f w') (rsum f rest')))).
      * apply (req_sym (plus zero zero) zero). apply plus_zero.
      * apply lt_plus_compat.
        -- apply Hf.
        -- apply IH. intro Hc. inversion Hc.
Qed.

(* 基座 list_sum_le L31104：逐点 ≤ ⟹ 和 ≤ *)
Lemma rls_le : forall f g : A -> R,
  (forall a : A, le (f a) (g a)) -> forall l : list A, le (rsum f l) (rsum g l).
Proof.
  intros f g Hfg l. induction l as [|w rest IH].
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_refl.
  - cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. apply le_plus_compat.
    + apply Hfg.
    + exact IH.
Qed.

(* req 通用归一化核（基座四归一化定理共用代数骨架的 req 真证；
   基座对 minp/topp/combined/combined_topk 四次重复同款 Id 证明，
   各区 temp_sum 定义即本件 S 项的 δ 展开） *)
Lemma rls_kernel_norm_gen :
  forall (l : list A)
         (P : A -> Set) (kd : forall w : A, Or (P w) (Not (P w)))
         (g : A -> R)
         (HS : lt zero (rsum (fun w => match kd w with
                                       | inl _ => g w
                                       | inr _ => zero
                                       end) l)),
  req (rsum (fun w => match kd w with
                      | inl _ => mult (g w)
                                      (inv_pos (rsum (fun w => match kd w with
                                                               | inl _ => g w
                                                               | inr _ => zero
                                                               end) l)
                                               HS)
                      | inr _ => zero
                      end) l)
      one.
Proof.
  intros l P kd g HS.
  apply (req_trans
    (rsum (fun w => match kd w with
                    | inl _ => mult (g w)
                                    (inv_pos (rsum (fun w => match kd w with
                                                             | inl _ => g w
                                                             | inr _ => zero
                                                             end) l)
                                             HS)
                    | inr _ => zero
                    end) l)
    (mult (inv_pos (rsum (fun w => match kd w with
                                   | inl _ => g w
                                   | inr _ => zero
                                   end) l)
                   HS)
          (rsum (fun w => match kd w with
                          | inl _ => g w
                          | inr _ => zero
                          end) l))
    one).
  - apply (req_trans
      (rsum (fun w => match kd w with
                      | inl _ => mult (g w)
                                      (inv_pos (rsum (fun w => match kd w with
                                                               | inl _ => g w
                                                               | inr _ => zero
                                                               end) l)
                                             HS)
                      | inr _ => zero
                      end) l)
      (rsum (fun w => mult (inv_pos (rsum (fun w => match kd w with
                                                    | inl _ => g w
                                                    | inr _ => zero
                                                    end) l)
                                   HS)
                           (match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end)) l)
      (mult (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS)
            (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l))).
    + apply (rls_ext (fun w => match kd w with
                               | inl _ => mult (g w)
                                               (inv_pos (rsum (fun w => match kd w with
                                                                        | inl _ => g w
                                                                        | inr _ => zero
                                                                        end) l)
                                                        HS)
                               | inr _ => zero
                               end)
                     (fun w => mult (inv_pos (rsum (fun w => match kd w with
                                                             | inl _ => g w
                                                             | inr _ => zero
                                                             end) l)
                                            HS)
                                    (match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end))).
      intro w. destruct (kd w) as [Hp | Hnp].
      * apply mult_comm.
      * apply req_sym. apply mult_zero.
    + apply rls_linear.
  - apply (req_trans
      (mult (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS)
            (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l))
      (mult (rsum (fun w => match kd w with
                            | inl _ => g w
                            | inr _ => zero
                            end) l)
            (inv_pos (rsum (fun w => match kd w with
                                     | inl _ => g w
                                     | inr _ => zero
                                     end) l)
                     HS))
      one).
    + apply mult_comm.
    + apply inv_pos_correct.
Qed.

End ReqListSumTool.


(* ============================================================ *)
(* 通用小件（基座 L31065 lt_zero_le_trans / L30881 le_mult_le_one_r *)
(* 的 req 化；全泛化，采样世界与逐出区共享）                       *)
(* ============================================================ *)
Section ReqOrdTools.

(* 基座 lt_zero_le_trans L31065：0 < a 且 a ≤ b ⟹ 0 < b
   （req 化差异：minus → req_minus；Id rewrite 链 → req_trans + req_minus_plus_cancel） *)
Lemma req_lt_zero_le_trans : forall a b : R,
  lt zero a -> le a b -> lt zero b.
Proof.
  intros a b Ha Hab.
  assert (Hnonneg : le zero (req_minus b a)).
  { apply req_le_minus_nonneg. exact Hab. }
  assert (Hpos : lt zero (plus (req_minus b a) a)).
  { apply req_plus_le_lt_pos.
    - exact Hnonneg.
    - exact Ha. }
  apply (lt_id_r zero (plus (req_minus b a) a) b).
  - apply (req_trans (plus (req_minus b a) a)
                     (plus a (req_minus b a)) b).
    + apply plus_comm.
    + apply req_minus_plus_cancel.
  - exact Hpos.
Qed.

(* 基座 le_mult_le_one_r L30881：0 ≤ a 且 b ≤ 1 ⟹ b·a ≤ a
   （req 化差异：minus → req_minus；Id rewrite 收尾 → le_id_l + req_minus_plus_cancel；
     H3 五段恒等链每段 req_trans 真证） *)
Lemma req_le_mult_le_one_r : forall a b : R,
  le zero a -> le b one -> le (mult b a) a.
Proof.
  intros a b Ha Hb.
  assert (H1 : le zero (req_minus one b)).
  { apply req_le_minus_nonneg. exact Hb. }
  assert (H2 : le zero (mult (req_minus one b) a)).
  { apply (le_id_l zero (mult a zero) (mult (req_minus one b) a)).
    - apply (req_sym (mult a zero) zero). apply mult_zero.
    - apply (le_id_r (mult a zero) (mult a (req_minus one b))
                     (mult (req_minus one b) a)).
      + apply mult_comm.
      + exact (req_le_mult_compat_r a zero (req_minus one b) Ha H1). }
  assert (H3 : req (mult (req_minus one b) a) (req_minus a (mult b a))).
  { apply (req_trans (mult (req_minus one b) a)
                     (mult a (req_minus one b))
                     (req_minus a (mult b a))).
    - apply mult_comm.
    - apply (req_trans (mult a (req_minus one b))
                       (req_minus (mult a one) (mult a b))
                       (req_minus a (mult b a))).
      + apply req_mult_minus_distr_l.
      + unfold req_minus. apply req_plus_compat.
        * apply mult_one.
        * apply req_opp_compat. apply mult_comm. }
  assert (H2' : le zero (req_minus a (mult b a))).
  { exact (le_id_r zero (mult (req_minus one b) a)
                   (req_minus a (mult b a)) H3 H2). }
  assert (H4 : le (plus (mult b a) zero)
                  (plus (mult b a) (req_minus a (mult b a)))).
  { apply (le_plus_compat (mult b a) (mult b a) zero (req_minus a (mult b a))).
    - apply le_refl.
    - exact H2'. }
  exact (le_id_r (mult b a) (plus (mult b a) (req_minus a (mult b a))) a
                 (req_minus_plus_cancel (mult b a) a)
                 (le_id_l (mult b a) (plus (mult b a) zero)
                          (plus (mult b a) (req_minus a (mult b a)))
                          (req_sym (plus (mult b a) zero) (mult b a)
                                   (plus_zero (mult b a)))
                          H4)).
Qed.

End ReqOrdTools.

(* ============================================================ *)
(* Part 1+2：采样世界（Min-P 区 L30684-31866 + Top-k 区          *)
(*   L31872-32542）。基座 TopP 以「闭包显式参数形式」使用 MinP    *)
(*   机器（L31914 同款 12 参显式调用）；req 合并单节同构重述，  *)
(*   逐件定义/语句仍与基座一一对应。                              *)
(*   top_p_keep（sort_kernel 成员形态，L31962）不迁：其排序/成员  *)
(*   机器为 list-Id 域（规划书 §1.1 边界 2），基座定理全部使用     *)
(*   le 形态 topp_keep（L31990）。                                *)
(* ============================================================ *)
Section ReqSamplingWorld.

(* ---- 接口假设（MinPSampling L30693-30701 同构） ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W 实例化位（AA13 #10，）：老否定形前提经 pls_ 适配引理升 sigT 见证形—— *)
(* 深实例化使用位：pls_vocab_ne_lift 原地升形，下游可直取走 sigT 通路。旧语句保留。 *)
Definition alb_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- Min-P 参数（L30870-30872 同位） ---- *)
Variable min_p : R.
Variable min_p_pos : lt zero min_p.
Variable min_p_lt_one : lt min_p one.

(* ---- 桥假设位 1：DecidableOrder 的 req 对偶（ord_le_dec L331/332 同位；
     setoid 类无序判定字段，T2① 假设位逐位对应） ---- *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- 桥假设位 2：三分判定（lt_dec_field_tk L32385 的 req 对偶；
     中支相等判据 Id→req——req 世界 R 上相等 = req） ---- *)
Hypothesis req_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* ---- 桥假设位 3：list 机器冻结给出（argmin 13 件不迁；仅给出顶层
     事实 pick_max ∈ vocab——UpKVEv 先例同款） ---- *)
Variable pick_max_token : list Token -> Token.
Hypothesis pick_max_in_vocab : forall prefix : list Token,
  InT (pick_max_token prefix) vocab.

(* ---- 2. 基础设施（L30703-30715 同构；list_sum → rsum） ---- *)
Definition alb_temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos)
                (total_loss (prefix ++ [w]))).

Definition alb_partition_temp (prefix : list Token) : R :=
  rsum Token (alb_temp_factor prefix) vocab.

(* 基座 req_partition_temp_pos L30768 *)
Lemma req_partition_temp_pos : forall prefix : list Token,
  lt zero (alb_partition_temp prefix).
Proof.
  intro prefix. unfold alb_partition_temp.
  apply (rls_pos Token (alb_temp_factor prefix)).
  - intro w. unfold alb_temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

Definition alb_markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (alb_temp_factor prefix w)
       (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).

(* 基座 markov_pos L30861 *)
Lemma req_markov_pos : forall (prefix : list Token) (w : Token),
  lt zero (alb_markov_kernel prefix w).
Proof.
  intros prefix w. unfold alb_markov_kernel. apply mult_positive.
  - unfold alb_temp_factor. apply exp_neg_pos.
  - apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
Qed.

(* 基座 markov_kernel_unfold L31156（定义性） *)
Lemma req_markov_kernel_unfold : forall (prefix : list Token) (w : Token),
  req (alb_markov_kernel prefix w)
      (mult (alb_temp_factor prefix w)
            (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))).
Proof.
  intros prefix w. apply req_refl.
Qed.

(* ---- 4. Min-P 阈值与判定（L30919-30945 同构） ---- *)
Definition alb_max_markov_prob (prefix : list Token) : R :=
  alb_markov_kernel prefix (pick_max_token prefix).

Definition alb_minp_threshold (prefix : list Token) : R :=
  mult min_p (alb_max_markov_prob prefix).

Definition alb_minp_keep (prefix : list Token) (w : Token) : Set :=
  le (alb_minp_threshold prefix) (alb_markov_kernel prefix w).

Definition alb_minp_keep_dec (prefix : list Token) (w : Token) :
  Or (alb_minp_keep prefix w) (Not (alb_minp_keep prefix w)) :=
  req_le_dec (alb_minp_threshold prefix) (alb_markov_kernel prefix w).

Definition alb_minp_temp_sum (prefix : list Token) : R :=
  rsum Token (fun w => match alb_minp_keep_dec prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* 基座 pick_max_token_minp_keep L30954（使用 req_le_mult_le_one_r） *)
Lemma req_pick_max_minp_keep : forall prefix : list Token,
  alb_minp_keep prefix (pick_max_token prefix).
Proof.
  intro prefix. unfold alb_minp_keep.
  apply (req_le_mult_le_one_r (alb_markov_kernel prefix (pick_max_token prefix))
                              min_p).
  - apply (lt_le_iff zero (alb_markov_kernel prefix (pick_max_token prefix))).
    left. apply req_markov_pos.
  - apply (lt_le_iff min_p one). left. exact min_p_lt_one.
Qed.

(* pick_max 的 tf 单项 ≤ alb_minp_temp_sum（temp_factor_max_le_sum L31328 核心肢；
   req_minp_temp_sum_pos 与 scaled_sum_ge_max 共用） *)
Lemma req_pick_max_tf_le_minp_sum : forall prefix : list Token,
  le (alb_temp_factor prefix (pick_max_token prefix)) (alb_minp_temp_sum prefix).
Proof.
  intro prefix. unfold alb_minp_temp_sum.
  assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                    (match alb_minp_keep_dec prefix (pick_max_token prefix) with
                     | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                     | inr _ => zero
                     end)).
  { destruct (alb_minp_keep_dec prefix (pick_max_token prefix)) as [Hk | Hd].
    - apply req_refl.
    - destruct (Hd (req_pick_max_minp_keep prefix)). }
  apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                 (match alb_minp_keep_dec prefix (pick_max_token prefix) with
                  | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (rsum Token
                        (fun w => match alb_minp_keep_dec prefix w with
                                  | inl _ => alb_temp_factor prefix w
                                  | inr _ => zero
                                  end) vocab)).
  - exact Heq.
  - apply (rls_single_le Token
           (fun w => match alb_minp_keep_dec prefix w with
                     | inl _ => alb_temp_factor prefix w
                     | inr _ => zero
                     end)
           (pick_max_token prefix) vocab).
    + apply pick_max_in_vocab.
    + intro w. destruct (alb_minp_keep_dec prefix w) as [Hk2 | Hd2].
      * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
        unfold alb_temp_factor. apply exp_neg_pos.
      * apply le_refl.
Qed.

(* 基座 req_minp_temp_sum_pos L30981 *)
Lemma req_minp_temp_sum_pos : forall prefix : list Token,
  lt zero (alb_minp_temp_sum prefix).
Proof.
  intro prefix.
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_minp_temp_sum prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact (req_pick_max_tf_le_minp_sum prefix).
Qed.

(* ---- Min-P 截断核（L31009-31049 同构） ---- *)
Definition alb_minp_markov_kernel (prefix : list Token) (w : Token) : R :=
  match alb_minp_keep_dec prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
  | inr _ => zero
  end.

(* 基座 minp_markov_kernel_nonneg L31022（Or 分解形态逐位对应） *)
Lemma req_minp_markov_kernel_nonneg : forall (prefix : list Token) (w : Token),
  Or (req (alb_minp_markov_kernel prefix w) zero)
     (lt zero (alb_minp_markov_kernel prefix w)).
Proof.
  intros prefix w. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hkeep | Hdrop].
  - right. apply mult_positive.
    + unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)).
  - left. apply req_refl.
Qed.

(* 基座 minp_markov_kernel_keep_pos L31036（条件式正性） *)
Lemma req_minp_markov_kernel_keep_pos : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w -> lt zero (alb_minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply mult_positive.
    + unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)).
  - destruct (Hdrop Hkeep).
Qed.

(* 基座 minp_markov_kernel_unfold_keep L31166 *)
Lemma req_minp_markov_kernel_unfold_keep : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  req (alb_minp_markov_kernel prefix w)
      (mult (alb_temp_factor prefix w)
            (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hdrop].
  - apply req_refl.
  - destruct (Hdrop Hkeep).
Qed.

(* ===== 基座 minp_markov_kernel_normalized L31050（定理 req 化主定理） =====
   Id 系 rewrite Hext/Hlin/Hdef 三步替换；req 系 = rls_kernel_norm_gen
   （代数骨架一次真证）+ 本语句级实例（conversion 逐位对应：
   alb_minp_markov_kernel/alb_minp_temp_sum 定义 δ 展开）。 *)
Theorem req_minp_markov_kernel_normalized : forall prefix : list Token,
  req (rsum Token (fun w => alb_minp_markov_kernel prefix w) vocab) one.
Proof.
  intro prefix.
  exact (rls_kernel_norm_gen Token vocab
           (fun w : Token => le (alb_minp_threshold prefix) (alb_markov_kernel prefix w))
           (fun w : Token => alb_minp_keep_dec prefix w) (alb_temp_factor prefix)
           (req_minp_temp_sum_pos prefix)).
Qed.

(* 基座 minp_temp_sum_le_partition L31112（rls_le 收尾） *)
Lemma req_minp_temp_sum_le_partition : forall prefix : list Token,
  le (alb_minp_temp_sum prefix) (alb_partition_temp prefix).
Proof.
  intro prefix. unfold alb_minp_temp_sum, alb_partition_temp.
  apply (rls_le Token
           (fun w => match alb_minp_keep_dec prefix w with
                     | inl _ => alb_temp_factor prefix w
                     | inr _ => zero
                     end)
           (alb_temp_factor prefix)).
  intro w. destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - apply le_refl.
  - apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
    unfold alb_temp_factor. apply exp_neg_pos.
Qed.

(* ===== 基座 minp_markov_kernel_keep_ge_full L31127：保留者核 ≥ 完整核 ===== *)
Lemma req_minp_markov_kernel_keep_ge_full : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  le (alb_markov_kernel prefix w) (alb_minp_markov_kernel prefix w).
Proof.
  intros prefix w Hkeep. unfold alb_minp_markov_kernel, alb_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - apply (req_le_mult_compat_r (alb_temp_factor prefix w)
                                (inv_pos (alb_partition_temp prefix)
                                         (req_partition_temp_pos prefix))
                                (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))).
    + apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
      unfold alb_temp_factor. apply exp_neg_pos.
    + apply (inv_pos_le_compat (alb_minp_temp_sum prefix) (alb_partition_temp prefix)
                               (req_minp_temp_sum_pos prefix)
                               (req_partition_temp_pos prefix)).
      exact (req_minp_temp_sum_le_partition prefix).
  - destruct (Hd Hkeep).
Qed.

(* ===== 基座 minp_markov_kernel_dropped_zero L31147（req 形态） ===== *)
Lemma req_minp_markov_kernel_dropped_zero : forall (prefix : list Token) (w : Token),
  Not (alb_minp_keep prefix w) -> req (alb_minp_markov_kernel prefix w) zero.
Proof.
  intros prefix w Hdrop. unfold alb_minp_markov_kernel.
  destruct (alb_minp_keep_dec prefix w) as [Hk | Hd].
  - destruct (Hdrop Hk).
  - apply req_refl.
Qed.

(* ===== 基座 minp_kernel_ratio L31182：放大因子显式形式 =====
   Id 系 id_cong 五段链；req 系以内层恒等 Hinner + req_mult_compat 显式给参
   （req 化非平凡件：inv 链 5 段每段独立真证）。 *)
Lemma req_minp_kernel_ratio : forall (prefix : list Token) (w : Token),
  alb_minp_keep prefix w ->
  req (alb_minp_markov_kernel prefix w)
      (mult (alb_markov_kernel prefix w)
            (mult (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
                  (alb_partition_temp prefix))).
Proof.
  intros prefix w Hkeep.
  assert (Hinner : req (mult (inv_pos (alb_partition_temp prefix)
                                       (req_partition_temp_pos prefix))
                             (mult (inv_pos (alb_minp_temp_sum prefix)
                                            (req_minp_temp_sum_pos prefix))
                                   (alb_partition_temp prefix)))
                       (inv_pos (alb_minp_temp_sum prefix)
                                (req_minp_temp_sum_pos prefix))).
  { apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
                  (alb_partition_temp prefix)))
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (alb_partition_temp prefix)
                  (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))))
      (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
    - apply req_mult_compat.
      + apply req_refl.
      + apply mult_comm.
    - apply (req_trans
        (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
              (mult (alb_partition_temp prefix)
                    (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))))
        (mult (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix))
              (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
        (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
      + apply mult_assoc.
      + apply (req_trans
          (mult (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                      (alb_partition_temp prefix))
                (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
          (mult (mult (alb_partition_temp prefix)
                      (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix)))
                (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
          (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
        * apply req_mult_compat.
          -- apply mult_comm.
          -- apply req_refl.
        * apply (req_trans
            (mult (mult (alb_partition_temp prefix)
                        (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix)))
                  (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix)))
            (mult one (inv_pos (alb_minp_temp_sum prefix)
                               (req_minp_temp_sum_pos prefix)))
            (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))).
          -- apply req_mult_compat.
             ++ apply inv_pos_correct.
             ++ apply req_refl.
          -- apply (req_trans
               (mult one (inv_pos (alb_minp_temp_sum prefix)
                                  (req_minp_temp_sum_pos prefix)))
               (mult (inv_pos (alb_minp_temp_sum prefix)
                              (req_minp_temp_sum_pos prefix)) one)
               (inv_pos (alb_minp_temp_sum prefix) (req_minp_temp_sum_pos prefix))
               (mult_comm one
                          (inv_pos (alb_minp_temp_sum prefix)
                                   (req_minp_temp_sum_pos prefix)))
               (mult_one (inv_pos (alb_minp_temp_sum prefix)
                                  (req_minp_temp_sum_pos prefix)))). }
  exact (req_trans
           (alb_minp_markov_kernel prefix w)
           (mult (alb_temp_factor prefix w)
                 (inv_pos (alb_minp_temp_sum prefix)
                          (req_minp_temp_sum_pos prefix)))
           (mult (alb_markov_kernel prefix w)
                 (mult (inv_pos (alb_minp_temp_sum prefix)
                                (req_minp_temp_sum_pos prefix))
                       (alb_partition_temp prefix)))
           (req_minp_markov_kernel_unfold_keep prefix w Hkeep)
           (req_trans
              (mult (alb_temp_factor prefix w)
                    (inv_pos (alb_minp_temp_sum prefix)
                             (req_minp_temp_sum_pos prefix)))
              (mult (alb_temp_factor prefix w)
                    (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix))))
              (mult (alb_markov_kernel prefix w)
                    (mult (inv_pos (alb_minp_temp_sum prefix)
                                   (req_minp_temp_sum_pos prefix))
                          (alb_partition_temp prefix)))
              (req_mult_compat
                 (alb_temp_factor prefix w) (alb_temp_factor prefix w)
                 (inv_pos (alb_minp_temp_sum prefix)
                          (req_minp_temp_sum_pos prefix))
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (mult (inv_pos (alb_minp_temp_sum prefix)
                                      (req_minp_temp_sum_pos prefix))
                             (alb_partition_temp prefix)))
                 (req_refl (alb_temp_factor prefix w))
                 (req_sym
                    (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix)))
                    (inv_pos (alb_minp_temp_sum prefix)
                             (req_minp_temp_sum_pos prefix))
                    Hinner))
              (mult_assoc (alb_temp_factor prefix w)
                          (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (inv_pos (alb_minp_temp_sum prefix)
                                         (req_minp_temp_sum_pos prefix))
                                (alb_partition_temp prefix))))).
Qed.

(* ---- 5. 截断质量（L31257-31451；minus → req_minus 签名变化，登记表 3） ---- *)
Definition alb_minp_dropped_mass (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                  (alb_minp_temp_sum prefix)).

(* 基座 minp_dropped_mass_nonneg L31261（le_minus_nonneg → req_le_minus_nonneg） *)
Lemma req_minp_dropped_mass_nonneg : forall prefix : list Token,
  le zero (alb_minp_dropped_mass prefix).
Proof.
  intro prefix. unfold alb_minp_dropped_mass.
  apply req_le_minus_nonneg.
  apply (le_id_r
    (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
          (alb_minp_temp_sum prefix))
    (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
          (alb_partition_temp prefix))
    one).
  - apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (alb_partition_temp prefix))
      (mult (alb_partition_temp prefix)
            (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)))
      one).
    + apply mult_comm.
    + apply inv_pos_correct.
  - apply (req_le_mult_compat_r
             (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
             (alb_minp_temp_sum prefix) (alb_partition_temp prefix)).
    + apply (lt_le_iff zero
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))).
      left. apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
    + exact (req_minp_temp_sum_le_partition prefix).
Qed.

(* 基座 temp_factor_max_eq L31298：tf(pick_max) == max_prob·partition
   （max_prob 经 alb_markov_kernel 定义 δ 展开 == tf·inv_p——req 化差异：
   该 δ 步为 conversion req_refl，assoc 步真证） *)
Lemma req_temp_factor_max_eq : forall prefix : list Token,
  req (alb_temp_factor prefix (pick_max_token prefix))
      (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)).
Proof.
  intro prefix.
  apply (req_trans
    (alb_temp_factor prefix (pick_max_token prefix))
    (mult (alb_temp_factor prefix (pick_max_token prefix))
          (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                (alb_partition_temp prefix)))
    (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))).
  - apply (req_trans
      (alb_temp_factor prefix (pick_max_token prefix))
      (mult (alb_temp_factor prefix (pick_max_token prefix)) one)
      (mult (alb_temp_factor prefix (pick_max_token prefix))
            (mult (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix))
                  (alb_partition_temp prefix)))).
    + apply (req_sym (mult (alb_temp_factor prefix (pick_max_token prefix)) one)
                     (alb_temp_factor prefix (pick_max_token prefix))).
      apply mult_one.
    + apply req_mult_compat.
      * apply req_refl.
      * apply (req_trans
          one
          (mult (alb_partition_temp prefix)
                (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)))
          (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                (alb_partition_temp prefix))).
        -- apply (req_sym
                    (mult (alb_partition_temp prefix)
                          (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix)))
                    one).
           apply inv_pos_correct.
        -- apply mult_comm.
  - apply (req_trans
      (mult (alb_temp_factor prefix (pick_max_token prefix))
            (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
                  (alb_partition_temp prefix)))
      (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                  (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix)))
            (alb_partition_temp prefix))
      (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))).
    + apply (req_sym
        (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))
              (mult (alb_temp_factor prefix (pick_max_token prefix))
              (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix)))).
      (* 盘故障中断修复（ ）：外层 req_sym 已翻转目标，
         assoc 步实为 mult_assoc 之对称——req_sym 显式翻回（正向修复）。 *)
      apply (req_sym
        (mult (alb_temp_factor prefix (pick_max_token prefix))
              (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_partition_temp prefix)))
        (mult (mult (alb_temp_factor prefix (pick_max_token prefix))
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))).
      apply mult_assoc.
    + apply req_refl.
Qed.

(* 基座 minp_scaled_sum_ge_max L31313：max_prob ≤ inv_p·minp_sum *)
Lemma req_minp_scaled_sum_ge_max : forall prefix : list Token,
  le (alb_max_markov_prob prefix)
     (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
           (alb_minp_temp_sum prefix)).
Proof.
  intro prefix.
  assert (Hid : req (mult (inv_pos (alb_partition_temp prefix)
                                   (req_partition_temp_pos prefix))
                          (mult (alb_max_markov_prob prefix)
                                (alb_partition_temp prefix)))
                    (alb_max_markov_prob prefix)).
  { apply (req_trans
      (mult (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
            (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
      (mult (mult (inv_pos (alb_partition_temp prefix)
                           (req_partition_temp_pos prefix))
                  (alb_max_markov_prob prefix))
            (alb_partition_temp prefix))
      (alb_max_markov_prob prefix)).
    - apply mult_assoc.
    - apply (req_trans
        (mult (mult (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix))
                    (alb_max_markov_prob prefix))
              (alb_partition_temp prefix))
        (mult (mult (alb_max_markov_prob prefix)
                    (inv_pos (alb_partition_temp prefix)
                             (req_partition_temp_pos prefix)))
              (alb_partition_temp prefix))
        (alb_max_markov_prob prefix)).
      + apply req_mult_compat.
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans
          (mult (mult (alb_max_markov_prob prefix)
                      (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix)))
                (alb_partition_temp prefix))
          (mult (alb_max_markov_prob prefix)
                (mult (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix))
                      (alb_partition_temp prefix)))
          (alb_max_markov_prob prefix)).
        * apply (req_sym
            (mult (alb_max_markov_prob prefix)
                  (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                        (alb_partition_temp prefix)))
            (mult (mult (alb_max_markov_prob prefix)
                        (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix)))
                  (alb_partition_temp prefix))).
          apply mult_assoc.
        * apply (req_trans
            (mult (alb_max_markov_prob prefix)
                  (mult (inv_pos (alb_partition_temp prefix)
                                 (req_partition_temp_pos prefix))
                        (alb_partition_temp prefix)))
            (mult (alb_max_markov_prob prefix) one)
            (alb_max_markov_prob prefix)).
          -- apply req_mult_compat.
             ++ apply req_refl.
             ++ apply (req_trans
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (alb_partition_temp prefix))
                 (mult (alb_partition_temp prefix)
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix)))
                 one).
                ** apply mult_comm.
                ** apply inv_pos_correct.
          -- apply mult_one. }
  assert (H1 : le (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
                  (alb_minp_temp_sum prefix)).
  { exact (le_id_l (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
                   (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_minp_temp_sum prefix)
                   (req_sym (alb_temp_factor prefix (pick_max_token prefix))
                            (mult (alb_max_markov_prob prefix)
                                  (alb_partition_temp prefix))
                            (req_temp_factor_max_eq prefix))
                   (req_pick_max_tf_le_minp_sum prefix)). }
  apply (le_id_l (alb_max_markov_prob prefix)
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
                 (mult (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))
                       (alb_minp_temp_sum prefix))).
  - apply (req_sym (mult (inv_pos (alb_partition_temp prefix)
                                  (req_partition_temp_pos prefix))
                         (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix)))
                   (alb_max_markov_prob prefix)).
    exact Hid.
  - apply (req_le_mult_compat_r
             (inv_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix))
             (mult (alb_max_markov_prob prefix) (alb_partition_temp prefix))
             (alb_minp_temp_sum prefix)).
    + apply (lt_le_iff zero
                       (inv_pos (alb_partition_temp prefix)
                                (req_partition_temp_pos prefix))).
      left. apply (inv_pos_pos (alb_partition_temp prefix) (req_partition_temp_pos prefix)).
    + exact H1.
Qed.

(* 基座 minp_dropped_mass_le_one_minus_max L31451（opp 反向 + 平移） *)
Lemma req_minp_dropped_mass_le_one_minus_max : forall prefix : list Token,
  le (alb_minp_dropped_mass prefix) (req_minus one (alb_max_markov_prob prefix)).
Proof.
  intro prefix. unfold alb_minp_dropped_mass.
  apply (le_plus_compat one one
           (opp (mult (inv_pos (alb_partition_temp prefix)
                               (req_partition_temp_pos prefix))
                      (alb_minp_temp_sum prefix)))
           (opp (alb_max_markov_prob prefix))).
  - apply le_refl.
  - apply opp_le_compat.
    exact (req_minp_scaled_sum_ge_max prefix).
Qed.

(* ============================================================ *)
(* Part 2：Top-k 区（基座 TopPSampling L31872-32542 对位）        *)
(* ============================================================ *)

(* 基座 topp_keep L31990（le 形态） *)
Definition alb_topp_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  le p (alb_markov_kernel prefix w).

Definition alb_topp_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (alb_topp_keep p prefix w) (Not (alb_topp_keep p prefix w)) :=
  req_le_dec p (alb_markov_kernel prefix w).

Definition alb_topp_temp_sum (p : R) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_topp_keep_dec p prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* 基座 topp_temp_sum_pos L32014：pick_max 保留性由前提 le p max 给出
   （alb_topp_keep p prefix pick_max ≡ le p (alb_max_markov_prob prefix) conversion） *)
Lemma req_topp_temp_sum_pos : forall (p : R) (prefix : list Token),
  le p (alb_max_markov_prob prefix) -> lt zero (alb_topp_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_topp_temp_sum p prefix)).
  { unfold alb_topp_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_topp_keep_dec p prefix (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_topp_keep_dec p prefix (pick_max_token prefix)) as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd Hp). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_topp_keep_dec p prefix (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_topp_keep_dec p prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_topp_keep_dec p prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_topp_keep_dec p prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_topp_temp_sum p prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* 基座 topp_markov_kernel L32085（Hpmax 前提位逐位对应） *)
Definition alb_topp_markov_kernel (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token) (w : Token) : R :=
  match alb_topp_keep_dec p prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_topp_temp_sum p prefix)
                    (req_topp_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== 基座 topp_markov_kernel_normalized L32084（定理 req 化主定理） ===== *)
Theorem req_topp_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token),
  req (rsum Token (fun w => alb_topp_markov_kernel p Hpmax prefix w) vocab) one.
Proof.
  intros p Hpmax prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_topp_keep p prefix)
           (fun w => alb_topp_keep_dec p prefix w) (alb_temp_factor prefix)
           (req_topp_temp_sum_pos p prefix (Hpmax prefix))).
Qed.

(* ---- 联合保留（Min-P ∧ Top-p，基座 L32152-32262） ---- *)
Definition alb_combined_keep (p : R) (prefix : list Token) (w : Token) : Set :=
  And (alb_minp_keep prefix w) (alb_topp_keep p prefix w).

Definition alb_combined_keep_dec (p : R) (prefix : list Token) (w : Token) :
  Or (alb_combined_keep p prefix w) (Not (alb_combined_keep p prefix w)).
Proof.
  unfold alb_combined_keep.
  destruct (alb_minp_keep_dec prefix w) as [Hmin | Hnotmin].
  - destruct (alb_topp_keep_dec p prefix w) as [Htp | Hntp].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntp Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

Definition alb_combined_temp_sum (p : R) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_combined_keep_dec p prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* 基座 combined_temp_sum_pos L32182：pick_max 双保留（minp 内证 + topp 前提） *)
Lemma req_combined_temp_sum_pos : forall (p : R) (prefix : list Token),
  le p (alb_max_markov_prob prefix) -> lt zero (alb_combined_temp_sum p prefix).
Proof.
  intros p prefix Hp.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_combined_temp_sum p prefix)).
  { unfold alb_combined_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_combined_keep_dec p prefix (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_combined_keep_dec p prefix (pick_max_token prefix)) as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd (pair (req_pick_max_minp_keep prefix) Hp)). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_combined_keep_dec p prefix (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_combined_keep_dec p prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_combined_keep_dec p prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_combined_keep_dec p prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_combined_temp_sum p prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* 基座 combined_markov_kernel L32354（Hpmax 显式前提位同基座） *)
Definition alb_combined_markov_kernel (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token) (w : Token) : R :=
  match alb_combined_keep_dec p prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_combined_temp_sum p prefix)
                    (req_combined_temp_sum_pos p prefix (Hpmax prefix)))
  | inr _ => zero
  end.

(* ===== 基座 combined_markov_kernel_normalized L32262（定理 req 化主定理） ===== *)
Theorem req_combined_markov_kernel_normalized : forall (p : R)
  (Hpmax : forall prefix : list Token, le p (alb_max_markov_prob prefix))
  (prefix : list Token),
  req (rsum Token (fun w => alb_combined_markov_kernel p Hpmax prefix w) vocab) one.
Proof.
  intros p Hpmax prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_combined_keep p prefix)
           (fun w => alb_combined_keep_dec p prefix w) (alb_temp_factor prefix)
           (req_combined_temp_sum_pos p prefix (Hpmax prefix))).
Qed.

(* ---- Top-k 计数保留（基座 L32366-32396 同构） ---- *)
(* nat/bool/list 侧 Id 判定原样保留（规划书 §1.1 边界 2） *)
Definition alb_NatLt_tk (n m : nat) : Set := Id (Nat.ltb n m) true.

Lemma urb_id_false_true : forall (H : Id false true), Empty_set.
Proof. intro H. inversion H. Qed.

Fixpoint alb_count_kernel_heavier (prefix : list Token) (w : Token)
         (l : list Token) : nat :=
  match l with
  | nil => Datatypes.O
  | a :: rest =>
      match req_lt_dec (alb_markov_kernel prefix w) (alb_markov_kernel prefix a) with
      | inl _ => Datatypes.S (alb_count_kernel_heavier prefix w rest)
      | inr _ => alb_count_kernel_heavier prefix w rest
      end
  end.

Definition alb_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  alb_NatLt_tk (alb_count_kernel_heavier prefix w vocab) K.

Definition alb_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (alb_topk_keep K prefix w) (Not (alb_topk_keep K prefix w)) :=
  match Nat.ltb (alb_count_kernel_heavier prefix w vocab) K as b
        return Or (Id b true) (Not (Id b true)) with
  | true => inl id_refl
  | false => inr (fun H => urb_id_false_true H)
  end.

(* 诚实前提（基座 L32346 同位 Variable：排序正确性弱化 判例组绕行） *)
Variable topk_pickmax_head : forall (K : nat) (prefix : list Token),
  (1 <= K)%nat -> alb_topk_keep K prefix (pick_max_token prefix).

(* ---- 联合保留（Min-P ∧ Top-k，基座 L32403-32481） ---- *)
Definition alb_combined_topk_keep (K : nat) (prefix : list Token) (w : Token) : Set :=
  And (alb_minp_keep prefix w) (alb_topk_keep K prefix w).

Definition alb_combined_topk_keep_dec (K : nat) (prefix : list Token) (w : Token) :
  Or (alb_combined_topk_keep K prefix w) (Not (alb_combined_topk_keep K prefix w)).
Proof.
  unfold alb_combined_topk_keep.
  destruct (alb_minp_keep_dec prefix w) as [Hmin | Hnotmin].
  - destruct (alb_topk_keep_dec K prefix w) as [Htop | Hntop].
    + left. split; assumption.
    + right. intros [Hm Ht]. exact (Hntop Ht).
  - right. intros [Hm Ht]. exact (Hnotmin Hm).
Defined.

Definition alb_combined_topk_temp_sum (K : nat) (prefix : list Token) : R :=
  rsum Token (fun w => match alb_combined_topk_keep_dec K prefix w with
                       | inl _ => alb_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

(* 基座 combined_topk_temp_sum_pos L32406：K ≥ 1 + 诚实前提 topk_pickmax_head *)
Lemma req_combined_topk_temp_sum_pos : forall (K : nat) (prefix : list Token),
  (1 <= K)%nat -> lt zero (alb_combined_topk_temp_sum K prefix).
Proof.
  intros K prefix HK.
  assert (Hle : le (alb_temp_factor prefix (pick_max_token prefix))
                   (alb_combined_topk_temp_sum K prefix)).
  { unfold alb_combined_topk_temp_sum.
    assert (Heq : req (alb_temp_factor prefix (pick_max_token prefix))
                      (match alb_combined_topk_keep_dec K prefix
                                 (pick_max_token prefix) with
                       | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                       | inr _ => zero
                       end)).
    { destruct (alb_combined_topk_keep_dec K prefix (pick_max_token prefix))
              as [Hk | Hd].
      - apply req_refl.
      - destruct (Hd (pair (req_pick_max_minp_keep prefix)
                           (topk_pickmax_head K prefix HK))). }
    apply (le_id_l (alb_temp_factor prefix (pick_max_token prefix))
                   (match alb_combined_topk_keep_dec K prefix
                                 (pick_max_token prefix) with
                    | inl _ => alb_temp_factor prefix (pick_max_token prefix)
                    | inr _ => zero
                    end)
                   (rsum Token
                          (fun w => match alb_combined_topk_keep_dec K prefix w with
                                    | inl _ => alb_temp_factor prefix w
                                    | inr _ => zero
                                    end) vocab)).
    - exact Heq.
    - apply (rls_single_le Token
               (fun w => match alb_combined_topk_keep_dec K prefix w with
                         | inl _ => alb_temp_factor prefix w
                         | inr _ => zero
                         end)
               (pick_max_token prefix) vocab).
      + apply pick_max_in_vocab.
      + intro w. destruct (alb_combined_topk_keep_dec K prefix w) as [Hk2 | Hd2].
        * apply (lt_le_iff zero (alb_temp_factor prefix w)). left.
          unfold alb_temp_factor. apply exp_neg_pos.
        * apply le_refl. }
  apply (req_lt_zero_le_trans (alb_temp_factor prefix (pick_max_token prefix))
                              (alb_combined_topk_temp_sum K prefix)).
  - unfold alb_temp_factor. apply exp_neg_pos.
  - exact Hle.
Qed.

(* 基座 combined_topk_markov_kernel L32473（HK 显式前提位同基座） *)
Definition alb_combined_topk_markov_kernel (K : nat)
  (HK : forall prefix : list Token, (1 <= K)%nat)
  (prefix : list Token) (w : Token) : R :=
  match alb_combined_topk_keep_dec K prefix w with
  | inl _ =>
      mult (alb_temp_factor prefix w)
           (inv_pos (alb_combined_topk_temp_sum K prefix)
                    (req_combined_topk_temp_sum_pos K prefix (HK prefix)))
  | inr _ => zero
  end.

(* ===== 基座 combined_topk_markov_kernel_normalized L32481（定理 req 化主定理） ===== *)
Theorem req_combined_topk_markov_kernel_normalized :
  forall (K : nat) (HK : forall prefix : list Token, (1 <= K)%nat)
         (prefix : list Token),
  req (rsum Token (fun w => alb_combined_topk_markov_kernel K HK prefix w) vocab) one.
Proof.
  intros K HK prefix.
  exact (rls_kernel_norm_gen Token vocab (alb_combined_topk_keep K prefix)
           (fun w => alb_combined_topk_keep_dec K prefix w) (alb_temp_factor prefix)
           (req_combined_topk_temp_sum_pos K prefix (HK prefix))).
Qed.

End ReqSamplingWorld.

(* ============================================================ *)
(* Part 3：熵动力学区 interface-level 余件（基座 EntropyDiffReal  *)
(*   L46821-51392 的 req 对位；RealDifferentiable 族随登记表 2 冻结， *)
(*   本区只迁代数/序余件与熵定义组——全部接口 Set 值）            *)
(* ============================================================ *)
Section ReqEntropyWorld.

(* ---- req 化 exp_neg 外延引擎（基座 L66223 exp_neg_req_compat_setoid 对位； *)
(*   接口无 exp_neg_ext 字段——le_antisym + exp_neg_le_decr + lt_le_iff 自足  *)
(*   重建，与基座同链；分级：对位直引真证）                                  *)
Lemma req_exp_neg_ext_local : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply (exp_neg_le_decr y x).
    apply (lt_le_iff y x). right. apply (req_sym x y Hxy).
  - apply (exp_neg_le_decr x y).
    apply (lt_le_iff x y). right. exact Hxy.
Qed.

(* ---- 基座 real_le_eps_Kone L47809 对位（e ≤ k·(1+e)） ----
   链：e ≤ 1·e ≤ k·e（le_mult_compat，1 < k）⟹ e ≤ k·e + k
   ⟹ 右端 == k·(1+e)（distrib + mult_one + comm）——分级：真证 *)
Lemma req_le_eps_Kone : forall e k : R,
  lt zero e -> lt zero k -> lt one k -> le e (mult k (plus one e)).
Proof.
  intros e k He Hk Hk1.
  assert (Hlek : le e (mult k e)).
  { apply (le_trans e (mult one e) (mult k e)).
    - apply (le_id_l e (mult one e) (mult one e)
               (req_sym (mult one e) e (req_mult_one_l e))
               (le_refl (mult one e))).
    - apply (le_mult_compat one k e He).
      apply (lt_le_iff one k). left. exact Hk1. }
  apply (le_id_r e (plus (mult k e) k) (mult k (plus one e))).
  - apply (req_sym (mult k (plus one e)) (plus (mult k e) k)).
    apply (req_trans (mult k (plus one e))
                     (plus (mult k one) (mult k e))
                     (plus (mult k e) k)).
    + apply distrib.
    + apply (req_trans (plus (mult k one) (mult k e))
                       (plus k (mult k e))
                       (plus (mult k e) k)).
      * apply (req_plus_compat (mult k one) k (mult k e) (mult k e)
                               (mult_one k) (req_refl (mult k e))).
      * apply plus_comm.
  - apply (le_trans e (mult k e) (plus (mult k e) k)).
    + exact Hlek.
    + apply (req_le_plus_nonneg_r (mult k e) k).
      apply (lt_le_iff zero k). left. exact Hk.
Qed.

(* ---- 基座 real_scal_sum_ge L47997 对位（s·a ≤ s·(a+b+c+d+1)） ----
   链：左嵌和三次 plus_assoc 重排为 a·(b+(c+(d+1))) → distrib 切出 s·a
   ⟹ s·a ≤ s·a + s·W（W > 0 逐段 plus_positive）——分级：真证 *)
Lemma req_scal_sum_ge : forall (s a b c d : R),
  lt zero s -> lt zero a -> lt zero b -> lt zero c -> lt zero d ->
  le (mult s a)
     (mult s (plus (plus (plus (plus a b) c) d) one)).
Proof.
  intros s a b c d Hs Ha Hb Hc Hd.
  assert (Hd1 : lt zero (plus d one))
    by (apply (plus_positive d one); [exact Hd | apply one_pos]).
  assert (Hcd1 : lt zero (plus c (plus d one)))
    by (apply (plus_positive c (plus d one)); [exact Hc | exact Hd1]).
  assert (HW : lt zero (plus b (plus c (plus d one))))
    by (apply (plus_positive b (plus c (plus d one))); [exact Hb | exact Hcd1]).
  apply (le_id_r (mult s a)
                 (plus (mult s a) (mult s (plus b (plus c (plus d one)))))
                 (mult s (plus (plus (plus (plus a b) c) d) one))).
  - apply (req_sym (mult s (plus (plus (plus (plus a b) c) d) one))
                   (plus (mult s a) (mult s (plus b (plus c (plus d one)))))).
    apply (req_trans (mult s (plus (plus (plus (plus a b) c) d) one))
                     (mult s (plus a (plus b (plus c (plus d one)))))
                     (plus (mult s a) (mult s (plus b (plus c (plus d one)))))).
    + apply (req_mult_compat s s (plus (plus (plus (plus a b) c) d) one)
                             (plus a (plus b (plus c (plus d one))))).
      * apply (req_refl s).
      * apply (req_trans (plus (plus (plus (plus a b) c) d) one)
                         (plus (plus (plus a b) c) (plus d one))
                         (plus a (plus b (plus c (plus d one))))).
        -- apply (req_sym (plus (plus (plus a b) c) (plus d one))
                          (plus (plus (plus (plus a b) c) d) one)
                          (plus_assoc (plus (plus a b) c) d one)).
        -- apply (req_trans (plus (plus (plus a b) c) (plus d one))
                            (plus (plus a b) (plus c (plus d one)))
                            (plus a (plus b (plus c (plus d one))))).
           ++ apply (req_sym (plus (plus a b) (plus c (plus d one)))
                             (plus (plus (plus a b) c) (plus d one))
                             (plus_assoc (plus a b) c (plus d one))).
           ++ apply (req_sym (plus a (plus b (plus c (plus d one))))
                             (plus (plus a b) (plus c (plus d one)))
                             (plus_assoc a b (plus c (plus d one)))).
    + apply distrib.
  - apply (req_le_plus_nonneg_r (mult s a)
                                (mult s (plus b (plus c (plus d one))))).
    apply (lt_le_iff zero (mult s (plus b (plus c (plus d one))))).
    left. apply (mult_positive s (plus b (plus c (plus d one))) Hs HW).
Qed.

(* ---- 基座 real_M_inv_absorb L48129 对位（M·(M⁻¹·x) == x） ----
   链：assoc → inv_pos_correct 换形 → mult_one_l——分级：真证（幂等 δ 对偶段） *)
Lemma req_M_inv_absorb : forall (M x : R) (HM : lt zero M),
  req (mult M (mult (inv_pos M HM) x)) x.
Proof.
  intros M x HM.
  apply (req_trans (mult M (mult (inv_pos M HM) x))
                   (mult (mult M (inv_pos M HM)) x)
                   x).
  - apply mult_assoc.
  - apply (req_trans (mult (mult M (inv_pos M HM)) x)
                     (mult one x)
                     x).
    + apply (req_mult_compat (mult M (inv_pos M HM)) one x x
                             (inv_pos_correct M HM) (req_refl x)).
    + apply (req_mult_one_l x).
Qed.

(* ---- 基座 real_abs_exp_pos L48538 对位（0 < |e^{−x}|） ----
   接口引擎：exp_neg_pos（基座引擎 cauchy_real_exp_pos 的 req 对位，自足）
   + abs_pos 换形——分级：真证（平凡直引段） *)
Lemma req_abs_exp_pos : forall x : R, lt zero (abs (exp_neg x)).
Proof.
  intro x.
  apply (lt_id_r zero (exp_neg x) (abs (exp_neg x))).
  - exact (req_sym (abs (exp_neg x)) (exp_neg x)
                   (abs_pos (exp_neg x) (exp_neg_pos x))).
  - apply exp_neg_pos.
Qed.

(* ---- 熵定义组（基座 L51341-51355 逐位 req 化） ---- *)
Variable Omega_A : forall (E_A : R), lt zero E_A -> R.
Variable Omega_B : forall (E_B : R), lt zero E_B -> R.
Variable Omega_A_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (Omega_A E_A H).
Variable Omega_B_pos : forall (E_B : R) (H : lt zero E_B),
  lt zero (Omega_B E_B H).
Variable E_total : R.
Variable k_B : R.
Variable E_B_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (plus E_total (opp E_A)).

(* 基座 real_E_B_ent L51341（假设位逐位对应；dOmega_* / Omega_B_wd 随登记表 2 冻结） *)
Definition req_E_B_ent (E_A : R) (H : lt zero E_A) : R :=
  plus E_total (opp E_A).

(* 基座 real_Omega_total_ent L51343 *)
Definition req_Omega_total_ent (E_A : R) (H : lt zero E_A) : R :=
  mult (Omega_A E_A H) (Omega_B (req_E_B_ent E_A H) (E_B_pos E_A H)).

(* ===== 基座 real_Omega_total_pos L51345 对位（Ω_A·Ω_B > 0） ===== *)
Lemma req_Omega_total_pos : forall (E_A : R) (H : lt zero E_A),
  lt zero (req_Omega_total_ent E_A H).
Proof.
  intros E_A H. unfold req_Omega_total_ent.
  apply (mult_positive (Omega_A E_A H)
                       (Omega_B (req_E_B_ent E_A H) (E_B_pos E_A H))).
  - exact (Omega_A_pos E_A H).
  - exact (Omega_B_pos (req_E_B_ent E_A H) (E_B_pos E_A H)).
Qed.

(* 基座 real_entropy_ent L51357：S := k_B·log Ω_total（熵定义组第 3 件） *)
Definition req_entropy_ent (E_A : R) (H : lt zero E_A) : R :=
  mult k_B (log (req_Omega_total_ent E_A H) (req_Omega_total_pos E_A H)).

End ReqEntropyWorld.


(* ============================================================ *)
(* Part 4：逐出区 interface-level req 化（基座 RealKVQuantMain    *)
(*   L53932-54965 对位 + epos 定义组 + P1 桥假设位）              *)
(*   签名变化（登记表 3 续）：接口无 plain exp——e^{·} 全部以         *)
(*   req_epos（:= exp_neg∘opp）重建；real_le 类假设位中接口 le     *)
(*   字段抽象不可分解者取 Or 分解形（逐位同构，见登记表 1 续）        *)
(* ============================================================ *)
Section ReqKVQuantWorld.
Variable S : Type.

(* ---- 逐出结构（基座 L53938-53940 同形：Set 层可判定） ---- *)
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

Variable transition : S -> S -> R.
(* 基座 real_transition_nonneg（real_le zero T，real_le 实为 Or 形）的逐位
   req 对偶：setoid 接口 le 字段抽象不可分解——假设位取 Or 分解形逐位同构；
   需接口 le zero T 处以 lt_le_iff 消解（本区 B4） *)
Variable transition_nonneg : forall s s' : S,
  Or (lt zero (transition s s')) (req zero (transition s s')).
Variable transition_sym : forall s s' : S,
  req (transition s s') (transition s' s).

Variable energy : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable L : R.
Variable L_pos : lt zero L.
Variable E_max : R.
Variable metric : S -> S -> R.
Variable metric_nonneg : forall s s' : S, le zero (metric s s').
(* 能量 Lipschitz：|e(s) − e(s')| ≤ L·metric（评审点名假设，逐位同构） *)
Variable energy_lipschitz : forall s s' : S,
  le (abs (plus (energy s) (opp (energy s'))))
     (mult L (metric s s')).
(* 能量下界：−E_max ≤ e(s) *)
Variable energy_lower : forall s : S, le (opp E_max) (energy s).
Variable sum_over_S : (S -> R) -> R.

(* ---- epos 定义组：正指数幂 e^{x} := exp_neg (opp x) ----
   （接口无 plain exp；exp_neg 逆的 req 重建，B3/B4 的 e^{E_max/D}、 *)
(*    e^{|u−v|}、e^{Ulips} 全部以此形式陈述）                        *)
Definition req_epos (x : R) : R := exp_neg (opp x).

Lemma req_epos_le_mono : forall x y : R, le x y -> le (req_epos x) (req_epos y).
Proof.
  intros x y Hxy. unfold req_epos.
  apply (exp_neg_le_decr (opp y) (opp x)).
  apply (opp_le_compat x y). exact Hxy.
Qed.

(* ---- P1 桥假设位（诚实登记表 1 续）：基座 real_exp_neg_diff_bound L53901
   的 req 对偶；其引擎 real_exp_abs_minus_one_eps 为 Real/Q 层 exp 分析
   （LogDiffPhase4 域），setoid 接口无 exp 线性 eps 字段——
   UpSigMigrate2 唯一诚实缺口 req_log_exp_neg 模式。P1 给出为桥，
   其余 B2/B3a/B3b/B3c/B4 各件全部真证 ---- *)
Variable req_boltzmann_diff_bridge : forall (u v eps : R),
  lt zero eps ->
  le (abs (plus (exp_neg u) (opp (exp_neg v))))
     (mult (exp_neg v)
           (plus (mult (abs (plus u (opp v))) (req_epos (abs (plus u (opp v)))))
                 eps)).

(* ---- 工具 A（基座 L54018 real_mult_minus_l 对位）：
   a·x + −(a·y) == a·(x + −y)（distrib + req_opp_mult_l）——真证 ---- *)
Lemma req_mult_minus_l : forall a x y : R,
  req (plus (mult a x) (opp (mult a y))) (mult a (plus x (opp y))).
Proof.
  intros a x y.
  apply (req_sym (mult a (plus x (opp y))) (plus (mult a x) (opp (mult a y)))).
  apply (req_trans (mult a (plus x (opp y)))
                   (plus (mult a x) (mult a (opp y)))
                   (plus (mult a x) (opp (mult a y)))).
  - apply distrib.
  - apply (req_plus_compat (mult a x) (mult a x)
                           (mult a (opp y)) (opp (mult a y))
                           (req_refl (mult a x)) (req_opp_mult_l a y)).
Qed.

(* ---- 工具 C（基座 L54037 real_mult_minus_r 对位）：
   x·z + −(y·z) == (x + −y)·z（req_opp_mult_r + distrib_r）——真证 ---- *)
Lemma req_mult_minus_r : forall x y z : R,
  req (plus (mult x z) (opp (mult y z))) (mult (plus x (opp y)) z).
Proof.
  intros x y z.
  apply (req_trans (plus (mult x z) (opp (mult y z)))
                   (plus (mult x z) (mult (opp y) z))
                   (mult (plus x (opp y)) z)).
  - apply (req_plus_compat (mult x z) (mult x z)
                           (opp (mult y z)) (mult (opp y) z)
                           (req_refl (mult x z))).
    apply (req_sym (mult (opp y) z) (opp (mult y z))).
    apply req_opp_mult_r.
  - apply (req_sym (mult (plus x (opp y)) z) (plus (mult x z) (mult (opp y) z))).
    apply req_mult_plus_distr_r.
Qed.

(* ---- 工具 E'（le zero Ulips 导出件）：0 < p ⟹ 0 ≤ x ⟹ 0 ≤ p·x ----
   le 字段抽象不可分解下 p·x ≥ 0 的接口级导出：zero·p ≤ x·p
   （le_mult_compat，p > 0 严格位）+ 交换运输——分级：真证 ---- *)
Lemma req_le_zero_mult_pos_l : forall p x : R,
  lt zero p -> le zero x -> le zero (mult p x).
Proof.
  intros p x Hp Hx.
  apply (le_id_l zero (mult zero p) (mult p x)).
  - apply (req_sym (mult zero p) zero).
    apply (req_trans (mult zero p) (mult p zero) zero).
    + apply mult_comm.
    + apply mult_zero.
  - apply (le_trans (mult zero p) (mult x p) (mult p x)).
    + apply (le_mult_compat zero x p Hp Hx).
    + apply (le_id_l (mult x p) (mult p x) (mult p x)
                     (mult_comm x p) (le_refl (mult p x))).
Qed.

(* ---- 工具 D'（基座 L54054 real_abs_nonneg_req 的 Or 形对位）：
   Or (0 < x) (0 == x) ⟹ |x| == x——分级：真证 ---- *)
Lemma req_abs_nonneg_id_or : forall x : R,
  Or (lt zero x) (req zero x) -> req (abs x) x.
Proof.
  intros x Hx. destruct Hx as [Hlt | Heq].
  - apply abs_pos. exact Hlt.
  - apply (req_trans (abs x) zero x).
    + apply (req_trans (abs x) (abs zero) zero).
      * apply (req_abs_compat x zero (req_sym zero x Heq)).
      * apply abs_zero.
    + exact Heq.
Qed.

(* ---- 工具 1（基座 L53731 real_exp_neg_split 对位）：
   e^{−u} == e^{−v}·e^{−(u−v)}（req_exp_neg_ext_local + exp_neg_plus）——真证 ---- *)
Lemma req_exp_neg_split : forall u v : R,
  req (exp_neg u) (mult (exp_neg v) (exp_neg (plus u (opp v)))).
Proof.
  intros u v.
  assert (Hsum : req (plus v (plus u (opp v))) u).
  { apply (req_trans (plus v (plus u (opp v)))
                     (plus (plus v u) (opp v))
                     u).
    - apply plus_assoc.
    - apply (req_trans (plus (plus v u) (opp v))
                       (plus (plus u v) (opp v))
                       u).
      + apply (req_plus_compat (plus v u) (plus u v) (opp v) (opp v)
                               (plus_comm v u) (req_refl (opp v))).
      + apply (req_trans (plus (plus u v) (opp v))
                         (plus u (plus v (opp v)))
                         u).
        * apply (req_sym (plus u (plus v (opp v)))
                         (plus (plus u v) (opp v))).
          apply plus_assoc.
        * apply (req_trans (plus u (plus v (opp v)))
                           (plus u zero)
                           u).
          -- apply (req_plus_compat u u (plus v (opp v)) zero
                                    (req_refl u) (plus_opp v)).
          -- apply plus_zero. }
  apply (req_trans (exp_neg u)
                   (exp_neg (plus v (plus u (opp v))))
                   (mult (exp_neg v) (exp_neg (plus u (opp v))))).
  - apply (req_exp_neg_ext_local u (plus v (plus u (opp v)))).
    apply (req_sym (plus v (plus u (opp v))) u). exact Hsum.
  - apply exp_neg_plus.
Qed.

(* ---- 工具 2b（基座 L53767 real_mult_minus_one_distr 对位）：
   a·(c − 1) == a·c + −a——真证 ---- *)
Lemma req_mult_minus_one_distr : forall a c : R,
  req (mult a (plus c (opp one))) (plus (mult a c) (opp a)).
Proof.
  intros a c.
  apply (req_trans (mult a (plus c (opp one)))
                   (plus (mult a c) (mult a (opp one)))
                   (plus (mult a c) (opp a))).
  - apply distrib.
  - apply (req_plus_compat (mult a c) (mult a c)
                           (mult a (opp one)) (opp a)
                           (req_refl (mult a c))).
    apply (req_trans (mult a (opp one)) (opp (mult a one)) (opp a)).
    + apply req_opp_mult_l.
    + apply (req_opp_compat (mult a one) a). apply mult_one.
Qed.

(* ===== 基座 L53790 real_exp_neg_diff_abs 对位（真证）：
   |e^{−u} − e^{−v}| == e^{−v}·|e^{−(u−v)} − 1| ----
   链：split 提因子 → mult_minus_one_distr → abs_compat → abs_mult
   → abs_pos(e^{−v}) 换形 ---- *)
Lemma req_exp_neg_diff_abs : forall u v : R,
  req (abs (plus (exp_neg u) (opp (exp_neg v))))
      (mult (exp_neg v)
            (abs (plus (exp_neg (plus u (opp v))) (opp one)))).
Proof.
  intros u v.
  pose proof (req_exp_neg_split u v) as Hsplit.
  apply (req_trans (abs (plus (exp_neg u) (opp (exp_neg v))))
                   (abs (mult (exp_neg v)
                              (plus (exp_neg (plus u (opp v))) (opp one))))
                   (mult (exp_neg v)
                         (abs (plus (exp_neg (plus u (opp v))) (opp one))))).
  - apply (req_abs_compat (plus (exp_neg u) (opp (exp_neg v)))
                          (mult (exp_neg v)
                                (plus (exp_neg (plus u (opp v))) (opp one)))).
    apply (req_trans (plus (exp_neg u) (opp (exp_neg v)))
                     (plus (mult (exp_neg v) (exp_neg (plus u (opp v))))
                           (opp (exp_neg v)))
                     (mult (exp_neg v)
                           (plus (exp_neg (plus u (opp v))) (opp one)))).
    + apply (req_plus_compat (exp_neg u)
                             (mult (exp_neg v) (exp_neg (plus u (opp v))))
                             (opp (exp_neg v)) (opp (exp_neg v))
                             Hsplit (req_refl (opp (exp_neg v)))).
    + apply (req_sym (mult (exp_neg v)
                           (plus (exp_neg (plus u (opp v))) (opp one)))
                     (plus (mult (exp_neg v) (exp_neg (plus u (opp v))))
                           (opp (exp_neg v)))).
      apply (req_mult_minus_one_distr (exp_neg v)
                                      (exp_neg (plus u (opp v)))).
  - apply (req_trans (abs (mult (exp_neg v)
                                (plus (exp_neg (plus u (opp v))) (opp one))))
                     (mult (abs (exp_neg v))
                           (abs (plus (exp_neg (plus u (opp v))) (opp one))))
                     (mult (exp_neg v)
                           (abs (plus (exp_neg (plus u (opp v))) (opp one))))).
    + apply abs_mult.
    + apply (req_mult_compat (abs (exp_neg v)) (exp_neg v)
                             (abs (plus (exp_neg (plus u (opp v))) (opp one)))
                             (abs (plus (exp_neg (plus u (opp v))) (opp one)))
                             (abs_pos (exp_neg v) (exp_neg_pos v))
                             (req_refl (abs (plus (exp_neg (plus u (opp v)))
                                                  (opp one))))).
Qed.

(* ---- Boltzmann 因子与逐出分布（基座 L53963-53990 逐位 req 化） ---- *)
Definition req_kv_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition req_evicted_partition : R :=
  sum_over_S (fun s : S => match keep_dec s with
                           | inl _ => req_kv_boltzmann_factor s
                           | inr _ => zero
                           end).

Variable req_evicted_partition_pos : lt zero req_evicted_partition.

Definition req_evicted_transition (s s' : S) : R :=
  match keep_dec s with
  | inl _ =>
      match keep_dec s' with
      | inl _ => transition s s'
      | inr _ => zero
      end
  | inr _ => zero
  end.

Definition req_evicted_boltzmann (s : S) : R :=
  match keep_dec s with
  | inl _ =>
      mult (inv_pos req_evicted_partition req_evicted_partition_pos)
           (req_kv_boltzmann_factor s)
  | inr _ => zero
  end.

(* 逐出导致的详细平衡破缺（基座 L53992 逐位 req 化） *)
Definition req_db_breaking (s s' : S) : R :=
  abs (plus (mult (req_evicted_boltzmann s) (req_evicted_transition s s'))
            (opp (mult (req_evicted_boltzmann s') (req_evicted_transition s' s)))).

(* ===== 基座 L54055 real_db_breaking_evicted_l 对位（真证）：
   s 被逐出 ⟹ db(s,s') == 0 ---- *)
Lemma req_db_breaking_evicted_l : forall s s' : S, Not (keep s) ->
  req (req_db_breaking s s') zero.
Proof.
  intros s s' Hnk. unfold req_db_breaking.
  assert (H1 : req (mult (req_evicted_boltzmann s) (req_evicted_transition s s'))
                   zero).
  { unfold req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - exact (match Hnk Hks with end).
    - apply (mult_zero zero). }
  assert (H2 : req (mult (req_evicted_boltzmann s') (req_evicted_transition s' s))
                   zero).
  { unfold req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s') as [Hks' | Hnks'].
    + destruct (keep_dec s) as [Hks | Hnks].
      * exact (match Hnk Hks with end).
      * apply (mult_zero (mult (inv_pos req_evicted_partition
                                          req_evicted_partition_pos)
                               (req_kv_boltzmann_factor s'))).
    + destruct (keep_dec s) as [Hks | Hnks].
      * exact (match Hnk Hks with end).
      * apply (mult_zero zero). }
  assert (Hopp : req (opp (mult (req_evicted_boltzmann s')
                                (req_evicted_transition s' s)))
                     zero).
  { apply (req_trans (opp (mult (req_evicted_boltzmann s')
                                (req_evicted_transition s' s)))
                     (opp zero) zero).
    - apply (req_opp_compat (mult (req_evicted_boltzmann s')
                                  (req_evicted_transition s' s))
                            zero H2).
    - apply (req_trans (opp zero) (plus (opp zero) zero) zero).
      + apply (req_sym (plus (opp zero) zero) (opp zero)).
        apply plus_zero.
      + apply (req_trans (plus (opp zero) zero) (plus zero (opp zero)) zero).
        * apply plus_comm.
        * apply plus_opp. }
  apply (req_trans (abs (plus (mult (req_evicted_boltzmann s)
                                    (req_evicted_transition s s'))
                              (opp (mult (req_evicted_boltzmann s')
                                         (req_evicted_transition s' s)))))
                   (abs (plus zero zero))
                   zero).
  - apply (req_abs_compat (plus (mult (req_evicted_boltzmann s)
                                      (req_evicted_transition s s'))
                                (opp (mult (req_evicted_boltzmann s')
                                           (req_evicted_transition s' s))))
                          (plus zero zero)).
    apply (req_plus_compat (mult (req_evicted_boltzmann s)
                                         (req_evicted_transition s s'))
                           zero
                           (opp (mult (req_evicted_boltzmann s')
                                      (req_evicted_transition s' s)))
                           zero H1 Hopp).
  - apply (req_trans (abs (plus zero zero)) (abs zero) zero).
    + apply (req_abs_compat (plus zero zero) zero (plus_zero zero)).
    + apply abs_zero.
Qed.

(* ---- B3a（基座 L54461 real_energy_lipschitz_scaled 对位，真证）：
   |u − v| ≤ (invD·L)·metric，u := invD·e(s)、v := invD·e(s') ----
   链：工具 A 提左因子 → abs_mult + abs_pos(invD) → 乘保序（invD > 0
   + lipschitz）→ assoc 换形 ---- *)
Lemma req_energy_lipschitz_scaled : forall s s' : S,
  le (abs (plus (mult (inv_pos D D_pos) (energy s))
                (opp (mult (inv_pos D D_pos) (energy s')))))
     (mult (mult (inv_pos D D_pos) L) (metric s s')).
Proof.
  intros s s'.
  assert (Hw : req (plus (mult (inv_pos D D_pos) (energy s))
                         (opp (mult (inv_pos D D_pos) (energy s'))))
                   (mult (inv_pos D D_pos)
                         (plus (energy s) (opp (energy s'))))).
  { apply (req_mult_minus_l (inv_pos D D_pos) (energy s) (energy s')). }
  assert (Habs : req (abs (plus (mult (inv_pos D D_pos) (energy s))
                                (opp (mult (inv_pos D D_pos) (energy s')))))
                     (mult (inv_pos D D_pos)
                           (abs (plus (energy s) (opp (energy s')))))).
  { apply (req_trans (abs (plus (mult (inv_pos D D_pos) (energy s))
                                (opp (mult (inv_pos D D_pos) (energy s')))))
                     (abs (mult (inv_pos D D_pos)
                                (plus (energy s) (opp (energy s')))))
                     (mult (inv_pos D D_pos)
                           (abs (plus (energy s) (opp (energy s')))))).
    - apply (req_abs_compat (plus (mult (inv_pos D D_pos) (energy s))
                                  (opp (mult (inv_pos D D_pos) (energy s'))))
                            (mult (inv_pos D D_pos)
                                  (plus (energy s) (opp (energy s')))) Hw).
    - apply (req_trans (abs (mult (inv_pos D D_pos)
                                  (plus (energy s) (opp (energy s')))))
                       (mult (abs (inv_pos D D_pos))
                             (abs (plus (energy s) (opp (energy s')))))
                       (mult (inv_pos D D_pos)
                             (abs (plus (energy s) (opp (energy s')))))).
      + apply abs_mult.
      + apply (req_mult_compat (abs (inv_pos D D_pos)) (inv_pos D D_pos)
                               (abs (plus (energy s) (opp (energy s'))))
                               (abs (plus (energy s) (opp (energy s'))))
                               (abs_pos (inv_pos D D_pos) (inv_pos_pos D D_pos))
                               (req_refl (abs (plus (energy s)
                                                    (opp (energy s')))))). }
  assert (Hle : le (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos) (mult L (metric s s')))).
  { apply (req_le_mult_compat_r (inv_pos D D_pos)
                                (abs (plus (energy s) (opp (energy s'))))
                                (mult L (metric s s'))).
    - apply (lt_le_iff zero (inv_pos D D_pos)). left.
      apply (inv_pos_pos D D_pos).
    - exact (energy_lipschitz s s'). }
  apply (le_trans (abs (plus (mult (inv_pos D D_pos) (energy s))
                             (opp (mult (inv_pos D D_pos) (energy s')))))
                  (mult (inv_pos D D_pos)
                        (abs (plus (energy s) (opp (energy s')))))
                  (mult (mult (inv_pos D D_pos) L) (metric s s'))).
  - apply (le_id_l (abs (plus (mult (inv_pos D D_pos) (energy s))
                              (opp (mult (inv_pos D D_pos) (energy s')))))
                   (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   Habs (le_refl (mult (inv_pos D D_pos)
                                       (abs (plus (energy s)
                                                  (opp (energy s'))))))).
  - apply (le_id_r (mult (inv_pos D D_pos)
                         (abs (plus (energy s) (opp (energy s')))))
                   (mult (inv_pos D D_pos) (mult L (metric s s')))
                   (mult (mult (inv_pos D D_pos) L) (metric s s'))).
    + apply mult_assoc.
    + exact Hle.
Qed.

(* ---- B3b（基座 L54529 real_boltzmann_upper 对位，真证）：
   b(s') ≤ e^{E_max/D}（= req_epos(invD·E_max)） ----
   链：invD·(−E_max) ≤ invD·e(s')（乘保序 + 能量下界）→ exp_neg 递减
   → −(invD·(−E_max)) == invD·E_max（req_opp_mult_l） ---- *)
Lemma req_boltzmann_upper : forall s' : S,
  le (req_kv_boltzmann_factor s')
     (req_epos (mult (inv_pos D D_pos) E_max)).
Proof.
  intro s'.
  assert (Hle : le (mult (inv_pos D D_pos) (opp E_max))
                   (mult (inv_pos D D_pos) (energy s'))).
  { apply (req_le_mult_compat_r (inv_pos D D_pos) (opp E_max) (energy s')).
    - apply (lt_le_iff zero (inv_pos D D_pos)). left.
      apply (inv_pos_pos D D_pos).
    - exact (energy_lower s'). }
  assert (Hdec : le (exp_neg (mult (inv_pos D D_pos) (energy s')))
                    (exp_neg (mult (inv_pos D D_pos) (opp E_max)))).
  { apply (exp_neg_le_decr (mult (inv_pos D D_pos) (opp E_max))
                           (mult (inv_pos D D_pos) (energy s'))).
    exact Hle. }
  apply (le_id_r (req_kv_boltzmann_factor s')
                 (exp_neg (mult (inv_pos D D_pos) (opp E_max)))
                 (req_epos (mult (inv_pos D D_pos) E_max))).
  - unfold req_epos.
    apply (req_exp_neg_ext_local (mult (inv_pos D D_pos) (opp E_max))
                                 (opp (mult (inv_pos D D_pos) E_max))).
    apply req_opp_mult_l.
  - unfold req_kv_boltzmann_factor. exact Hdec.
Qed.


(* ---- B3c（基座 L54604 real_abs_diff_prod_bound 对位，真证）：
   |u−v|·e^{|u−v|} ≤ Ulips·e^{Ulips} + eps'
   （Ulips := (invD·L)·metric；le zero Ulips 由 req_le_zero_mult_pos_l
   自 metric_nonneg 导出——基座此步走 Q 逐点 real_abs_prod_le_eps，
   setoid 层改走 le_mult_compat/req_le_mult_compat_r 双段单调） ---- *)
Definition req_ulips (s s' : S) : R :=
  mult (mult (inv_pos D D_pos) L) (metric s s').

Definition req_duv (s s' : S) : R :=
  plus (mult (inv_pos D D_pos) (energy s))
       (opp (mult (inv_pos D D_pos) (energy s'))).

Lemma req_abs_diff_prod_bound : forall (s s' : S) (eps' : R),
  lt zero eps' ->
  le (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s'))))
     (plus (mult (req_ulips s s') (req_epos (req_ulips s s'))) eps').
Proof.
  intros s s' eps' Hep'.
  assert (H1 : le (abs (req_duv s s')) (req_ulips s s')).
  { exact (req_energy_lipschitz_scaled s s'). }
  assert (HzU : le zero (req_ulips s s')).
  { unfold req_ulips.
    apply (req_le_zero_mult_pos_l (mult (inv_pos D D_pos) L) (metric s s')).
    - apply (mult_positive (inv_pos D D_pos) L (inv_pos_pos D D_pos) L_pos).
    - exact (metric_nonneg s s'). }
  assert (HltE : lt zero (req_epos (abs (req_duv s s')))).
  { unfold req_epos. apply exp_neg_pos. }
  assert (Hmono : le (req_epos (abs (req_duv s s')))
                     (req_epos (req_ulips s s'))).
  { apply (req_epos_le_mono (abs (req_duv s s')) (req_ulips s s')). exact H1. }
  apply (le_trans (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s'))))
                  (mult (req_ulips s s') (req_epos (abs (req_duv s s'))))
                  (plus (mult (req_ulips s s') (req_epos (req_ulips s s')))
                        eps')).
  - apply (le_mult_compat (abs (req_duv s s')) (req_ulips s s')
                          (req_epos (abs (req_duv s s'))) HltE H1).
  - apply (le_trans (mult (req_ulips s s') (req_epos (abs (req_duv s s'))))
                    (mult (req_ulips s s') (req_epos (req_ulips s s')))
                    (plus (mult (req_ulips s s') (req_epos (req_ulips s s')))
                          eps')).
    + apply (req_le_mult_compat_r (req_ulips s s')
                                  (req_epos (abs (req_duv s s')))
                                  (req_epos (req_ulips s s')) HzU Hmono).
    + apply (req_le_plus_nonneg_r
               (mult (req_ulips s s') (req_epos (req_ulips s s'))) eps').
      apply (lt_le_iff zero eps'). left. exact Hep'.
Qed.

(* ---- B2c（基座 L54304 real_db_breaking_kept_final 对位，真证）：
   双保留时 db == invZ·(T·|b(s) − b(s')|) ----
   链：T'==T（sym）→ 工具 C 右提 T → abs_mult + |T|==T（Or 工具 D'）→ comm；
   结构恒等：unfold+δ 分支 → assoc 反向 + 工具 A 提 invZ → abs_mult +
   abs_pos(invZ)；末段 mult_compat 传 Hinner ---- *)
Lemma req_db_breaking_kept_final : forall s s' : S,
  keep s -> keep s' ->
  req (req_db_breaking s s')
      (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
            (mult (transition s s')
                  (abs (plus (req_kv_boltzmann_factor s)
                             (opp (req_kv_boltzmann_factor s')))))).
Proof.
  intros s s' Hs Hs'.
  assert (Hinner : req (abs (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s)))))
                       (mult (transition s s')
                             (abs (plus (req_kv_boltzmann_factor s)
                                        (opp (req_kv_boltzmann_factor s')))))).
  { apply (req_trans
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s' s)))))
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s s')))))
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s)
                              (opp (req_kv_boltzmann_factor s')))))).
    - apply (req_abs_compat
               (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                     (opp (mult (req_kv_boltzmann_factor s')
                                (transition s' s))))
               (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                     (opp (mult (req_kv_boltzmann_factor s')
                                (transition s s'))))).
      apply (req_plus_compat
               (mult (req_kv_boltzmann_factor s) (transition s s'))
               (mult (req_kv_boltzmann_factor s) (transition s s'))
               (opp (mult (req_kv_boltzmann_factor s') (transition s' s)))
               (opp (mult (req_kv_boltzmann_factor s') (transition s s')))
               (req_refl (mult (req_kv_boltzmann_factor s) (transition s s')))
               (req_opp_compat
                  (mult (req_kv_boltzmann_factor s') (transition s' s))
                  (mult (req_kv_boltzmann_factor s') (transition s s'))
                  (req_mult_compat (req_kv_boltzmann_factor s')
                                   (req_kv_boltzmann_factor s')
                                   (transition s' s) (transition s s')
                                   (req_refl (req_kv_boltzmann_factor s'))
                                   (transition_sym s' s)))).
    - apply (req_trans
               (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                          (opp (mult (req_kv_boltzmann_factor s')
                                     (transition s s')))))
               (abs (mult (plus (req_kv_boltzmann_factor s)
                                (opp (req_kv_boltzmann_factor s')))
                          (transition s s')))
               (mult (transition s s')
                     (abs (plus (req_kv_boltzmann_factor s)
                                (opp (req_kv_boltzmann_factor s')))))).
      + apply (req_abs_compat
                 (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                       (opp (mult (req_kv_boltzmann_factor s')
                                  (transition s s'))))
                 (mult (plus (req_kv_boltzmann_factor s)
                             (opp (req_kv_boltzmann_factor s')))
                       (transition s s'))).
        apply (req_mult_minus_r (req_kv_boltzmann_factor s)
                                (req_kv_boltzmann_factor s')
                                (transition s s')).
      + apply (req_trans
                 (abs (mult (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s')))
                            (transition s s')))
                 (mult (abs (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s'))))
                       (abs (transition s s')))
                 (mult (transition s s')
                       (abs (plus (req_kv_boltzmann_factor s)
                                  (opp (req_kv_boltzmann_factor s')))))).
        * apply abs_mult.
        * apply (req_trans
                   (mult (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s'))))
                         (abs (transition s s')))
                   (mult (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s'))))
                         (transition s s'))
                   (mult (transition s s')
                         (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s')))))).
          -- apply (req_mult_compat
                      (abs (plus (req_kv_boltzmann_factor s)
                                 (opp (req_kv_boltzmann_factor s'))))
                      (abs (plus (req_kv_boltzmann_factor s)
                                 (opp (req_kv_boltzmann_factor s'))))
                      (abs (transition s s')) (transition s s')
                      (req_refl (abs (plus (req_kv_boltzmann_factor s)
                                           (opp (req_kv_boltzmann_factor s')))))
                      (req_abs_nonneg_id_or (transition s s')
                                            (transition_nonneg s s'))).
          -- apply mult_comm. }
  assert (Hk : req (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))).
  { unfold req_db_breaking, req_evicted_boltzmann, req_evicted_transition.
    destruct (keep_dec s) as [Hks | Hnks].
    - destruct (keep_dec s') as [Hks' | Hnks'].
      + apply (req_trans
                 (abs (plus (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                       (req_kv_boltzmann_factor s))
                                 (transition s s'))
                           (opp (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                           (req_kv_boltzmann_factor s'))
                                      (transition s' s)))))
                 (abs (mult (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s))))))
                 (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                       (abs (plus (mult (req_kv_boltzmann_factor s)
                                        (transition s s'))
                                  (opp (mult (req_kv_boltzmann_factor s')
                                             (transition s' s))))))).
        * apply (req_abs_compat
                   (plus (mult (mult (inv_pos req_evicted_partition
                                               req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s))
                                 (transition s s'))
                           (opp (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                           (req_kv_boltzmann_factor s'))
                                      (transition s' s))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (plus (mult (req_kv_boltzmann_factor s)
                                     (transition s s'))
                               (opp (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))).
          apply (req_trans
                   (plus (mult (mult (inv_pos req_evicted_partition
                                                req_evicted_partition_pos)
                                         (req_kv_boltzmann_factor s))
                               (transition s s'))
                         (opp (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                          (req_kv_boltzmann_factor s'))
                                    (transition s' s))))
                   (plus (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s)
                                     (transition s s')))
                         (opp (mult (inv_pos req_evicted_partition
                                             req_evicted_partition_pos)
                                    (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (plus (mult (req_kv_boltzmann_factor s)
                                     (transition s s'))
                               (opp (mult (req_kv_boltzmann_factor s')
                                          (transition s' s)))))).
          -- apply (req_plus_compat
                      (mult (mult (inv_pos req_evicted_partition
                                               req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s))
                            (transition s s'))
                      (mult (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (mult (req_kv_boltzmann_factor s)
                                  (transition s s')))
                      (opp (mult (mult (inv_pos req_evicted_partition
                                                   req_evicted_partition_pos)
                                       (req_kv_boltzmann_factor s'))
                                 (transition s' s)))
                      (opp (mult (inv_pos req_evicted_partition
                                          req_evicted_partition_pos)
                                 (mult (req_kv_boltzmann_factor s')
                                       (transition s' s))))
                      (req_sym
                         (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s)
                                     (transition s s')))
                         (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                     (req_kv_boltzmann_factor s))
                               (transition s s'))
                         (mult_assoc
                            (inv_pos req_evicted_partition
                                     req_evicted_partition_pos)
                            (req_kv_boltzmann_factor s) (transition s s')))
                      (req_opp_compat
                         (mult (mult (inv_pos req_evicted_partition
                                              req_evicted_partition_pos)
                                     (req_kv_boltzmann_factor s'))
                               (transition s' s))
                         (mult (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (mult (req_kv_boltzmann_factor s')
                                     (transition s' s)))
                         (req_sym
                            (mult (inv_pos req_evicted_partition
                                           req_evicted_partition_pos)
                                  (mult (req_kv_boltzmann_factor s')
                                        (transition s' s)))
                            (mult (mult (inv_pos req_evicted_partition
                                                 req_evicted_partition_pos)
                                        (req_kv_boltzmann_factor s'))
                                  (transition s' s))
                            (mult_assoc
                               (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (req_kv_boltzmann_factor s')
                               (transition s' s))))).
          -- apply (req_mult_minus_l
                      (inv_pos req_evicted_partition req_evicted_partition_pos)
                      (mult (req_kv_boltzmann_factor s) (transition s s'))
                      (mult (req_kv_boltzmann_factor s') (transition s' s))).
        * apply (req_trans
                   (abs (mult (inv_pos req_evicted_partition
                                       req_evicted_partition_pos)
                              (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (abs (inv_pos req_evicted_partition
                                       req_evicted_partition_pos))
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))).
          -- apply abs_mult.
          -- apply (req_mult_compat
                      (abs (inv_pos req_evicted_partition
                                    req_evicted_partition_pos))
                      (inv_pos req_evicted_partition req_evicted_partition_pos)
                      (abs (plus (mult (req_kv_boltzmann_factor s)
                                       (transition s s'))
                                 (opp (mult (req_kv_boltzmann_factor s')
                                            (transition s' s)))))
                      (abs (plus (mult (req_kv_boltzmann_factor s)
                                       (transition s s'))
                                 (opp (mult (req_kv_boltzmann_factor s')
                                            (transition s' s)))))
                      (abs_pos (inv_pos req_evicted_partition
                                        req_evicted_partition_pos)
                               (inv_pos_pos req_evicted_partition
                                            req_evicted_partition_pos))
                      (req_refl (abs (plus (mult (req_kv_boltzmann_factor s)
                                                 (transition s s'))
                                           (opp (mult (req_kv_boltzmann_factor s')
                                                      (transition s' s))))))).
      + exact (match Hnks' Hs' with end).
    - exact (match Hnks Hs with end). }
  apply (req_trans (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (abs (plus (mult (req_kv_boltzmann_factor s)
                                          (transition s s'))
                                    (opp (mult (req_kv_boltzmann_factor s')
                                               (transition s' s))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))).
  - exact Hk.
  - apply (req_mult_compat
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (abs (plus (mult (req_kv_boltzmann_factor s) (transition s s'))
                        (opp (mult (req_kv_boltzmann_factor s')
                                   (transition s' s)))))
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s)
                              (opp (req_kv_boltzmann_factor s')))))
             (req_refl (inv_pos req_evicted_partition req_evicted_partition_pos))
             Hinner).
Qed.

Definition req_Emax_exp : R := req_epos (mult (inv_pos D D_pos) E_max).
Definition req_eulips (s s' : S) : R := req_epos (req_ulips s s').

(* ---- B3 最终（基座 L54636 real_boltzmann_diff_bound 对位）：
   |b(s) − b(s')| ≤ E·(U·eU) + (E·eps + eps')——除 P1 桥外全真证 ---- *)
Lemma req_boltzmann_diff_bound : forall (s s' : S) (eps eps' : R),
  lt zero eps -> lt zero eps' ->
  le (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
     (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
           (plus (mult req_Emax_exp eps) eps')).
Proof.
  intros s s' eps eps' Hep Hep'.
  assert (HleEv : le (req_kv_boltzmann_factor s') req_Emax_exp).
  { exact (req_boltzmann_upper s'). }
  assert (H1 : le (abs (req_duv s s')) (req_ulips s s')).
  { exact (req_energy_lipschitz_scaled s s'). }
  assert (HltE : lt zero (req_epos (abs (req_duv s s')))).
  { unfold req_epos. apply exp_neg_pos. }
  assert (Hmono : le (req_epos (abs (req_duv s s'))) (req_eulips s s')).
  { apply (req_epos_le_mono (abs (req_duv s s')) (req_ulips s s')). exact H1. }
  assert (Hexp : req (mult (req_kv_boltzmann_factor s')
                           (plus (mult (abs (req_duv s s'))
                                       (req_epos (abs (req_duv s s'))))
                                 eps))
                     (plus (mult (req_kv_boltzmann_factor s')
                                 (mult (abs (req_duv s s'))
                                       (req_epos (abs (req_duv s s')))))
                           (mult (req_kv_boltzmann_factor s') eps))).
  { unfold req_kv_boltzmann_factor. apply distrib. }
  assert (Hle1 : le (abs (plus (req_kv_boltzmann_factor s)
                               (opp (req_kv_boltzmann_factor s'))))
                    (plus (mult (req_kv_boltzmann_factor s')
                                (mult (abs (req_duv s s'))
                                      (req_epos (abs (req_duv s s')))))
                          (mult (req_kv_boltzmann_factor s') eps))).
  { apply (le_id_r
             (abs (plus (req_kv_boltzmann_factor s)
                        (opp (req_kv_boltzmann_factor s'))))
             (mult (req_kv_boltzmann_factor s')
                   (plus (mult (abs (req_duv s s'))
                               (req_epos (abs (req_duv s s'))))
                         eps))
             (plus (mult (req_kv_boltzmann_factor s')
                         (mult (abs (req_duv s s'))
                               (req_epos (abs (req_duv s s')))))
                   (mult (req_kv_boltzmann_factor s') eps)))
    ; [ exact Hexp
      | exact (req_boltzmann_diff_bridge (mult (inv_pos D D_pos) (energy s))
                                         (mult (inv_pos D D_pos) (energy s'))
                                         eps Hep) ]. }
  assert (Hltduv : lt zero (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s'))))).
  { unfold req_kv_boltzmann_factor.
    apply (mult_positive (exp_neg (mult (inv_pos D D_pos) (energy s')))
                         (req_epos (abs (req_duv s s')))).
    - apply exp_neg_pos.
    - exact HltE. }
  assert (Hmono2 : le (mult (req_kv_boltzmann_factor s')
                            (req_epos (abs (req_duv s s'))))
                      (mult req_Emax_exp (req_eulips s s'))).
  { apply (le_trans (mult (req_kv_boltzmann_factor s')
                          (req_epos (abs (req_duv s s'))))
                    (mult req_Emax_exp (req_epos (abs (req_duv s s'))))
                    (mult req_Emax_exp (req_eulips s s'))).
    - apply (le_mult_compat (req_kv_boltzmann_factor s') req_Emax_exp
                            (req_epos (abs (req_duv s s'))) HltE HleEv).
    - apply (req_le_mult_compat_r req_Emax_exp
                                  (req_epos (abs (req_duv s s')))
                                  (req_eulips s s')).
      + apply (lt_le_iff zero req_Emax_exp). left.
        unfold req_Emax_exp, req_epos. apply exp_neg_pos.
      + exact Hmono. }
  assert (Heq1 : req (mult (req_kv_boltzmann_factor s')
                           (mult (abs (req_duv s s'))
                                 (req_epos (abs (req_duv s s')))))
                     (mult (abs (req_duv s s'))
                           (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s')))))).
  { apply (req_trans
             (mult (req_kv_boltzmann_factor s')
                   (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
             (mult (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                   (req_epos (abs (req_duv s s'))))
             (mult (abs (req_duv s s'))
                   (mult (req_kv_boltzmann_factor s')
                         (req_epos (abs (req_duv s s')))))).
    - apply mult_assoc.
    - apply (req_trans
               (mult (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                     (req_epos (abs (req_duv s s'))))
               (mult (mult (abs (req_duv s s')) (req_kv_boltzmann_factor s'))
                     (req_epos (abs (req_duv s s'))))
               (mult (abs (req_duv s s'))
                     (mult (req_kv_boltzmann_factor s')
                           (req_epos (abs (req_duv s s')))))).
      + apply (req_mult_compat
                 (mult (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                 (mult (abs (req_duv s s')) (req_kv_boltzmann_factor s'))
                 (req_epos (abs (req_duv s s')))
                 (req_epos (abs (req_duv s s')))
                 (mult_comm (req_kv_boltzmann_factor s') (abs (req_duv s s')))
                 (req_refl (req_epos (abs (req_duv s s'))))).
      + apply (req_sym
                 (mult (abs (req_duv s s'))
                       (mult (req_kv_boltzmann_factor s')
                             (req_epos (abs (req_duv s s')))))
                 (mult (mult (abs (req_duv s s'))
                             (req_kv_boltzmann_factor s'))
                       (req_epos (abs (req_duv s s'))))).
        apply mult_assoc. }
  assert (HzU : le zero (req_ulips s s')).
  { unfold req_ulips.
    apply (req_le_zero_mult_pos_l (mult (inv_pos D D_pos) L) (metric s s')).
    - apply (mult_positive (inv_pos D D_pos) L (inv_pos_pos D D_pos) L_pos).
    - exact (metric_nonneg s s'). }
  assert (HstepY : le (mult (req_ulips s s')
                            (mult (req_kv_boltzmann_factor s')
                                  (req_epos (abs (req_duv s s')))))
                      (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))).
  { apply (req_le_mult_compat_r (req_ulips s s')
                                (mult (req_kv_boltzmann_factor s')
                                      (req_epos (abs (req_duv s s'))))
                                (mult req_Emax_exp (req_eulips s s')))
    ; [ exact HzU | exact Hmono2 ]. }
  assert (Hbig1 : le (mult (abs (req_duv s s'))
                           (mult (req_kv_boltzmann_factor s')
                                 (req_epos (abs (req_duv s s')))))
                      (plus (mult (req_ulips s s')
                                  (mult req_Emax_exp (req_eulips s s')))
                            eps')).
  { apply (le_trans
             (mult (abs (req_duv s s'))
                   (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
             (mult (req_ulips s s') (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')).
    - apply (le_mult_compat (abs (req_duv s s')) (req_ulips s s')
                            (mult (req_kv_boltzmann_factor s')
                                  (req_epos (abs (req_duv s s'))))
                            Hltduv H1).
    - apply (le_trans
               (mult (req_ulips s s') (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
               (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')).
      + exact HstepY.
      + apply (req_le_plus_nonneg_r
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps').
        apply (lt_le_iff zero eps'). left. exact Hep'. }
  assert (Hbig1a : le (mult (req_kv_boltzmann_factor s')
                            (mult (abs (req_duv s s'))
                                  (req_epos (abs (req_duv s s')))))
                      (plus (mult (req_ulips s s')
                                  (mult req_Emax_exp (req_eulips s s')))
                            eps')).
  { exact (le_id_l (mult (req_kv_boltzmann_factor s')
                         (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                   (mult (abs (req_duv s s'))
                         (mult (req_kv_boltzmann_factor s') (req_epos (abs (req_duv s s')))))
                   (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                   Heq1 Hbig1). }
  assert (Hbig2 : le (mult (req_kv_boltzmann_factor s') eps)
                     (mult req_Emax_exp eps)).
  { apply (le_mult_compat (req_kv_boltzmann_factor s') req_Emax_exp eps
                          Hep HleEv). }
  assert (Hsum : le (plus (mult (req_kv_boltzmann_factor s')
                                (mult (abs (req_duv s s'))
                                      (req_epos (abs (req_duv s s')))))
                          (mult (req_kv_boltzmann_factor s') eps))
                    (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                          (mult req_Emax_exp eps))).
  { apply (le_plus_compat
             (mult (req_kv_boltzmann_factor s') (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
             (mult (req_kv_boltzmann_factor s') eps)
             (mult req_Emax_exp eps)
             Hbig1a Hbig2). }
  assert (HrA : req (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                    (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
  { apply (req_trans (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (mult (mult (req_ulips s s') req_Emax_exp) (req_eulips s s'))
                     (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (req_ulips s s') req_Emax_exp) (req_eulips s s'))
                       (mult (mult req_Emax_exp (req_ulips s s')) (req_eulips s s'))
                       (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))).
      + apply (req_mult_compat (mult (req_ulips s s') req_Emax_exp)
                               (mult req_Emax_exp (req_ulips s s'))
                               (req_eulips s s') (req_eulips s s')
                               (mult_comm (req_ulips s s') req_Emax_exp)
                               (req_refl (req_eulips s s'))).
      + apply (req_sym (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (mult (mult req_Emax_exp (req_ulips s s')) (req_eulips s s'))).
        apply mult_assoc. }
  assert (Hr : req
                 (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                       (mult req_Emax_exp eps))
                 (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (plus (mult req_Emax_exp eps) eps'))).
  { apply (req_trans
             (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                   (mult req_Emax_exp eps))
             (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))
             (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))).
    - apply (req_trans
               (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                     (mult req_Emax_exp eps))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (plus eps' (mult req_Emax_exp eps)))
               (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                     (plus (mult req_Emax_exp eps) eps'))).
      + apply (req_sym (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                             (plus eps' (mult req_Emax_exp eps)))
                       (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                             (mult req_Emax_exp eps))).
        apply plus_assoc.
      + apply (req_plus_compat
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                 (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
                 (plus eps' (mult req_Emax_exp eps))
                 (plus (mult req_Emax_exp eps) eps')
                 (req_refl (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))))
                 (plus_comm eps' (mult req_Emax_exp eps))).
    - apply (req_plus_compat
               (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s')))
               (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
               (plus (mult req_Emax_exp eps) eps')
               (plus (mult req_Emax_exp eps) eps')
               HrA
               (req_refl (plus (mult req_Emax_exp eps) eps'))). }
  apply (le_trans (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
                  (plus (mult (req_kv_boltzmann_factor s')
                              (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                        (mult (req_kv_boltzmann_factor s') eps))
                  (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                        (plus (mult req_Emax_exp eps) eps'))).
  - exact Hle1.
  - exact (le_id_r (plus (mult (req_kv_boltzmann_factor s')
                                    (mult (abs (req_duv s s')) (req_epos (abs (req_duv s s')))))
                              (mult (req_kv_boltzmann_factor s') eps))
                   (plus (plus (mult (req_ulips s s') (mult req_Emax_exp (req_eulips s s'))) eps')
                         (mult req_Emax_exp eps))
                   (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                         (plus (mult req_Emax_exp eps) eps'))
                   Hr Hsum).
Qed.

(* ---- B4 最终定理（基座 L54841 real_db_breaking_bound_eps 定理对位，真证）：
   db(s,s') ≤ invZ·T·[E·(U·eU) + (E·eps + eps')]
   组装：B2c 结构恒等 → B3 定量界 → 两层乘保序（T ≥ 0 的 Or 消解 +
   invZ > 0）→ le_trans 完成 ---- *)
Theorem req_db_breaking_bound_eps : forall (s s' : S) (eps eps' : R),
  keep s -> keep s' -> lt zero eps -> lt zero eps' ->
  le (req_db_breaking s s')
     (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
           (mult (transition s s')
                 (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                       (plus (mult req_Emax_exp eps) eps')))).
Proof.
  intros s s' eps eps' Hs Hs' Hep Hep'.
  assert (Hk : le (req_db_breaking s s')
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (abs (plus (req_kv_boltzmann_factor s)
                                         (opp (req_kv_boltzmann_factor s'))))))).
  { exact (le_id_l (req_db_breaking s s')
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))
                   (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                         (mult (transition s s')
                               (abs (plus (req_kv_boltzmann_factor s)
                                          (opp (req_kv_boltzmann_factor s'))))))
                   (req_db_breaking_kept_final s s' Hs Hs')
                   (le_refl (mult (inv_pos req_evicted_partition
                                             req_evicted_partition_pos)
                                  (mult (transition s s')
                                        (abs (plus (req_kv_boltzmann_factor s)
                                                   (opp (req_kv_boltzmann_factor s')))))))). }
  pose proof (req_boltzmann_diff_bound s s' eps eps' Hep Hep') as Hbd.
  assert (Hin : le (mult (transition s s')
                         (abs (plus (req_kv_boltzmann_factor s)
                                    (opp (req_kv_boltzmann_factor s')))))
                   (mult (transition s s')
                         (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                               (plus (mult req_Emax_exp eps) eps')))).
  { apply (req_le_mult_compat_r
             (transition s s')
             (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s'))))
             (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                   (plus (mult req_Emax_exp eps) eps'))).
    - apply (lt_le_iff zero (transition s s')). exact (transition_nonneg s s').
    - exact Hbd. }
  assert (Hout : le (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                          (mult (transition s s')
                                (abs (plus (req_kv_boltzmann_factor s)
                                           (opp (req_kv_boltzmann_factor s'))))))
                    (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                          (mult (transition s s')
                                (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                                      (plus (mult req_Emax_exp eps) eps'))))).
  { apply (req_le_mult_compat_r
             (inv_pos req_evicted_partition req_evicted_partition_pos)
             (mult (transition s s')
                   (abs (plus (req_kv_boltzmann_factor s) (opp (req_kv_boltzmann_factor s')))))
             (mult (transition s s')
                   (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                         (plus (mult req_Emax_exp eps) eps')))).
    - apply (lt_le_iff zero (inv_pos req_evicted_partition req_evicted_partition_pos)).
      left. apply (inv_pos_pos req_evicted_partition req_evicted_partition_pos).
    - exact Hin. }
  apply (le_trans (req_db_breaking s s')
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (abs (plus (req_kv_boltzmann_factor s)
                                         (opp (req_kv_boltzmann_factor s'))))))
                  (mult (inv_pos req_evicted_partition req_evicted_partition_pos)
                        (mult (transition s s')
                              (plus (mult req_Emax_exp (mult (req_ulips s s') (req_eulips s s')))
                                    (plus (mult req_Emax_exp eps) eps'))))).
  - exact Hk.
  - exact Hout.
Qed.

End ReqKVQuantWorld.

(* ============================================================ *)
(* 文件尾清单注记（核对登记表， ）                *)
(* ============================================================ *)
(*
      [Part 0] rls_ext/rls_linear/rls_nonneg/rls_single_le/rls_pos/rls_le/
      rls_kernel_norm_gen + req_lt_zero_le_trans/req_le_mult_le_one_r —— 全建。
      [Part 1] 14 件全建（另附 3 件辅助：req_partition_temp_pos/
      req_markov_pos/req_markov_kernel_unfold + req_pick_max_tf_le_minp_sum）。
      [Part 2] 6 件全建（含三枚 alb_markov_kernel 定义族 + alb_topp_keep/alb_topk_keep/
      combined_* 判定与计数结构）。
      [Part 3] req_exp_neg_ext_local/req_le_eps_Kone/req_scal_sum_ge/
      req_M_inv_absorb/req_abs_exp_pos + 熵定义组 3 件 + req_Omega_total_pos
      —— 全建（Section ReqEntropyWorld）。
      [Part 4] epos 定义组（req_epos/req_epos_le_mono）+ 环工具
      （req_mult_minus_l/req_mult_minus_r/req_le_zero_mult_pos_l/
      req_abs_nonneg_id_or）+ exp 引擎（req_exp_neg_split/
      req_exp_neg_diff_abs）+ 逐出定义族（req_kv_boltzmann_factor/
      req_evicted_partition(+_pos)/req_evicted_transition/req_evicted_boltzmann/
      req_db_breaking）+ B1 evicted_l + B2c kept_final + B3a
      lipschitz_scaled + B3b boltzmann_upper + B3c abs_diff_prod_bound +
      B3 boltzmann_diff_bound + B4 bound_eps —— 全建（Section ReqKVQuantWorld）。
   2. 非平凡性分级（红线 5）：真证 = Parts 0/1/2 全部核心件 + Part 3 全部 +
      Part 4 工具族/B1/B2c/B3a/B3b/B3c/B4（req 链 + 接口字段 + UpReqAlgebra
      引擎）；组装 = B3（P1 桥 + distrib + 单调链 + req 重排）；幂等 δ 对偶 =
      alb_markov_kernel 定义族（δ 展开 + rls_kernel_norm_gen 一击）。
   3. 登记表 2（nat 嵌入/argmin list 机器/RealDifferentiable 族/
      Q 逐点乘积界），续建未新增冻结件；新增诚实假设位 2 枚（bridge、
      transition_nonneg Or 形）均已逐位核对（头注登记表 1）。
   4. 中断事故与修复：见头注登记表 4（5 处正向修复，快照链
*)
