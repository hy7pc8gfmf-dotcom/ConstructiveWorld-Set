(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ========================================================================= *)
(* 【ToyR 工程·· 】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 工程 替换落件（原名落件）；落件时头部漏植工程标记，本块由  *)
(*  于  补设：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/。       *)
(* 替换定理清单：req_r_pow_nonneg／req_minus_pos／req_one_minus_kappa_pos    *)
(* ／req_abs_minus_zero／req_gradient_zero_neg_entropy_truth（共 5 条）      *)
(* 非平凡性口径：幂正体归纳内联与序界直造，消除单跳转发；无一行拆分式假非    *)
(* 平凡。                                                                    *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* UpReqCauchy.v *)
(* *)
(* 目的： 梯度下降收敛链的 req 层副本（熵梯度幂衰减）。 *)
(* 主件： req_grad_decay_iter / req_r_pow_dec 幂衰减族与 req_sum_R_le 尾和界。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSLM。 *)
(* 备注： 熵函数、梯度、动力学与步长前提以 Section 变量给出；幂衰减为显式迭代构造。 *)
(* ============================================================ *)

(* UpReqCauchy.v — 签名迁移批 5 · 波 2：Section ConvergenceCauchy 机械平移（43 件 (b)）
   §0.5 ReqNonnegPlain 双参数 Require 换轨依存，节参挂实例、语句零变化；
   纯 term-mode（req_trans 链 + compat 字段桥），零 setoid 改写器依赖；
   Set 层语句（req/lt/le 全 Set 值，零 Prop 泄露；And/Not/Or/ExistsT 用 L66-73 Set 版）。
   ----------------------------------------------------------------
   诚实签名变化登记表（判据 §0.2-3/-4/-5 逐件登记）：
   1. B 类 Variable 全部假设位逐位保留（T2①）：entropy/entropy_gradient/dynamics/eta/
      dynamics_gradient_step/strict_concavity/L/L_pos/gradient_lipschitz/S_max/
      entropy_upper_bound/metric_abs/kappa/kappa_pos/kappa_lt_one/gradient_abs_decay/
      lt_plus_compat_lt_le/lt_plus_compat_le_lt/metric_refl_zero/r_arch_pow/eta_abs_pos/
      log_lt_mono_cc/lim_metric_approx/le_all_eps_zero/mu/mu_pos/strong_concavity/
      entropy_tangent/weak_trich——Id→req 同形换字（Id 换 req，minus 换 req_minus）。
   2. 判据 0.2-5 假设位（Id 证明依存 plain 形、setoid 接口已 eps 化不可导出）：
      - abs_nonneg_plain : forall a, le zero (abs a)
        （setoid abs_nonneg eps 形 @L40553；依存件：req_iterate_step_abs_diff_iter/
        req_iterate_metric_tail_bound/req_grad_bound_aux/req_grad_squeeze_zero——
        Require 依存其 Class 字段（节参挂实例），语句零变化）
      - metric_pos_plain : forall a b, le zero (metric a b)
        （setoid metric_pos eps 形 @L40585；依存件：req_grad_squeeze_zero 完成位——同上换轨）
      - metric_triangle_plain : forall a b c, le (metric a c) (plus (metric a b) (metric b c))
        （setoid metric_triangle eps 形 @L40584；依存件：req_metric_tail_le_sum/
   3. 判据 0.2-4 log 前提化（setoid log 带 lt zero x 前提 @L40570 区）：
      - log_lt_mono_cc Variable 前提位升格：forall a b, lt zero a -> lt zero b ->
        （log_mult 字段见证位逐字匹配要求：字段结论固定 mult_positive 形见证，
        opaque 引理见证不可 conversion——规范形 Fixpoint 见证 delta+iota 可导）。
        以 sigT 封装为结论第一分量（Hp : lt zero (...)），零 witness-in-statement 摩擦。
   4. (d) 冻结 2 件（natle_to_le @L14643 / natle_of_le @L14747，纯 nat Id 机器）：
      跨接口 Require 复用 原件（裸名），零重证——规划书 §3.4 路线；
      req_iterate_cauchy 结论位改 NatLe 形（cauchy_complete 字段 L40591 对接形），
      Id 的 (N <= m)%nat 前提由 natle_to_le 复用件在证内桥接。
   5. §7.7 ConvergenceTheorem 3 助件节内自持（ 对位件，依存前置）：
      req_iterate_step_diff / req_iterate_step_abs_diff / req_gradient_abs_mono
      （Id @L13880/L13929/L13982）——仅依存本节 Variables， 可凭本文件已证明对位。
   6. minus 非接口字段：全节语句以 req_minus（UpReqAlgebra）书写，证内 unfold；
      Id 接口字段 minus_plus_cancel/minus_plus_cancel_r/le_plus_nonneg_r/le_mult_compat_r/
      half_pos/half_twice/abs_minus_sym 依存位 → UpReqAlgebra req_minus_plus_cancel/
      req_minus_plus_cancel_r/req_le_plus_nonneg_r/req_le_mult_compat_r/
      req_half_pos_loc（本节自持，req_two_pos 见证形）/req_half_twice/req_abs_minus_sym。
   ----------------------------------------------------------------
   覆盖核对（req 件名 -> Id 原件 @ 行号；§2 逐件表 43 件 (b)）：
   载体：req_r_pow<-14071 req_sum_R<-14191 req_nat_to_R<-14559（iterate 顶层复用 @1394）
   幂族：req_r_pow_pos<-14085 req_r_pow_nonneg<-14093 req_r_pow_dec<-14100
     req_r_pow_dec_iter<-14438 req_pow_pos_c（规范见证，req_log_pow_cc 配套）
   衰减：req_grad_decay_iter<-14117 req_iterate_step_abs_diff_iter<-14154
     req_gradient_abs_mono<-13982(§7.7) req_iterate_grad_abs_mono<-14674
   求和：req_sum_R_le<-14198 req_sum_R_zero<-14215 req_sum_R_scal_l<-14356
     req_sum_R_mult_r<-14366
   代数：req_mult_one_minus_r<-14228 req_telescoping<-14238 req_mult_swap_mid<-14455
     req_mult_swap_outer<-14464 req_abs_minus_zero<-14732 req_minus_plus_cancel_gap<-14882
     req_dynamics_step_unfold<-14875 req_minus_pos<-15007
   等比：req_geom_sum_closed<-14251 req_one_minus_kappa_pos<-14270
     req_one_minus_pow_le_one<-14279 req_geom_sum_bound<-14290
   度量尾界：req_metric_tail_le_sum<-14319(+1 假设位) req_iterate_metric_tail_bound<-14376
     req_grad_bound_aux<-14473 req_iterate_metric_min_bound<-14499
   柯西/lim 簇（解冻 5 件，接口字段 L40589-40596 实测）：req_iterate_cauchy<-14528
     req_r_arch_pow_log_budget<-14592 req_iterate_cauchy_explicit_N<-14610
     req_iterate_lim_exists<-14653 req_grad_squeeze_zero<-14763(+2 假设位)
     req_dynamics_converges<-14845 req_unique_attractor<-15197
     req_attractor_converges_unique_truth<-15215
   μ-强凹族：req_gradient_step_contraction<-14896 req_gradient_step_abs_contraction<-15016
     req_gradient_iterate_abs_decay<-15045 req_grad_decay_positive_iter<-15064
   驻点族：req_gradient_zero_entropy_max<-15120 req_gradient_zero_neg_entropy_truth<-15142
     req_gradient_zero_unique<-15169
   log 族：req_log_pow_cc<-14567（前提化）
   ---------------------------------------------------------------- *)

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
Require Import UpReqSLM.
From Stdlib Require Import Arith Lia.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid + global
   Instance RealEnhancedReal; Notation passthrough per the world's own UpReqAlign3.v
   precedent). UpReqSLM's premise classes ReqNonnegPlain/ReqLogPlain are likewise
   re-anchored zero-argument in the pool build, so the downstream Context below drops
   the carrier argument per the G09_MiscSmall.v nw10cure convention. *)
Notation R := Real.

(* Pool-build self-held machine (seat_abl19): the frozen nat Id machine
   natle_to_le (Id-generation S04_RealExpLogConv.v:926, not migrated into the
   pool's S01-S15) is inlined here verbatim per the file's own header rule
   "节内自持" — pure nat Id machine, zero interface dependency. *)
Lemma natle_to_le : forall n m, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  unfold NatLe in H.
  destruct (Nat.leb n m) eqn:E.
  - apply (proj1 (Nat.leb_le n m)). exact E.
  - inversion H.
Qed.

(* ============================================================ *)
(* Section UpReqConvergenceCauchy                                *)
(* ============================================================ *)
Section UpReqConvergenceCauchy.

(* A-face adaptation (M43 nw10cure, per UpReqAlign3.v precedent): the argument-bearing
   generation binders Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are
   deleted; the carrier R is bound to the global Real by the file-top Notation above,
   and the class fields resolve through the global instance RealEnhancedReal.
   the argument-bearing generation binders Context {R : Set}
   {RIS : RealInterfaceEnhancedSetoid R}. are deleted; the carrier R is bound to
   the global Real by the file-top Notation above. Zero Obj.magic, zero Prop
   casts, statement faces preserved verbatim. *)

(* ============ A. 诚实接口 Variable（B 类假设位逐位保留 T2①） ============ *)

Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable dynamics_gradient_step : forall x : R,
  req (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable strict_concavity : forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz :
  forall x y : R,
    le (abs (req_minus (entropy_gradient x) (entropy_gradient y)))
       (mult L (abs (req_minus x y))).
Variable S_max : R.
Variable entropy_upper_bound : forall E_A, le (entropy E_A) S_max.

(* metric 由范数诱导（同 Id 节 L14048 同位） *)
Variable metric_abs : forall a b : R, req (metric a b) (abs (req_minus a b)).

(* 梯度绝对值几何衰减（Id L14051-14055 同位） *)
Variable kappa : R.
Variable kappa_pos : lt zero kappa.
Variable kappa_lt_one : lt kappa one.
Variable gradient_abs_decay : forall (E_A : R) (n : nat),
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult kappa (abs (entropy_gradient (iterate dynamics n E_A)))).

(* lt+le 混合加保序（Id L14060-14061 同位） *)
Variable lt_plus_compat_lt_le : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable lt_plus_compat_le_lt : forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).

(* ============ A+. 判据 0.2-5 假设位（reqNonnegPlain 双参数 Require 换轨 + triangle 参数位自持，登记表 2） ============ *)
(* Id 证明依存 plain 形 abs_nonneg/metric_pos/metric_triangle，setoid 接口对应字段
   已 Bishop eps 化（L40553/L40584/L40585），plain 形不可由 eps 形导出（序无消去）。
   （ 原节内自持 Variable 副本已删）→ 节参挂 ReqNonnegPlain 实例依存其字段：
   投影 R/RIS/实例三位全隐式，裸名依存走类型类推断（本地实例 RN），证明体逐位零改动，
   实例位 discharged 为隐式参数（Print Assumptions 仍 Closed，零新增公理面）。
   Variable 先例同构）。 *)
Context {RN : ReqNonnegPlain}.
Variable metric_triangle_plain : forall a b c : R, le (metric a c) (plus (metric a b) (metric b c)).

(* req_half_pos_loc：req_two_pos 见证形（req_half_pos 的见证规范形版本，登记表 6） *)
Lemma req_half_pos_loc : forall a : R, lt zero a ->
  lt zero (mult (inv_pos (plus one one) req_two_pos) a).
Proof.
  intros a Ha.
  apply (mult_positive (inv_pos (plus one one) req_two_pos) a).
  - apply inv_pos_pos.
  - exact Ha.
Qed.

(* ============ B. §7.7 ConvergenceTheorem 3 助件（节内自持， 对位） ============ *)

(* Id iterate_step_diff L13880：x_{n+1} − x_n == η·g(x_n) *)
Lemma req_iterate_step_diff : forall (E_A : R) (n : nat),
  req (req_minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
      (mult eta (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n. induction n as [| n IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - exact (req_trans (plus (dynamics E_A) (opp E_A))
                     (plus (plus E_A (mult eta (entropy_gradient E_A))) (opp E_A))
                     (mult eta (entropy_gradient E_A))
                     (req_plus_compat (dynamics E_A)
                                      (plus E_A (mult eta (entropy_gradient E_A)))
                                      (opp E_A) (opp E_A)
                                      (dynamics_gradient_step E_A) (req_refl (opp E_A)))
                     (req_minus_plus_cancel_r E_A (mult eta (entropy_gradient E_A)))).
  - exact (req_trans (plus (dynamics (iterate dynamics (Datatypes.S n) E_A)) (opp (iterate dynamics (Datatypes.S n) E_A)))
                     (plus (plus (iterate dynamics (Datatypes.S n) E_A)
                                 (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
                           (opp (iterate dynamics (Datatypes.S n) E_A)))
                     (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
                     (req_plus_compat (dynamics (iterate dynamics (Datatypes.S n) E_A))
                                      (plus (iterate dynamics (Datatypes.S n) E_A)
                                            (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))
                                      (opp (iterate dynamics (Datatypes.S n) E_A))
                                      (opp (iterate dynamics (Datatypes.S n) E_A))
                                      (dynamics_gradient_step (iterate dynamics (Datatypes.S n) E_A))
                                      (req_refl (opp (iterate dynamics (Datatypes.S n) E_A))))
                     (req_minus_plus_cancel_r (iterate dynamics (Datatypes.S n) E_A)
                                              (mult eta (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))))).
Qed.

(* Id iterate_step_abs_diff L13929：|x_{n+1} − x_n| == |η|·|g(x_n)| *)
Lemma req_iterate_step_abs_diff : forall (E_A : R) (n : nat),
  req (abs (req_minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A)))
      (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n.
  exact (req_trans (abs (req_minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A)))
                   (abs (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A))))
                   (req_abs_compat (req_minus (iterate dynamics (Datatypes.S n) E_A) (iterate dynamics n E_A))
                                   (mult eta (entropy_gradient (iterate dynamics n E_A)))
                                   (req_iterate_step_diff E_A n))
                   (abs_mult eta (entropy_gradient (iterate dynamics n E_A)))).
Qed.

(* Id gradient_abs_mono L13982：x < y、0 < g(y) < g(x) ⟹ |g(y)| ≤ |g(x)| *)
Lemma req_gradient_abs_mono : forall x y : R,
  lt x y -> lt zero (entropy_gradient y) ->
  lt (entropy_gradient y) (entropy_gradient x) ->
  le (abs (entropy_gradient y)) (abs (entropy_gradient x)).
Proof.
  intros x y Hxy Hgypos Hgygx.
  assert (Hgxpos : lt zero (entropy_gradient x))
    by (apply (lt_trans _ (entropy_gradient y) _); [exact Hgypos | exact Hgygx]).
  assert (Habsy : req (abs (entropy_gradient y)) (entropy_gradient y))
    by exact (abs_pos (entropy_gradient y) Hgypos).
  assert (Habsx : req (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgxpos).
  apply (le_id_l (abs (entropy_gradient y)) (entropy_gradient y) (abs (entropy_gradient x)) Habsy).
  apply (le_id_r (entropy_gradient y) (entropy_gradient x) (abs (entropy_gradient x))
                 (req_sym _ _ Habsx)
                 (lt_le_iff _ _ (inl Hgygx))).
Qed.

(* ============ C. R 层幂载体（Id L14071 同构） ============ *)

Fixpoint req_r_pow (x : R) (n : nat) : R :=
  match n with
  | 0%nat => one
  | Datatypes.S m => mult x (req_r_pow x m)
  end.

Variable metric_refl_zero : forall a : R, req (metric a a) zero.

(* 几何击穿（Id L14082 同位；req_r_pow 载体形） *)
Variable r_arch_pow : forall (a : R), lt zero a -> forall eps : R, lt zero eps ->
  sigT (fun n : nat => lt (mult a (req_r_pow kappa n)) eps).

(* Id r_pow_pos L14085 *)
Lemma req_r_pow_pos : forall x n, lt zero x -> lt zero (req_r_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - exact one_pos.
  - apply (mult_positive x (req_r_pow x m) Hx IH).
Qed.

(* 规范 Fixpoint 正性见证（req_log_pow_cc 的 log_mult 字段见证位配套，登记表 3） *)
Fixpoint req_pow_pos_c (x : R) (Hx : lt zero x) (n : nat) : lt zero (req_r_pow x n) :=
  match n with
  | 0%nat => one_pos
  | Datatypes.S m => mult_positive x (req_r_pow x m) Hx (req_pow_pos_c x Hx m)
  end.

(* Id r_pow_nonneg L14093 *)
Lemma req_r_pow_nonneg : forall x n, lt zero x -> le zero (req_r_pow x n).
Proof.
  intros x n Hx.
  assert (Hpos : lt zero (req_r_pow x n)).
  { induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
    - exact one_pos.
    - exact (mult_positive x (req_r_pow x m) Hx IH). }
  exact (lt_le_iff zero (req_r_pow x n) (inl Hpos)).
Qed.

(* Id r_pow_dec L14100：0 < b < 1 ⟹ b^{S n} ≤ b^n *)
Lemma req_r_pow_dec : forall b n, lt zero b -> lt b one ->
  le (req_r_pow b (Datatypes.S n)) (req_r_pow b n).
Proof.
  intros b n Hb Hblt.
  induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply (le_id_l _ b _).
    + apply (mult_one b).
    + apply (lt_le_iff _ _ (inl Hblt)).
  - apply (le_id_l _ (mult (req_r_pow b (Datatypes.S m)) b) _).
    + apply (mult_comm b (req_r_pow b (Datatypes.S m))).
    + apply (le_id_r _ (mult (req_r_pow b m) b) _).
      * apply (mult_comm (req_r_pow b m) b).
      * apply (le_mult_compat (req_r_pow b (Datatypes.S m)) (req_r_pow b m) b Hb).
        exact IH.
Qed.

(* ============ D. 梯度绝对值几何衰减迭代（Id L14117） ============ *)

Lemma req_grad_decay_iter : forall (E_A : R) (n k : nat),
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (req_r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + exact (req_trans _ _ _
               (req_sym _ _ (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
               (req_sym _ _ (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - apply (le_trans _ (mult kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + rewrite (Nat.add_succ_r n k).
      apply (le_id_l _ (abs (entropy_gradient (iterate dynamics (Datatypes.S (n + k)) E_A))) _).
      * apply req_refl.
      * exact (gradient_abs_decay E_A (n + k)).
    + apply (le_trans _ (mult kappa (mult (req_r_pow kappa k)
                                          (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + k) E_A))) kappa) _).
        -- apply (mult_comm kappa (abs (entropy_gradient (iterate dynamics (n + k) E_A)))).
        -- apply (le_id_r _ (mult (mult (req_r_pow kappa k)
                                        (abs (entropy_gradient (iterate dynamics n E_A)))) kappa) _).
           ++ apply (mult_comm (mult (req_r_pow kappa k)
                                     (abs (entropy_gradient (iterate dynamics n E_A)))) kappa).
           ++ apply (le_mult_compat (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                    (mult (req_r_pow kappa k)
                                          (abs (entropy_gradient (iterate dynamics n E_A))))
                                    kappa kappa_pos).
              exact IH.
      * apply (le_id_r _ (mult kappa (mult (req_r_pow kappa k)
                                           (abs (entropy_gradient (iterate dynamics n E_A))))) _).
        -- apply (mult_assoc kappa (req_r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A)))).
        -- apply le_refl.
Qed.

(* ============ E. 多步步长收缩（Id L14154） ============ *)

Lemma req_iterate_step_abs_diff_iter : forall (E_A : R) (n k : nat),
  le (abs (req_minus (iterate dynamics (n + Datatypes.S k) E_A)
                     (iterate dynamics (n + k) E_A)))
     (mult (abs eta) (mult (req_r_pow kappa k) (abs (entropy_gradient (iterate dynamics n E_A))))).
Proof.
  intros E_A n k.
  induction k as [| k IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - rewrite (Nat.add_1_r n). rewrite (Nat.add_0_r n).
    apply (le_id_l _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
    + exact (req_iterate_step_abs_diff E_A n).
    + apply (le_id_r _ (mult (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))) _).
      * exact (req_mult_compat (abs eta) (abs eta) (abs (entropy_gradient (iterate dynamics n E_A)))
                               (mult one (abs (entropy_gradient (iterate dynamics n E_A))))
                               (req_refl (abs eta))
                               (req_sym _ _
                                 (req_trans (mult one (abs (entropy_gradient (iterate dynamics n E_A))))
                                            (mult (abs (entropy_gradient (iterate dynamics n E_A))) one)
                                            (abs (entropy_gradient (iterate dynamics n E_A)))
                                            (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A))))
                                            (mult_one (abs (entropy_gradient (iterate dynamics n E_A))))))).
      * apply le_refl.
  - apply (le_trans _ (mult (abs eta)
                            (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
    + rewrite (Nat.add_succ_r n (Datatypes.S k)).
      apply (le_id_l _ (mult (abs eta)
                             (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))) _).
      * exact (req_iterate_step_abs_diff E_A (n + Datatypes.S k)).
      * apply le_refl.
    + apply (le_id_l _ (mult (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A))) (abs eta)) _).
      * apply (mult_comm (abs eta) (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))).
      * apply (le_id_r _ (mult (mult (req_r_pow kappa (Datatypes.S k))
                                     (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)) _).
        -- apply (mult_comm (mult (req_r_pow kappa (Datatypes.S k))
                                  (abs (entropy_gradient (iterate dynamics n E_A)))) (abs eta)).
        -- apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics (n + Datatypes.S k) E_A)))
                                      (mult (req_r_pow kappa (Datatypes.S k))
                                            (abs (entropy_gradient (iterate dynamics n E_A))))
                                      (abs eta) (abs_nonneg_plain eta)).
           apply (req_grad_decay_iter E_A n (Datatypes.S k)).
Qed.

(* ============ F. R 层有限和载体 + 求和机器（Id L14191-14226） ============ *)

Fixpoint req_sum_R (f : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => zero
  | Datatypes.S m => plus (req_sum_R f m) (f m)
  end.

(* Id sum_R_le L14198 *)
Lemma req_sum_R_le : forall f g n,
  (forall k, (k < n)%nat -> le (f k) (g k)) ->
  le (req_sum_R f n) (req_sum_R g n).
Proof.
  intros f g n H.
  induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply le_refl.
  - apply (le_trans (plus (req_sum_R f m) (f m)) (plus (req_sum_R g m) (f m)) (plus (req_sum_R g m) (g m))).
    + apply (le_plus_compat (req_sum_R f m) (req_sum_R g m) (f m) (f m)).
      * apply IH. intros k Hk. apply (H k). lia.
      * apply le_refl.
    + apply (le_plus_compat (req_sum_R g m) (req_sum_R g m) (f m) (g m)).
      * apply le_refl.
      * apply (H m (Nat.lt_succ_diag_r m)).
Qed.

(* Id sum_R_zero L14215 *)
Lemma req_sum_R_zero : forall f n,
  (forall k, (k < n)%nat -> req (f k) zero) ->
  req (req_sum_R f n) zero.
Proof.
  intros f n H.
  induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - apply req_refl.
  - exact (req_trans (plus (req_sum_R f m) (f m)) (plus zero zero) zero
                     (req_plus_compat (req_sum_R f m) zero (f m) zero
                                      (IH (fun k Hk => H k (Nat.lt_trans k m (Datatypes.S m) Hk (Nat.lt_succ_diag_r m))))
                                      (H m (Nat.lt_succ_diag_r m)))
                     (plus_zero zero)).
Qed.

(* ============ G. 代数辅件（Id L14228-14249） ============ *)

(* Id mult_one_minus_r L14228：mult (1−x)·y == y + (−x)·y *)
Lemma req_mult_one_minus_r : forall x y : R,
  req (mult (req_minus one x) y) (plus y (mult (opp x) y)).
Proof.
  intros x y.
  exact (req_trans (mult (plus one (opp x)) y)
                   (plus (mult one y) (mult (opp x) y))
                   (plus y (mult (opp x) y))
                   (req_mult_plus_distr_r one (opp x) y)
                   (req_plus_compat (mult one y) y (mult (opp x) y) (mult (opp x) y)
                                    (req_trans (mult one y) (mult y one) y
                                               (mult_comm one y) (mult_one y))
                                    (req_refl (mult (opp x) y)))).
Qed.

(* Id telescoping L14238：1−A + A−B == 1−B *)
Lemma req_telescoping : forall a b : R,
  req (plus (req_minus one a) (req_minus a b)) (req_minus one b).
Proof.
  intros a b.
  apply (req_trans (plus (plus one (opp a)) (plus a (opp b)))
                   (plus one (plus (opp a) (plus a (opp b))))
                   (plus one (opp b))
                   (req_sym _ _ (plus_assoc one (opp a) (plus a (opp b))))
                   (req_plus_compat one one (plus (opp a) (plus a (opp b))) (opp b)
                                    (req_refl one)
                                    (req_trans (plus (opp a) (plus a (opp b)))
                                               (plus (plus (opp a) a) (opp b))
                                               (opp b)
                                               (plus_assoc (opp a) a (opp b))
                                               (req_trans (plus (plus (opp a) a) (opp b))
                                                          (plus zero (opp b))
                                                          (opp b)
                                                          (req_plus_compat (plus (opp a) a) zero (opp b) (opp b)
                                                                           (req_trans (plus (opp a) a)
                                                                                      (plus a (opp a))
                                                                                      zero
                                                                                      (plus_comm (opp a) a)
                                                                                      (plus_opp a))
                                                                           (req_refl (opp b)))
                                                          (req_trans (plus zero (opp b))
                                                                     (plus (opp b) zero)
                                                                     (opp b)
                                                                     (plus_comm zero (opp b))
                                                                     (plus_zero (opp b))))))).
Qed.

(* ============ H. 几何级数机器（Id L14251-14317） ============ *)

(* Id geom_sum_closed L14251：(1−κ)·Σ_{k<m} κ^k == 1−κ^m *)
Lemma req_geom_sum_closed : forall m : nat,
  req (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m))
      (req_minus one (req_r_pow kappa m)).
Proof.
  intro m.
  induction m as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - exact (req_trans (mult (req_minus one kappa) zero) zero (req_minus one one)
                     (mult_zero (req_minus one kappa))
                     (req_sym _ _ (req_minus_self_zero one one (req_refl one)))).
  - apply (req_trans _ (plus (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m))
                             (mult (req_minus one kappa) (req_r_pow kappa m))) _
            (distrib (req_minus one kappa) (req_sum_R (req_r_pow kappa) m) (req_r_pow kappa m))).
    apply (req_trans _ (plus (req_minus one (req_r_pow kappa m))
                             (mult (req_minus one kappa) (req_r_pow kappa m))) _
            (req_plus_compat (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m))
                             (req_minus one (req_r_pow kappa m))
                             (mult (req_minus one kappa) (req_r_pow kappa m))
                             (mult (req_minus one kappa) (req_r_pow kappa m))
                             IH (req_refl (mult (req_minus one kappa) (req_r_pow kappa m))))).
    apply (req_trans _ (plus (req_minus one (req_r_pow kappa m))
                             (plus (req_r_pow kappa m) (mult (opp kappa) (req_r_pow kappa m)))) _
            (req_plus_compat (req_minus one (req_r_pow kappa m))
                             (req_minus one (req_r_pow kappa m))
                             (mult (req_minus one kappa) (req_r_pow kappa m))
                             (plus (req_r_pow kappa m) (mult (opp kappa) (req_r_pow kappa m)))
                             (req_refl (req_minus one (req_r_pow kappa m)))
                             (req_mult_one_minus_r kappa (req_r_pow kappa m)))).
    apply (req_trans _ (plus (req_minus one (req_r_pow kappa m))
                             (plus (req_r_pow kappa m) (opp (mult kappa (req_r_pow kappa m))))) _
            (req_plus_compat (req_minus one (req_r_pow kappa m))
                             (req_minus one (req_r_pow kappa m))
                             (plus (req_r_pow kappa m) (mult (opp kappa) (req_r_pow kappa m)))
                             (plus (req_r_pow kappa m) (opp (mult kappa (req_r_pow kappa m))))
                             (req_refl (req_minus one (req_r_pow kappa m)))
                             (req_plus_compat (req_r_pow kappa m) (req_r_pow kappa m)
                                              (mult (opp kappa) (req_r_pow kappa m))
                                              (opp (mult kappa (req_r_pow kappa m)))
                                              (req_refl (req_r_pow kappa m))
                                              (req_opp_mult_r kappa (req_r_pow kappa m))))).
    exact (req_telescoping (req_r_pow kappa m) (mult kappa (req_r_pow kappa m))).
Qed.

(* Id one_minus_kappa_pos L14270：0 < 1−κ *)
Lemma req_one_minus_kappa_pos : lt zero (req_minus one kappa).
Proof.
  unfold req_minus.
  exact (lt_id_l zero (plus kappa (opp kappa)) (plus one (opp kappa))
           (req_sym (plus kappa (opp kappa)) zero (plus_opp kappa))
           (lt_plus_compat_lt_le kappa one (opp kappa) (opp kappa) kappa_lt_one
              (le_refl (opp kappa)))).
Qed.

(* Id one_minus_pow_le_one L14279：1−κ^m ≤ 1 *)
Lemma req_one_minus_pow_le_one : forall m, le (req_minus one (req_r_pow kappa m)) one.
Proof.
  intro m.
  apply (le_id_r _ (plus (req_minus one (req_r_pow kappa m)) (req_r_pow kappa m)) _).
  - exact (req_trans (plus (req_minus one (req_r_pow kappa m)) (req_r_pow kappa m))
                     (plus (req_r_pow kappa m) (req_minus one (req_r_pow kappa m)))
                     one
                     (plus_comm (req_minus one (req_r_pow kappa m)) (req_r_pow kappa m))
                     (req_minus_plus_cancel (req_r_pow kappa m) one)).
  - apply (req_le_plus_nonneg_r (req_minus one (req_r_pow kappa m)) (req_r_pow kappa m)).
    apply (req_r_pow_nonneg kappa m kappa_pos).
Qed.

(* Id geom_sum_bound L14290：Σ_{k<m} κ^k ≤ 1/(1−κ) *)
Lemma req_geom_sum_bound : forall m,
  le (req_sum_R (req_r_pow kappa) m) (inv_pos (req_minus one kappa) req_one_minus_kappa_pos).
Proof.
  intro m.
  set (I := inv_pos (req_minus one kappa) req_one_minus_kappa_pos).
  apply (le_id_r _ (mult one I) _).
  - exact (req_trans (mult one I) (mult I one) I
                     (mult_comm one I) (mult_one I)).
  - apply (le_id_l _ (mult (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m)) I) _).
    + exact (req_trans (req_sum_R (req_r_pow kappa) m)
                       (mult (req_sum_R (req_r_pow kappa) m) one)
                       (mult (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m)) I)
                       (req_sym _ _ (mult_one (req_sum_R (req_r_pow kappa) m)))
                       (req_trans (mult (req_sum_R (req_r_pow kappa) m) one)
                                  (mult (req_sum_R (req_r_pow kappa) m) (mult (req_minus one kappa) I))
                                  (mult (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m)) I)
                                  (req_mult_compat (req_sum_R (req_r_pow kappa) m)
                                                   (req_sum_R (req_r_pow kappa) m)
                                                   one
                                                   (mult (req_minus one kappa) I)
                                                   (req_refl (req_sum_R (req_r_pow kappa) m))
                                                   (req_sym _ _ (inv_pos_correct (req_minus one kappa) req_one_minus_kappa_pos)))
                                  (req_trans (mult (req_sum_R (req_r_pow kappa) m) (mult (req_minus one kappa) I))
                                             (mult (mult (req_sum_R (req_r_pow kappa) m) (req_minus one kappa)) I)
                                             (mult (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m)) I)
                                             (mult_assoc (req_sum_R (req_r_pow kappa) m) (req_minus one kappa) I)
                                             (req_mult_compat (mult (req_sum_R (req_r_pow kappa) m) (req_minus one kappa))
                                                              (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m))
                                                              I I
                                                              (mult_comm (req_sum_R (req_r_pow kappa) m) (req_minus one kappa))
                                                              (req_refl I))))).
    + apply (le_mult_compat_weak (mult (req_minus one kappa) (req_sum_R (req_r_pow kappa) m)) one I).
      * apply (lt_le_iff _ _ (inl (inv_pos_pos (req_minus one kappa) req_one_minus_kappa_pos))).
      * apply (le_id_l _ (req_minus one (req_r_pow kappa m)) _).
        -- exact (req_geom_sum_closed m).
        -- apply (req_one_minus_pow_le_one m).
Qed.

(* ============ I. metric 尾界（Id L14319-14436；+1 假设位 metric_triangle_plain） ============ *)

(* Id metric_tail_le_sum L14319：metric 三角迭代到和。
   签名差异登记（登记表 2）：setoid metric_triangle 为 eps 形（L40584），Id 证明依存 plain 形
   不可导出（序无消去）→ 新增假设位 metric_triangle_plain，语句与 Id 原件逐字同形。 *)
Lemma req_metric_tail_le_sum : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (req_sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                 (iterate dynamics (n + k) E_A)) m).
Proof.
  intros E_A n m.
  induction m as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - rewrite (Nat.add_0_r n).
    apply (le_id_l _ zero _ (metric_refl_zero (iterate dynamics n E_A)) (le_refl zero)).
  - rewrite (Nat.add_succ_r n m).
    apply (le_trans _ (plus (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))) _).
    + apply (le_id_r _ (plus (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                     (iterate dynamics (n + m) E_A))
                             (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))) _).
      * apply (plus_comm (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                 (iterate dynamics (n + m) E_A))
                         (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))).
      * apply (metric_triangle_plain (iterate dynamics (Datatypes.S (n + m)) E_A)
                                     (iterate dynamics (n + m) E_A)
                                     (iterate dynamics n E_A)).
    + apply (le_plus_compat (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
                            (req_sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                                        (iterate dynamics (n + k) E_A)) m)
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))
                            (metric (iterate dynamics (Datatypes.S (n + m)) E_A)
                                    (iterate dynamics (n + m) E_A))).
      * exact IH.
      * apply le_refl.
Qed.

(* Id sum_R_scal_l L14356 *)
Lemma req_sum_R_scal_l : forall a f n,
  req (req_sum_R (fun k => mult a (f k)) n) (mult a (req_sum_R f n)).
Proof.
  intros a f n.
  induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - exact (req_sym _ _ (mult_zero a)).
  - exact (req_trans (plus (req_sum_R (fun k => mult a (f k)) m) (mult a (f m)))
                     (plus (mult a (req_sum_R f m)) (mult a (f m)))
                     (mult a (plus (req_sum_R f m) (f m)))
                     (req_plus_compat (req_sum_R (fun k => mult a (f k)) m)
                                      (mult a (req_sum_R f m))
                                      (mult a (f m)) (mult a (f m))
                                      IH (req_refl (mult a (f m))))
                     (req_sym _ _ (distrib a (req_sum_R f m) (f m)))).
Qed.

(* Id sum_R_mult_r L14366 *)
Lemma req_sum_R_mult_r : forall f b n,
  req (req_sum_R (fun k => mult (f k) b) n) (mult (req_sum_R f n) b).
Proof.
  intros f b n.
  induction n as [| m IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - exact (req_sym _ _ (req_trans (mult zero b) (mult b zero) zero
                                  (mult_comm zero b) (mult_zero b))).
  - exact (req_trans (plus (req_sum_R (fun k => mult (f k) b) m) (mult (f m) b))
                     (plus (mult (req_sum_R f m) b) (mult (f m) b))
                     (mult (plus (req_sum_R f m) (f m)) b)
                     (req_plus_compat (req_sum_R (fun k => mult (f k) b) m)
                                      (mult (req_sum_R f m) b)
                                      (mult (f m) b) (mult (f m) b)
                                      IH (req_refl (mult (f m) b)))
                     (req_sym _ _ (req_mult_plus_distr_r (req_sum_R f m) (f m) b))).
Qed.

(* Id iterate_metric_tail_bound L14376：尾部收缩（plain abs_nonneg 依存位 ×2，登记表 2） *)
Lemma req_iterate_metric_tail_bound : forall (E_A : R) (n m : nat),
  le (metric (iterate dynamics (n + m) E_A) (iterate dynamics n E_A))
     (mult (abs eta)
           (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                 (inv_pos (req_minus one kappa) req_one_minus_kappa_pos))).
Proof.
  intros E_A n m.
  apply (le_trans _ (req_sum_R (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                              (iterate dynamics (n + k) E_A)) m) _).
  - apply (req_metric_tail_le_sum E_A n m).
  - apply (le_trans _ (req_sum_R (fun k => mult (abs eta)
                                                (mult (req_r_pow kappa k)
                                                      (abs (entropy_gradient (iterate dynamics n E_A))))) m) _).
    + apply (req_sum_R_le (fun k => metric (iterate dynamics (n + Datatypes.S k) E_A)
                                           (iterate dynamics (n + k) E_A))
                          (fun k => mult (abs eta)
                                         (mult (req_r_pow kappa k)
                                               (abs (entropy_gradient (iterate dynamics n E_A))))) m).
      intros k Hk.
      apply (le_id_l _ (abs (req_minus (iterate dynamics (n + Datatypes.S k) E_A)
                                       (iterate dynamics (n + k) E_A))) _).
      * apply (metric_abs (iterate dynamics (n + Datatypes.S k) E_A)
                          (iterate dynamics (n + k) E_A)).
      * apply (req_iterate_step_abs_diff_iter E_A n k).
    + apply (le_id_l _ (mult (abs eta)
                             (mult (req_sum_R (req_r_pow kappa) m)
                                   (abs (entropy_gradient (iterate dynamics n E_A))))) _).
      * exact (req_trans (req_sum_R (fun k => mult (abs eta)
                                                   (mult (req_r_pow kappa k)
                                                         (abs (entropy_gradient (iterate dynamics n E_A))))) m)
                         (mult (abs eta) (req_sum_R (fun k => mult (req_r_pow kappa k)
                                                                   (abs (entropy_gradient (iterate dynamics n E_A)))) m))
                         (mult (abs eta)
                               (mult (req_sum_R (req_r_pow kappa) m)
                                     (abs (entropy_gradient (iterate dynamics n E_A)))))
                         (req_sum_R_scal_l (abs eta)
                                           (fun k => mult (req_r_pow kappa k)
                                                          (abs (entropy_gradient (iterate dynamics n E_A)))) m)
                         (req_mult_compat (abs eta) (abs eta)
                                          (req_sum_R (fun k => mult (req_r_pow kappa k)
                                                                    (abs (entropy_gradient (iterate dynamics n E_A)))) m)
                                          (mult (req_sum_R (req_r_pow kappa) m)
                                                (abs (entropy_gradient (iterate dynamics n E_A))))
                                          (req_refl (abs eta))
                                          (req_sum_R_mult_r (req_r_pow kappa)
                                                            (abs (entropy_gradient (iterate dynamics n E_A))) m))).
      * apply (req_le_mult_compat_r (abs eta)
                                    (mult (req_sum_R (req_r_pow kappa) m)
                                          (abs (entropy_gradient (iterate dynamics n E_A))))
                                    (mult (abs (entropy_gradient (iterate dynamics n E_A)))
                                          (inv_pos (req_minus one kappa) req_one_minus_kappa_pos))).
        -- apply (abs_nonneg_plain eta).
        -- apply (le_id_r _ (mult (inv_pos (req_minus one kappa) req_one_minus_kappa_pos)
                                  (abs (entropy_gradient (iterate dynamics n E_A)))) _).
           ++ apply (mult_comm (inv_pos (req_minus one kappa) req_one_minus_kappa_pos)
                               (abs (entropy_gradient (iterate dynamics n E_A)))).
           ++ apply (le_mult_compat_weak (req_sum_R (req_r_pow kappa) m)
                                         (inv_pos (req_minus one kappa) req_one_minus_kappa_pos)
                                         (abs (entropy_gradient (iterate dynamics n E_A)))
                                         (abs_nonneg_plain (entropy_gradient (iterate dynamics n E_A)))).
              ** apply (req_geom_sum_bound m).
Qed.

(* ============ J. 幂递减 + 乘法交换 + 梯度界（Id L14398-14497） ============ *)

(* 非零步长（Id L14398 同位） *)
Variable eta_abs_pos : lt zero (abs eta).

(* 1/(1−κ)（Id L14401 同位） *)
Let S := inv_pos (req_minus one kappa) req_one_minus_kappa_pos.

(* Id r_pow_dec_iter L14438：m ≤ n ⟹ κ^n ≤ κ^m *)
Lemma req_r_pow_dec_iter : forall m n, (m <= n)%nat -> le (req_r_pow kappa n) (req_r_pow kappa m).
Proof.
  intros m n Hmn.
  revert m Hmn.
  induction n as [| n IH]; intros m Hmn.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply le_refl.
  - destruct (Nat.leb m n) eqn:Emn.
    + apply (le_trans _ (req_r_pow kappa n) _);
        [apply (req_r_pow_dec kappa n kappa_pos kappa_lt_one) | apply (IH m (proj1 (Nat.leb_le m n) Emn))].
    + apply Nat.leb_gt in Emn.
      assert (Hm : m = Datatypes.S n) by lia. subst m. apply le_refl.
Qed.

(* Id mult_swap_mid L14455 *)
Lemma req_mult_swap_mid : forall a b c : R, req (mult (mult a b) c) (mult (mult a c) b).
Proof.
  intros a b c.
  exact (req_trans (mult (mult a b) c)
                   (mult a (mult b c))
                   (mult (mult a c) b)
                   (req_sym _ _ (mult_assoc a b c))
                   (req_trans (mult a (mult b c)) (mult a (mult c b)) (mult (mult a c) b)
                              (req_mult_compat a a (mult b c) (mult c b)
                                              (req_refl a) (mult_comm b c))
                              (mult_assoc a c b))).
Qed.

(* Id mult_swap_outer L14464 *)
Lemma req_mult_swap_outer : forall a b c d : R,
  req (mult (mult (mult a b) c) d) (mult (mult (mult a c) d) b).
Proof.
  intros a b c d.
  exact (req_trans (mult (mult (mult a b) c) d)
                   (mult (mult (mult a c) b) d)
                   (mult (mult (mult a c) d) b)
                   (req_mult_compat (mult (mult a b) c) (mult (mult a c) b) d d
                                    (req_mult_swap_mid a b c) (req_refl d))
                   (req_mult_swap_mid (mult a c) b d)).
Qed.

(* Id grad_bound_aux L14473（plain abs_nonneg 依存位，登记表 2） *)
Lemma req_grad_bound_aux : forall E_A n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (req_r_pow kappa n)).
Proof.
  intros E_A n Hg0pos.
  apply (le_id_r _ (mult (abs eta) (mult (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)) _).
  - exact (req_trans (mult (abs eta) (mult (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S))
                     (mult (mult (abs eta) (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))) S)
                     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S) (req_r_pow kappa n))
                     (mult_assoc (abs eta) (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                     (req_trans (mult (mult (abs eta) (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))) S)
                                (mult (mult (mult (abs eta) (req_r_pow kappa n)) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                                (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S) (req_r_pow kappa n))
                                (req_mult_compat (mult (abs eta) (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))))
                                                 (mult (mult (abs eta) (req_r_pow kappa n)) (abs (entropy_gradient (iterate dynamics 0 E_A))))
                                                 S S
                                                 (mult_assoc (abs eta) (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))
                                                 (req_refl S))
                                (req_mult_swap_outer (abs eta) (req_r_pow kappa n)
                                                     (abs (entropy_gradient (iterate dynamics 0 E_A))) S))).
  - apply (req_le_mult_compat_r (abs eta)
                                (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)
                                (mult (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)).
    + apply (abs_nonneg_plain eta).
    + apply (le_mult_compat_weak (abs (entropy_gradient (iterate dynamics n E_A)))
                                 (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A))))
                                 S).
      * apply (lt_le_iff _ _ (inl (inv_pos_pos (req_minus one kappa) req_one_minus_kappa_pos))).
      * apply (req_grad_decay_iter E_A 0 n).
Qed.

(* Id iterate_metric_min_bound L14499 *)
Lemma req_iterate_metric_min_bound : forall E_A m n,
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  le (metric (iterate dynamics m E_A) (iterate dynamics n E_A))
     (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
           (req_r_pow kappa (Nat.min m n))).
Proof.
  intros E_A m n Hg0pos.
  destruct (Nat.leb m n) eqn:Emn.
  - apply Nat.leb_le in Emn.
    apply (le_id_l _ (metric (iterate dynamics n E_A) (iterate dynamics m E_A)) _).
    { exact (metric_sym (iterate dynamics m E_A) (iterate dynamics n E_A)). }
    rewrite (Nat.min_l m n Emn).
    rewrite <- (Nat.sub_add m n Emn).
    rewrite (Nat.add_comm (n - m) m).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics m E_A))) S)) _).
    + apply (req_iterate_metric_tail_bound E_A m (n - m)).
    + apply (req_grad_bound_aux E_A m Hg0pos).
  - apply Nat.leb_gt in Emn.
    rewrite (Nat.min_r m n (Nat.lt_le_incl n m Emn)).
    rewrite <- (Nat.sub_add n m (Nat.lt_le_incl n m Emn)).
    rewrite (Nat.add_comm (m - n) n).
    apply (le_trans _ (mult (abs eta) (mult (abs (entropy_gradient (iterate dynamics n E_A))) S)) _).
    + apply (req_iterate_metric_tail_bound E_A n (m - n)).
    + apply (req_grad_bound_aux E_A n Hg0pos).
Qed.

(* ============ K. 柯西性（Id L14528-14564；结论位 NatLe 形对接 cauchy_complete，登记表 4） ============ *)

Lemma req_iterate_cauchy : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (req_minus one kappa) req_one_minus_kappa_pos). }
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  intros m n Hm Hn.
  apply (le_lt_trans _ (mult a (req_r_pow kappa (Nat.min m n))) _).
  - unfold a.
    apply (req_iterate_metric_min_bound E_A m n Hg0pos).
  - apply (le_lt_trans _ (mult a (req_r_pow kappa N0)) _).
    + apply (req_le_mult_compat_r a (req_r_pow kappa (Nat.min m n)) (req_r_pow kappa N0)).
      * apply (lt_le_iff _ _ (inl Ha)).
      * assert (Hmle : (N0 <= m)%nat) by exact (natle_to_le N0 m Hm).
        assert (Hnle : (N0 <= n)%nat) by exact (natle_to_le N0 n Hn).
        apply (req_r_pow_dec_iter N0 (Nat.min m n)). lia.
    + exact HN0.
Qed.

(* ============ L. log 族（Id L14565-14641；log 前提化，登记表 3） ============ *)

Variable log_lt_mono_cc : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (log a Ha) (log b Hb).

(* nat 到 R 嵌入载体（Id L14559 同构；reqd_nat_to_R 先例） *)
Fixpoint req_nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (req_nat_to_R n')
  end.


Lemma req_log_pow_cc : forall (x : R) (n : nat) (Hx : lt zero x),
  req (log (req_r_pow x n) (req_pow_pos_c x Hx n)) (mult (req_nat_to_R n) (log x Hx)).
Proof.
  intros x n Hx.
  induction n as [| n IH].
  - exact (req_trans (log one (req_pow_pos_c x Hx 0)) zero (mult (req_nat_to_R 0) (log x Hx))
                     (log_one (req_pow_pos_c x Hx 0))
                     (req_sym _ _
                       (req_trans (mult zero (log x Hx)) (mult (log x Hx) zero) zero
                                  (mult_comm zero (log x Hx))
                                  (mult_zero (log x Hx))))).
  - cbn [req_r_pow].
    apply (req_trans (log (mult x (req_r_pow x n)) (req_pow_pos_c x Hx (Datatypes.S n)))
                     (plus (log x Hx) (log (req_r_pow x n) (req_pow_pos_c x Hx n)))
                     (mult (plus one (req_nat_to_R n)) (log x Hx))
                     (log_mult x (req_r_pow x n) Hx (req_pow_pos_c x Hx n))
                     (req_trans (plus (log x Hx) (log (req_r_pow x n) (req_pow_pos_c x Hx n)))
                                (plus (log x Hx) (mult (req_nat_to_R n) (log x Hx)))
                                (mult (plus one (req_nat_to_R n)) (log x Hx))
                                (req_plus_compat (log x Hx) (log x Hx)
                                                 (log (req_r_pow x n) (req_pow_pos_c x Hx n))
                                                 (mult (req_nat_to_R n) (log x Hx))
                                                 (req_refl (log x Hx)) IH)
                                (req_sym _ _
                                  (req_trans (mult (plus one (req_nat_to_R n)) (log x Hx))
                                             (mult (log x Hx) (plus one (req_nat_to_R n)))
                                             (plus (log x Hx) (mult (req_nat_to_R n) (log x Hx)))
                                             (mult_comm (plus one (req_nat_to_R n)) (log x Hx))
                                             (req_trans (mult (log x Hx) (plus one (req_nat_to_R n)))
                                                        (plus (mult (log x Hx) one) (mult (log x Hx) (req_nat_to_R n)))
                                                        (plus (log x Hx) (mult (req_nat_to_R n) (log x Hx)))
                                                        (distrib (log x Hx) one (req_nat_to_R n))
                                                        (req_plus_compat (mult (log x Hx) one) (log x Hx)
                                                                         (mult (log x Hx) (req_nat_to_R n))
                                                                         (mult (req_nat_to_R n) (log x Hx))
                                                                         (mult_one (log x Hx))
                                                                         (mult_comm (log x Hx) (req_nat_to_R n)))))))).
Qed.


Lemma req_r_arch_pow_log_budget : forall a : R, lt zero a -> forall (eps : R) (Hep : lt zero eps),
  sigT (fun N : nat =>
    sigT (fun Hp : lt zero (mult a (req_r_pow kappa N)) =>
      And (le (log (mult a (req_r_pow kappa N)) Hp) (log eps Hep))
          (lt (mult a (req_r_pow kappa N)) eps))).
Proof.
  intros a Ha eps Hep.
  destruct (r_arch_pow a Ha eps Hep) as [N0 HN0].
  exists N0.
  exists (mult_positive a (req_r_pow kappa N0) Ha (req_r_pow_pos kappa N0 kappa_pos)).
  split.
  - apply (lt_le_iff _ _ (inl (log_lt_mono_cc (mult a (req_r_pow kappa N0)) eps
                                              (mult_positive a (req_r_pow kappa N0) Ha (req_r_pow_pos kappa N0 kappa_pos))
                                              Hep
                                              HN0))).
  - exact HN0.
Qed.

(* Id iterate_cauchy_explicit_N L14610：显式可计算收敛率主定理（Hp 见证 sigT 封装，登记表 3） *)
Theorem req_iterate_cauchy_explicit_N : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  forall (eps : R) (Hep : lt zero eps),
    sigT (fun N : nat =>
      sigT (fun Hp : lt zero (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                                   (req_r_pow kappa N)) =>
        And (le (log (mult (mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S)
                            (req_r_pow kappa N))
                     Hp)
                (log eps Hep))
            (forall m n : nat, NatLe N m -> NatLe N n ->
              lt (metric (iterate dynamics m E_A) (iterate dynamics n E_A)) eps))).
Proof.
  intros E_A Hg0pos eps Hep.
  set (a := mult (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
  assert (Ha : lt zero a).
  { unfold a.
    apply (mult_positive (mult (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A)))) S).
    - apply (mult_positive (abs eta) (abs (entropy_gradient (iterate dynamics 0 E_A))) eta_abs_pos Hg0pos).
    - exact (inv_pos_pos (req_minus one kappa) req_one_minus_kappa_pos). }
  destruct (req_r_arch_pow_log_budget a Ha eps Hep) as [N [Hp [HNlog HNgeo]]].
  exists N.
  exists Hp.
  split.
  - unfold a in HNlog. exact HNlog.
  - intros m n Hm Hn.
    apply (le_lt_trans _ (mult a (req_r_pow kappa (Nat.min m n))) _).
    + unfold a.
      apply (req_iterate_metric_min_bound E_A m n Hg0pos).
    + apply (le_lt_trans _ (mult a (req_r_pow kappa N)) _).
      * apply (req_le_mult_compat_r a (req_r_pow kappa (Nat.min m n)) (req_r_pow kappa N)).
        -- apply (lt_le_iff _ _ (inl Ha)).
        -- assert (Hmle : (N <= m)%nat) by exact (natle_to_le N m Hm).
           assert (Hnle : (N <= n)%nat) by exact (natle_to_le N n Hn).
           apply (req_r_pow_dec_iter N (Nat.min m n)). lia.
      * exact HNgeo.
Qed.

(* ============ M. lim 存在（Id L14653-14672；lim 簇解冻件 1/5，字段 L40591 实测） ============ *)

Lemma req_iterate_lim_exists : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R => lim (fun n => iterate dynamics n E_A) E_star).
Proof.
  intros E_A Hg0pos.
  apply (cauchy_complete (fun n => iterate dynamics n E_A)).
  intros eps Hep.
  destruct (req_iterate_cauchy E_A Hg0pos eps Hep) as [N HN].
  exists N.
  intros m n Hm Hn.
  exact (HN m n Hm Hn).
Qed.

(* ============ N. 梯度绝对值单调（Id L14674-14730） ============ *)

Theorem req_iterate_grad_abs_mono : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt zero (entropy_gradient (iterate dynamics n E_A)) ->
  lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (abs (entropy_gradient (iterate dynamics n E_A))).
Proof.
  intros E_A n Heta Hgn Hgn1.
  assert (Hxnext : req (iterate dynamics (Datatypes.S n) E_A)
                       (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete]. exact (dynamics_gradient_step (iterate dynamics n E_A)). }
  assert (Heta_g : lt zero (mult eta (entropy_gradient (iterate dynamics n E_A)))).
  { apply (mult_positive eta (entropy_gradient (iterate dynamics n E_A)) Heta Hgn). }
  assert (Hlt0 : lt (iterate dynamics n E_A)
                    (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))).
  { apply (lt_id_l (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) zero)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (req_sym _ _ (plus_zero (iterate dynamics n E_A)))
                   (lt_plus_compat_le_lt (iterate dynamics n E_A) (iterate dynamics n E_A) zero
                                         (mult eta (entropy_gradient (iterate dynamics n E_A)))
                                         (le_refl (iterate dynamics n E_A)) Heta_g)). }
  assert (Hlt : lt (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  { apply (lt_id_r (iterate dynamics n E_A)
                   (plus (iterate dynamics n E_A) (mult eta (entropy_gradient (iterate dynamics n E_A))))
                   (iterate dynamics (Datatypes.S n) E_A)
                   (req_sym _ _ Hxnext) Hlt0). }
  assert (Hgdec : lt (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))
                     (entropy_gradient (iterate dynamics n E_A))).
  { apply (strict_concavity (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
    exact Hlt. }
  apply (req_gradient_abs_mono (iterate dynamics n E_A) (iterate dynamics (Datatypes.S n) E_A)).
  - exact Hlt.
  - exact Hgn1.
  - exact Hgdec.
Qed.

(* ============ O. lim 的 eps-N 语义 + 任意小非负（Id L14725-14731 同位） ============ *)

Variable lim_metric_approx : forall (u : nat -> R) (l : R),
  lim u l -> forall eps : R, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n -> lt (metric (u n) l) eps).

Variable le_all_eps_zero : forall x : R,
  (forall eps : R, lt zero eps -> lt x eps) -> le x zero.

(* ============ P. 辅件（Id L14732-14762） ============ *)


Lemma req_opp_zero : req (opp zero) zero.
Proof.
  exact (req_trans (opp zero) (plus zero (opp zero)) zero
                   (req_sym _ _
                     (req_trans (plus zero (opp zero)) (plus (opp zero) zero) (opp zero)
                                (plus_comm zero (opp zero))
                                (plus_zero (opp zero))))
                   (plus_opp zero)).
Qed.

(* Id abs_minus_zero L14732：abs (a − 0) == abs a *)
Lemma req_abs_minus_zero : forall a : R, req (abs (req_minus a zero)) (abs a).
Proof.
  intro a.
  exact (req_abs_compat (req_minus a zero) a
           (req_trans (plus a (opp zero)) (plus a zero) a
              (req_plus_compat a a (opp zero) zero (req_refl a) req_opp_zero)
              (plus_zero a))).
Qed.

(* ============ Q. lim 夹逼核心（Id L14763-14844；+2 假设位，登记表 2） ============ *)

Lemma req_grad_squeeze_zero : forall (E_A E_star : R),
  lim (fun n => iterate dynamics n E_A) E_star ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  req (entropy_gradient E_star) zero.
Proof.
  intros E_A E_star Hlim Hg0pos.
  apply metric_zero.
  apply le_antisym.
  - apply le_all_eps_zero.
    intros eps Heps.
    pose (eps2 := mult (inv_pos (plus one one) req_two_pos) eps).
    assert (Heps2 : lt zero eps2) by (unfold eps2; apply (req_half_pos_loc eps); exact Heps).
    pose (eps1 := mult (inv_pos L L_pos) eps2).
    assert (Heps1 : lt zero eps1).
    { unfold eps1.
      apply (mult_positive (inv_pos L L_pos) eps2).
      - apply inv_pos_pos.
      - exact Heps2. }
    destruct (lim_metric_approx (fun n => iterate dynamics n E_A) E_star Hlim eps1 Heps1) as [N1 HN1].
    destruct (r_arch_pow (abs (entropy_gradient (iterate dynamics 0 E_A))) Hg0pos eps2 Heps2) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    assert (Hn1 : NatLe N1 n) by (unfold n; apply natle_of_le; apply Nat.le_max_l).
    assert (Hn2 : NatLe N2 n) by (unfold n; apply natle_of_le; apply Nat.le_max_r).
    assert (Ht : le (metric (entropy_gradient E_star) zero)
                   (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                         (metric (entropy_gradient (iterate dynamics n E_A)) zero)))
      by exact (metric_triangle_plain (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)) zero).
    assert (Hhalf1 : lt (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))) eps2).
    { apply (le_lt_trans _ (mult L (metric (iterate dynamics n E_A) E_star)) _).
      - apply (le_id_l _ (abs (req_minus (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))) _).
        + apply (metric_abs (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A))).
        + apply (le_id_r _ (mult L (abs (req_minus E_star (iterate dynamics n E_A)))) _).
          * exact (req_mult_compat L L (abs (req_minus E_star (iterate dynamics n E_A)))
                                   (metric (iterate dynamics n E_A) E_star)
                                   (req_refl L)
                                   (req_trans (abs (req_minus E_star (iterate dynamics n E_A)))
                                              (abs (req_minus (iterate dynamics n E_A) E_star))
                                              (metric (iterate dynamics n E_A) E_star)
                                              (req_abs_minus_sym E_star (iterate dynamics n E_A))
                                              (req_sym _ _ (metric_abs (iterate dynamics n E_A) E_star)))).
          * exact (gradient_lipschitz E_star (iterate dynamics n E_A)).
      - apply (lt_id_r _ (mult L eps1) _).
        + unfold eps1.
          apply (req_trans _ _ _
                   (mult_assoc L (inv_pos L L_pos) eps2)
                   (req_trans _ _ _
                     (req_mult_compat (mult L (inv_pos L L_pos)) one eps2 eps2
                                      (inv_pos_correct L L_pos) (req_refl eps2))
                     (req_trans _ _ _ (mult_comm one eps2) (mult_one eps2)))).
        + apply (lt_id_l _ (mult (metric (iterate dynamics n E_A) E_star) L) _).
          * apply (mult_comm L (metric (iterate dynamics n E_A) E_star)).
          * apply (lt_id_r _ (mult eps1 L) _).
            -- exact (req_sym _ _ (mult_comm L eps1)).
            -- apply (lt_mult_compat (metric (iterate dynamics n E_A) E_star) eps1 L L_pos).
               exact (HN1 n Hn1). }
    assert (Hhalf2 : lt (metric (entropy_gradient (iterate dynamics n E_A)) zero) eps2).
    { apply (le_lt_trans _ (mult (req_r_pow kappa n) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
      - apply (le_id_l _ (abs (req_minus (entropy_gradient (iterate dynamics n E_A)) zero)) _).
        + apply (metric_abs (entropy_gradient (iterate dynamics n E_A)) zero).
        + apply (le_id_l _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
          * exact (req_abs_minus_zero (entropy_gradient (iterate dynamics n E_A))).
          * exact (req_grad_decay_iter E_A 0 n).
      - apply (le_lt_trans _ (mult (req_r_pow kappa N2) (abs (entropy_gradient (iterate dynamics 0 E_A)))) _).
        + apply (le_mult_compat_weak (req_r_pow kappa n) (req_r_pow kappa N2)
                                     (abs (entropy_gradient (iterate dynamics 0 E_A)))
                                     (abs_nonneg_plain (entropy_gradient (iterate dynamics 0 E_A)))).
          apply (req_r_pow_dec_iter N2 n). exact (natle_to_le N2 n Hn2).
        + apply (lt_id_l _ (mult (abs (entropy_gradient (iterate dynamics 0 E_A))) (req_r_pow kappa N2)) _).
          * exact (req_sym _ _ (mult_comm (abs (entropy_gradient (iterate dynamics 0 E_A))) (req_r_pow kappa N2))).
          * exact HN2. }
    apply (lt_id_r _ (plus eps2 eps2) _).
    { exact (req_half_twice eps req_two_pos). }
    { apply (le_lt_trans _ (plus (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                                 (metric (entropy_gradient (iterate dynamics n E_A)) zero)) _).
      { exact Ht. }
      { exact (lt_plus_compat (metric (entropy_gradient E_star) (entropy_gradient (iterate dynamics n E_A)))
                              eps2
                              (metric (entropy_gradient (iterate dynamics n E_A)) zero)
                              eps2
                              Hhalf1 Hhalf2). } }
  - apply metric_pos_plain.
Qed.

(* ============ R. dynamics_converges 组装（Id L14845-14874；lim 簇解冻件 2/5） ============ *)

Theorem req_dynamics_converges : forall (E_A : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  ExistsT (fun E_star : R =>
    And (lim (fun n => iterate dynamics n E_A) E_star)
        (req (entropy_gradient E_star) zero)).
Proof.
  intros E_A Hg0pos.
  destruct (req_iterate_lim_exists E_A Hg0pos) as [E_star Hlim].
  exists E_star.
  split.
  - exact Hlim.
  - exact (req_grad_squeeze_zero E_A E_star Hlim Hg0pos).
Qed.

(* ============ S. μ-强凹族（Id L14917-15063 同位） ============ *)

Variable mu : R.
Variable mu_pos : lt zero mu.
Variable strong_concavity : forall x y : R, lt x y ->
  le (mult mu (req_minus y x)) (req_minus (entropy_gradient x) (entropy_gradient y)).

(* Id dynamics_step_unfold L14875 *)
Lemma req_dynamics_step_unfold : forall x : R,
  req (dynamics x) (plus x (mult eta (entropy_gradient x))).
Proof.
  intros x. exact (dynamics_gradient_step x).
Qed.

(* Id minus_plus_cancel_gap L14882 *)
Lemma req_minus_plus_cancel_gap : forall a b : R,
  req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  exact (req_trans (plus (plus a (opp b)) b) (plus a (plus (opp b) b)) a
                   (req_sym _ _ (plus_assoc a (opp b) b))
                   (req_trans (plus a (plus (opp b) b)) (plus a zero) a
                              (req_plus_compat a a (plus (opp b) b) zero
                                               (req_refl a) (req_plus_opp_l b))
                              (plus_zero a))).
Qed.

(* Id gradient_step_contraction L14896：K1a 正分支单步收缩 *)
Lemma req_gradient_step_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  le (entropy_gradient (dynamics x))
     (mult (req_minus one (mult eta mu)) (entropy_gradient x)).
Proof.
  intros x Heta Heta_mu Hgx.
  assert (Heta_g : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) Heta Hgx).
  assert (Hlt : lt x (dynamics x)).
  {
    apply (lt_id_l x (plus x zero) (dynamics x) (req_sym _ _ (plus_zero x))).
    apply (lt_id_r (plus x zero) (plus x (mult eta (entropy_gradient x))) (dynamics x)
                   (req_sym _ _ (req_dynamics_step_unfold x))).
    apply (lt_plus_compat_le_lt x x zero (mult eta (entropy_gradient x)) (le_refl x) Heta_g).
  }
  pose proof (strong_concavity x (dynamics x) Hlt) as Hsc.
  assert (Hdiff : req (req_minus (dynamics x) x) (mult eta (entropy_gradient x))).
  {
    unfold req_minus.
    exact (req_trans (plus (dynamics x) (opp x))
                     (plus (plus x (mult eta (entropy_gradient x))) (opp x))
                     (mult eta (entropy_gradient x))
                     (req_plus_compat (dynamics x)
                                      (plus x (mult eta (entropy_gradient x)))
                                      (opp x) (opp x)
                                      (req_dynamics_step_unfold x) (req_refl (opp x)))
                     (req_minus_plus_cancel_r x (mult eta (entropy_gradient x)))).
  }
  assert (Hsc' : le (mult mu (mult eta (entropy_gradient x)))
                    (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult mu (mult eta (entropy_gradient x)))
                   (mult mu (req_minus (dynamics x) x))
                   (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (req_sym _ _
                     (req_mult_compat mu mu (req_minus (dynamics x) x) (mult eta (entropy_gradient x))
                                      (req_refl mu) Hdiff))).
    exact Hsc. }
  assert (Hmm : req (mult mu (mult eta (entropy_gradient x)))
                    (mult (mult eta mu) (entropy_gradient x))).
  {
    exact (req_trans (mult mu (mult eta (entropy_gradient x)))
                     (mult mu (mult (entropy_gradient x) eta))
                     (mult (mult eta mu) (entropy_gradient x))
                     (req_mult_compat mu mu (mult eta (entropy_gradient x)) (mult (entropy_gradient x) eta)
                                      (req_refl mu) (mult_comm eta (entropy_gradient x)))
                     (req_trans (mult mu (mult (entropy_gradient x) eta))
                                (mult (mult mu (entropy_gradient x)) eta)
                                (mult (mult eta mu) (entropy_gradient x))
                                (mult_assoc mu (entropy_gradient x) eta)
                                (req_trans (mult (mult mu (entropy_gradient x)) eta)
                                           (mult (mult (entropy_gradient x) mu) eta)
                                           (mult (mult eta mu) (entropy_gradient x))
                                           (req_mult_compat (mult mu (entropy_gradient x)) (mult (entropy_gradient x) mu) eta eta
                                                            (mult_comm mu (entropy_gradient x)) (req_refl eta))
                                           (req_trans (mult (mult (entropy_gradient x) mu) eta)
                                                      (mult eta (mult (entropy_gradient x) mu))
                                                      (mult (mult eta mu) (entropy_gradient x))
                                                      (mult_comm (mult (entropy_gradient x) mu) eta)
                                                      (req_trans (mult eta (mult (entropy_gradient x) mu))
                                                                 (mult eta (mult mu (entropy_gradient x)))
                                                                 (mult (mult eta mu) (entropy_gradient x))
                                                                 (req_mult_compat eta eta (mult (entropy_gradient x) mu) (mult mu (entropy_gradient x))
                                                                                  (req_refl eta) (mult_comm (entropy_gradient x) mu))
                                                                 (mult_assoc eta mu (entropy_gradient x))))))).
  }
  assert (Hsc'' : le (mult (mult eta mu) (entropy_gradient x))
                     (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))).
  { apply (le_id_l (mult (mult eta mu) (entropy_gradient x))
                   (mult mu (mult eta (entropy_gradient x)))
                   (req_minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                   (req_sym _ _ Hmm)).
    exact Hsc'. }
  pose (A := mult (mult eta mu) (entropy_gradient x)).
  pose (B := entropy_gradient x).
  pose (C := entropy_gradient (dynamics x)).
  assert (H1 : le (plus A C) B).
  {
    apply (le_id_r (plus A C) (plus (req_minus B C) C) B).
    - exact (req_minus_plus_cancel_gap B C).
    - apply (le_plus_compat A (req_minus B C) C C Hsc'' (le_refl C)).
  }
  assert (H2 : le (plus (plus A C) (opp A)) (plus B (opp A))).
  {
    apply (le_plus_compat (plus A C) B (opp A) (opp A) H1 (le_refl (opp A))).
  }
  assert (H3 : req (plus (plus A C) (opp A)) C).
  {
    unfold A. unfold C.
    apply (req_trans (plus (plus (mult (mult eta mu) (entropy_gradient x)) (entropy_gradient (dynamics x))) (opp (mult (mult eta mu) (entropy_gradient x))))
                     (plus (plus (entropy_gradient (dynamics x)) (mult (mult eta mu) (entropy_gradient x))) (opp (mult (mult eta mu) (entropy_gradient x))))
                     (entropy_gradient (dynamics x))
                     (req_plus_compat (plus (mult (mult eta mu) (entropy_gradient x)) (entropy_gradient (dynamics x)))
                                      (plus (entropy_gradient (dynamics x)) (mult (mult eta mu) (entropy_gradient x)))
                                      (opp (mult (mult eta mu) (entropy_gradient x)))
                                      (opp (mult (mult eta mu) (entropy_gradient x)))
                                      (plus_comm (mult (mult eta mu) (entropy_gradient x)) (entropy_gradient (dynamics x)))
                                      (req_refl (opp (mult (mult eta mu) (entropy_gradient x)))))
                     (req_trans (plus (plus (entropy_gradient (dynamics x)) (mult (mult eta mu) (entropy_gradient x))) (opp (mult (mult eta mu) (entropy_gradient x))))
                                (plus (entropy_gradient (dynamics x)) (plus (mult (mult eta mu) (entropy_gradient x)) (opp (mult (mult eta mu) (entropy_gradient x)))))
                                (entropy_gradient (dynamics x))
                                (req_sym _ _ (plus_assoc (entropy_gradient (dynamics x)) (mult (mult eta mu) (entropy_gradient x)) (opp (mult (mult eta mu) (entropy_gradient x)))))
                                (req_trans (plus (entropy_gradient (dynamics x)) (plus (mult (mult eta mu) (entropy_gradient x)) (opp (mult (mult eta mu) (entropy_gradient x)))))
                                           (plus (entropy_gradient (dynamics x)) zero)
                                           (entropy_gradient (dynamics x))
                                           (req_plus_compat (entropy_gradient (dynamics x)) (entropy_gradient (dynamics x))
                                                            (plus (mult (mult eta mu) (entropy_gradient x)) (opp (mult (mult eta mu) (entropy_gradient x))))
                                                            zero
                                                            (req_refl (entropy_gradient (dynamics x)))
                                                            (plus_opp (mult (mult eta mu) (entropy_gradient x))))
                                           (plus_zero (entropy_gradient (dynamics x)))))).
  }
  assert (H4 : req (plus B (opp A)) (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  { unfold A. unfold B. apply req_refl. }
  assert (H5 : le C (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))).
  {
    apply (le_id_l C (plus (plus A C) (opp A)) (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) (req_sym _ _ H3)).
    apply (le_id_r (plus (plus A C) (opp A)) (plus B (opp A)) (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x))) H4 H2).
  }
  assert (H6 : req (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                   (mult (req_minus one (mult eta mu)) (entropy_gradient x))).
  {
    unfold req_minus.
    exact (req_sym _ _
             (req_trans (mult (plus one (opp (mult eta mu))) (entropy_gradient x))
                        (plus (mult one (entropy_gradient x)) (mult (opp (mult eta mu)) (entropy_gradient x)))
                        (plus (entropy_gradient x) (opp (mult (mult eta mu) (entropy_gradient x))))
                        (req_mult_plus_distr_r one (opp (mult eta mu)) (entropy_gradient x))
                        (req_trans (plus (mult one (entropy_gradient x)) (mult (opp (mult eta mu)) (entropy_gradient x)))
                                   (plus (entropy_gradient x) (mult (opp (mult eta mu)) (entropy_gradient x)))
                                   (plus (entropy_gradient x) (opp (mult (mult eta mu) (entropy_gradient x))))
                                   (req_plus_compat (mult one (entropy_gradient x)) (entropy_gradient x)
                                                    (mult (opp (mult eta mu)) (entropy_gradient x))
                                                    (mult (opp (mult eta mu)) (entropy_gradient x))
                                                    (req_trans (mult one (entropy_gradient x))
                                                               (mult (entropy_gradient x) one)
                                                               (entropy_gradient x)
                                                               (mult_comm one (entropy_gradient x))
                                                               (mult_one (entropy_gradient x)))
                                                    (req_refl (mult (opp (mult eta mu)) (entropy_gradient x))))
                                   (req_plus_compat (entropy_gradient x) (entropy_gradient x)
                                                    (mult (opp (mult eta mu)) (entropy_gradient x))
                                                    (opp (mult (mult eta mu) (entropy_gradient x)))
                                                    (req_refl (entropy_gradient x))
                                                    (req_opp_mult_r (mult eta mu) (entropy_gradient x)))))).
  }
  apply (le_id_r C (req_minus (entropy_gradient x) (mult (mult eta mu) (entropy_gradient x)))
                 (mult (req_minus one (mult eta mu)) (entropy_gradient x)) H6 H5).
Qed.

(* Id minus_pos L15007：a < b ⟹ 0 < b − a *)
Lemma req_minus_pos : forall a b : R, lt a b -> lt zero (req_minus b a).
Proof.
  intros a b Hab. unfold req_minus.
  exact (lt_id_l zero (plus a (opp a)) (plus b (opp a))
           (req_sym _ _ (plus_opp a))
           (lt_plus_compat_lt_le a b (opp a) (opp a) Hab (le_refl (opp a)))).
Qed.

(* Id gradient_step_abs_contraction L15016：K1c 正分支单步绝对值收缩 *)
Lemma req_gradient_step_abs_contraction : forall x : R,
  lt zero eta ->
  lt (mult eta mu) one ->
  lt zero (entropy_gradient x) ->
  lt zero (entropy_gradient (dynamics x)) ->
  le (abs (entropy_gradient (dynamics x)))
     (mult (req_minus one (mult eta mu)) (abs (entropy_gradient x))).
Proof.
  intros x Heta Heta_mu Hgx Hgdyn.
  assert (Habsd : req (abs (entropy_gradient (dynamics x))) (entropy_gradient (dynamics x)))
    by exact (abs_pos (entropy_gradient (dynamics x)) Hgdyn).
  assert (Habsx : req (abs (entropy_gradient x)) (entropy_gradient x))
    by exact (abs_pos (entropy_gradient x) Hgx).
  apply (le_id_l (abs (entropy_gradient (dynamics x)))
                 (entropy_gradient (dynamics x))
                 (mult (req_minus one (mult eta mu)) (abs (entropy_gradient x)))
                 Habsd).
  apply (le_id_r (entropy_gradient (dynamics x))
                 (mult (req_minus one (mult eta mu)) (entropy_gradient x))
                 (mult (req_minus one (mult eta mu)) (abs (entropy_gradient x)))
                 (req_mult_compat (req_minus one (mult eta mu)) (req_minus one (mult eta mu))
                                  (entropy_gradient x) (abs (entropy_gradient x))
                                  (req_refl (req_minus one (mult eta mu))) (req_sym _ _ Habsx))
                 (req_gradient_step_contraction x Heta Heta_mu Hgx)).
Qed.

(* Id gradient_iterate_abs_decay L15045：K2 正分支单步迭代收缩 *)
Theorem req_gradient_iterate_abs_decay : forall (E_A : R) (n : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall k : nat, (k <= Datatypes.S n)%nat -> lt zero (entropy_gradient (iterate dynamics k E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (Datatypes.S n) E_A)))
     (mult (req_minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n Heta Heta_mu Hall.
  assert (Hgn : lt zero (entropy_gradient (iterate dynamics n E_A))).
  { apply Hall. lia. }
  assert (Hgn1 : lt zero (entropy_gradient (iterate dynamics (Datatypes.S n) E_A))).
  { apply Hall. lia. }
  exact (req_gradient_step_abs_contraction (iterate dynamics n E_A) Heta Heta_mu Hgn Hgn1).
Qed.

(* Id grad_decay_positive_iter L15064：K3 正分支 κ 幂衰减 *)
Theorem req_grad_decay_positive_iter : forall (E_A : R) (n k : nat),
  lt zero eta ->
  lt (mult eta mu) one ->
  (forall j : nat, (j <= n + k)%nat -> lt zero (entropy_gradient (iterate dynamics j E_A))) ->
  le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
     (mult (req_r_pow (req_minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))).
Proof.
  intros E_A n k Heta Heta_mu Hall.
  assert (Hkpos : lt zero (req_minus one (mult eta mu))).
  { apply (req_minus_pos _ _ Heta_mu). }
  induction k as [| k IH]; cbn -[req req_refl req_sym req_trans zero one plus mult opp abs lt le req_plus_compat req_mult_compat req_opp_compat req_abs_compat req_lt_compat req_le_compat plus_assoc plus_comm plus_zero plus_opp mult_assoc mult_comm mult_one distrib mult_zero lt_irrefl lt_trans le_refl le_trans le_antisym le_lt_trans lt_le_trans lt_le_iff le_id_l le_id_r lt_id_l lt_id_r inv_pos inv_pos_correct one_pos lt_plus_compat le_plus_compat plus_positive mult_positive lt_mult_compat le_mult_compat le_mult_compat_weak opp_lt_compat lt_zero_opp opp_le_compat inv_pos_pos inv_pos_ext inv_pos_le_compat min min_le_l min_le_r min_pos r_max r_max_le_l r_max_le_r r_max_l_iff r_max_r_iff pos_test pos_test_lt lt_pos_test pos_part pos_part_def pos_part_nonneg mr_if mr_if_true mr_if_false abs_nonneg abs_triangle abs_zero abs_mult abs_opp abs_pos exp_neg exp_neg_pos exp_neg_zero exp_neg_plus exp_neg_decr exp_neg_le_decr log log_mult log_one log_le_linear_eps log_inv log_inv_log exp_neg_log_inv metric metric_sym metric_pos metric_zero metric_triangle lim lim_unique cauchy_complete].
  - rewrite (Nat.add_0_r n).
    apply (le_id_r _ (abs (entropy_gradient (iterate dynamics n E_A))) _).
    + exact (req_trans _ _ _
               (req_sym _ _ (mult_one (abs (entropy_gradient (iterate dynamics n E_A)))))
               (req_sym _ _ (mult_comm one (abs (entropy_gradient (iterate dynamics n E_A)))))).
    + apply le_refl.
  - apply (le_trans _ (mult (req_minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A)))) _).
    + rewrite (Nat.add_succ_r n k).
      apply (req_gradient_iterate_abs_decay E_A (n + k) Heta Heta_mu).
      intros j Hj. apply Hall. lia.
    + assert (IH' : le (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                       (mult (req_r_pow (req_minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))).
      { apply IH. intros j Hj. apply Hall. lia. }
      apply (le_id_r (mult (req_minus one (mult eta mu)) (abs (entropy_gradient (iterate dynamics (n + k) E_A))))
                     (mult (req_minus one (mult eta mu))
                           (mult (req_r_pow (req_minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A)))))
                     (mult (mult (req_minus one (mult eta mu)) (req_r_pow (req_minus one (mult eta mu)) k)) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (mult_assoc (req_minus one (mult eta mu)) (req_r_pow (req_minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                     (req_le_mult_compat_r (req_minus one (mult eta mu))
                                           (abs (entropy_gradient (iterate dynamics (n + k) E_A)))
                                           (mult (req_r_pow (req_minus one (mult eta mu)) k) (abs (entropy_gradient (iterate dynamics n E_A))))
                                           (lt_le_iff _ _ (inl Hkpos))
                                           IH')).
Qed.

(* ============ T. 驻点族 + 唯一吸引子（Id L15120-15233） ============ *)

Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))).

(* Id gradient_zero_entropy_max L15120 *)
Theorem req_gradient_zero_entropy_max : forall x : R,
  req (entropy_gradient x) zero ->
  forall y : R, le (entropy y) (entropy x).
Proof.
  intros x Hg y.
  assert (Htangent : le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))))
    by exact (entropy_tangent x y).
  assert (Hid : req (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))) (entropy x)).
  {
    apply (req_trans (plus (entropy x) (mult (entropy_gradient x) (req_minus y x)))
                     (plus (entropy x) zero)
                     (entropy x)
                     (req_plus_compat (entropy x) (entropy x)
                                      (mult (entropy_gradient x) (req_minus y x)) zero
                                      (req_refl (entropy x))
                                      (req_trans (mult (entropy_gradient x) (req_minus y x))
                                                 (mult zero (req_minus y x))
                                                 zero
                                                 (req_mult_compat (entropy_gradient x) zero
                                                                  (req_minus y x) (req_minus y x)
                                                                  Hg (req_refl (req_minus y x)))
                                                 (req_trans (mult zero (req_minus y x))
                                                            (mult (req_minus y x) zero)
                                                            zero
                                                            (mult_comm zero (req_minus y x))
                                                            (mult_zero (req_minus y x)))))
                     (plus_zero (entropy x))).
  }
  exact (le_id_r (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))) (entropy x) Hid Htangent).
Qed.

(* Id gradient_zero_neg_entropy_truth L15142 *)
Theorem req_gradient_zero_neg_entropy_truth : forall x : R,
  req (entropy_gradient x) zero ->
  forall y : R, le (opp (entropy x)) (opp (entropy y)).
Proof.
  intros x Hg y.
  exact (opp_le_compat (entropy y) (entropy x)
           (req_gradient_zero_entropy_max x Hg y)).
Qed.

(* 弱三分（Id L15169 同位；Real 层 real_weak_trich L32526 已证可满足） *)
Variable weak_trich : forall x y : R, Not (lt x y) -> Not (lt y x) -> req x y.

(* Id gradient_zero_unique L15169：K1 驻点唯一性 *)
Lemma req_gradient_zero_unique : forall x y : R,
  req (entropy_gradient x) zero ->
  req (entropy_gradient y) zero ->
  req x y.
Proof.
  intros x y Hgx Hgy.
  apply weak_trich.
  - intro Hxy.
    pose proof (strict_concavity x y Hxy) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient y) zero).
    + exact (req_sym _ _ Hgy).
    + apply (lt_id_r (entropy_gradient y) (entropy_gradient x) zero Hgx Hdec).
  - intro Hyx.
    pose proof (strict_concavity y x Hyx) as Hdec.
    apply (lt_irrefl zero).
    apply (lt_id_l zero (entropy_gradient x) zero).
    + exact (req_sym _ _ Hgx).
    + apply (lt_id_r (entropy_gradient x) (entropy_gradient y) zero Hgy Hdec).
Qed.

(* Id unique_attractor L15197：K3 唯一吸引子（lim 簇解冻件 4/5） *)
Theorem req_unique_attractor : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    req E1 E2.
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (req_grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (req_grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  exact (req_gradient_zero_unique E1 E2 Hg1 Hg2).
Qed.

(* Id attractor_converges_unique_truth L15215（lim 簇解冻件 5/5；And 为 Set 层乘积） *)
Theorem req_attractor_converges_unique_truth : forall (E_A E_A' : R),
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A))) ->
  lt zero (abs (entropy_gradient (iterate dynamics 0 E_A'))) ->
  forall E1 E2 : R,
    lim (fun n => iterate dynamics n E_A) E1 ->
    lim (fun n => iterate dynamics n E_A') E2 ->
    And (req E1 E2)
        (And (req (entropy_gradient E1) zero)
             (forall y : R, le (opp (entropy E1)) (opp (entropy y)))).
Proof.
  intros E_A E_A' Hg0 Hg0' E1 E2 Hlim1 Hlim2.
  pose proof (req_grad_squeeze_zero E_A E1 Hlim1 Hg0) as Hg1.
  pose proof (req_grad_squeeze_zero E_A' E2 Hlim2 Hg0') as Hg2.
  split.
  - exact (req_gradient_zero_unique E1 E2 Hg1 Hg2).
  - split.
    + exact Hg1.
    + exact (req_gradient_zero_neg_entropy_truth E1 Hg1).
Qed.

End UpReqConvergenceCauchy.

(* ============================================================ *)
(* ---- (d) 冻结清单（本节 2 件；§1.1 边界2；零证明行） ----      *)
(*                                                              *)
(* 1. natle_to_le（Id @L14643）：纯 nat Id 机器（NatLe/leb/  *)
(*    ≤，零 R）；req 侧依存 = 跨接口 Require 复用 原件裸名    *)
(*    （规划书 §3.4；GRPO grpo_count_one 预定路线同款），零重证。  *)
(*    依存位：req_iterate_cauchy / req_iterate_cauchy_explicit_N / *)
(*    req_grad_squeeze_zero（证内 (N <= n)%nat 桥接）。            *)
(* 2. natle_of_le（Id @L14747）：同上；req 侧依存 = 跨接口    *)
(*    Require 复用 原件裸名。依存位：req_grad_squeeze_zero    *)
(*    （Nat.max 两翼 NatLe 构造）。                                *)
(* 另：req_iterate_cauchy 结论位由 Id 的 (N <= m)%nat 前提改为      *)
(* NatLe 前提（cauchy_complete 字段 L40591 对接形）——语义同构，     *)
(* 依存 iterate_lim_exists 零摩擦，登记头注登记表 4。                *)
(* ============================================================ *)
Print Assumptions req_r_pow_nonneg.
Print Assumptions req_minus_pos.
Print Assumptions req_one_minus_kappa_pos.
Print Assumptions req_abs_minus_zero.
Print Assumptions req_gradient_zero_neg_entropy_truth.
