(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 头批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   w2_gibbs_eq（原 L479，2 句玩具证）                                   *)
(*   w2_gap_diff（原 L457，2 句玩具证）                                   *)
(*   w2_policy_improvement_mono（原 L445，2 句玩具证）                    *)
(*   w2_rel_ent_self_zero（原 L438，2 句玩具证）                          *)
(*   w2_pi_star_normalized（原 L433，1 句玩具证）                         *)
(*   w2_pi_next_normalized（原 L425，2 句玩具证）                         *)
(*   r2u_JJ_witness_ext（原 L417，2 句玩具证）                            *)
(*   log_req_compat_real（原 L121，2 句玩具证）                           *)
(*   log_req_witness_compat（原 L109，2 句玩具证）                        *)
(* ============================================================ *)
(* ============================================================ *)
(* 【 恒等守恒修订注记】 包AW九 （恒等头注修订全量首段）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 （包AL）全量恒等核查已证结论、（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 9 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此修订。                                        *)
(* 修订口径：真替换 0 槽＋恒等守恒 9 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；记录册承载见  附录／ 修正块／ 评估册／ 记录册。                        *)
(* 附记： 判级全文恒等； 全量首段整批直推（ 六·1 方案①）                           *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqU2.v *)
(* *)
(* 目的： U2 升级面：log_req_compat 桥与对齐族 witness 扩充。 *)
(* 主件： log_req_compat_real / u2_rlhf_optimal_seed_discharge 与 w2_* 求和定律族。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqAlign、UpReqAlign2、UpReqAlign3、UpSigMigrate2。 *)
(* 备注： 对数接口兼容性经具体实数实例落定；witness 外延为构造核。 *)
(* ============================================================ *)

(* UpReqU2.v — 签名迁移批 3 U2 ：ReqLogBridge 扩展 + req_u2_kl_arg2_ext + U2 主体 7 件 req 化
     （批 2 清单 U2FixedPoint 区：Section 23281–23791 共 10 件；
       2 件辅件 req_u2_nonneg_sum_zero / req_u2_minus_minus 已在 UpReqDist.v 结果，
       本文件结果保底 2 件 + 主体 7 件，10 − 2 − 1 = 7 核对闭合。）
   上游（Require 按依赖序，全部使用不重建）：
     CW_ConstructiveWorld_219.v（基座，含 setoid 接口与 RealEnhancedReal 具体实例）
     UpReqAlgebra.v（批 1 代数银行 + ReqLogBridge 节）+ UpReqDist.v（批 2，req_gibbs_equality 等）
     + UpReqAlign.v / UpReqAlign2.v（批 3/3b，req2 定义簇）+ UpReqAlign3.v（批 3c，r2_/w_ 机器）
     + UpSigMigrate2.v（RLHF req 机器上游）。
   纯 term-mode（req_trans 链 + compat 桥），零 Morphisms 依赖；
   Set 层语句（req/lt/le/Or/And 均为 自定义 Set 值连词，零 Prop 泄露）。
   ----------------------------------------------------------------
   本文件结果：
   [保底 1] log_req_compat —— setoid log 兼容场，文件级成品引理（ReqLogBridge 扩展）。
     语句形态与 UpReqAlign3.v Section 内同名自持桥假设位逐位同形
     （forall x y Hx Hy, req x y -> req (log x Hx) (log y Hy)），
     但该假设位节闭后非常量不可跨文件使用，故以**显式单参桥**（log 单调 le 桥）
     重建为文件级引理：req 兼容场 ⟸ log 单调 le 桥（Real 层种子 real_log_le_mono
     同形；无条件版不可得——接口仅备逐 eps log_le_linear_eps，序无消去，诚实边界）。
     log_req_compat 的 x ≡ x 特例；req_gibbs_equality 的 log_inv_one_inv 槽
     见证无关化即使用此件（Algebra 版 req_log_inv_one_inv 结论钉死 inv_pos_pos 见证）。
   [保底 1b] log_req_compat_real —— 具体实例消解（T2 模板 ② 形态）：
     以 L112104 real_log_le_mono 显式应用抽象桥，Real 层无条件闭合。
   [保底 2] req_u2_kl_arg2_ext —— 函数外延性敏感件 (b) 化改述（规划书 §3-(d).3 规则）：
     逐点 req 前提版 (forall s, req (q s) (q' s)) -> req (KL p q) (KL p q')。
     诚实签名变化：log 前提化（Hp/Hq 显式携带）+ Hq' 逐点正性由 req_lt_compat
   [主体 7 件] req_u2_align_objective_ext / req_u2_pi_next_pi_star_fixed /
     req_u2_no_progress_fixed_point / req_u2_fixed_point_unique /
     req_u2_no_progress_optimal / req_u2_optimal_no_progress /
     req_u2_objective_eq_optimal_iff —— 与 Id 版语句逐位同构（T2 模板 ①：
     假设位逐位对应；Id align_objective 的 req 对位 = JJ := req2_J；
     Id pi_next/pi_star 的 req 对位 = NPX/PSTR（req2_pi_next/pi_star）；
     Id relative_entropy 的 req 对位 = KLE（req2_rel_ent，与 UpReqDist.req_relative_entropy
     δ 透明同形）。
   [保底 3] u2_rlhf_optimal_seed_discharge —— rlhf_optimal_seed 槽 FEP 装配消解
     （Id rlhf_optimal @19049 对位；沿 UpSigMigrate2.a_rlhf_optimal 消解手法：
     FEP 分解 ⟹ F(pistar) ≤ F(p) ⟹ opp 保序取负。分解机 = UpReqAlign3
     对 p := pistar 复用之 + w_rel_ent_self_zero（KL(pistar‖pistar)==0）得
     F(p) == F(pistar) + β·KL(p‖pistar)；KL ≥ 0 = req2_gibbs_inequality 槽（登记表 5）
     + β>0 保序；完成 = le_id_l/r 转换 + opp_le_compat）。
     节内 rlhf_optimal_seed 槽随之降为使用件（Hypothesis → Definition）。
   ----------------------------------------------------------------
   诚实桥假设位登记表（逐位保留，不放大主张；槽 = 节参数，非公理，
   唯一性件 Print Assumptions 因此保持 Closed under the global context）：
   1. sum_zero_nonneg —— SumOver 类 sum_zero_nonneg 字段的 req 槽
     （req_gibbs_equality 出口参数位，UpReqDist ReqFEP 同款假设位）。
   2. log_le_linear —— log x ≤ x−1 的 plain-le 桥（setoid 接口仅备逐 eps 形式，
     深水区注 = UpReqDist 文件头同款；req_gibbs_inequality/equality 出口参数位）。
     Real 层需强三分/LPO，构造性不可证，诚实边界 = L41204 注）。
   4. log_req_compat / log_inv_exp_neg_req —— ReqLogBridge 同位桥槽
     （本文件保底件给出单参桥归约与具体实例消解）。
   5. req2_gibbs_inequality —— KL ≥ 0 桥槽（UpReqAlign3 同名假设位同位；
     KL ≥ 0 的 plain-le 形态不可由接口逐 eps 字段导出）。
   6. req_backward_kl_step_le —— 【已消解降级，非槽】向后 KL 单步 ≤ 桥
     （Id policy_iter_backward_kl_step_le @22790 同位）。UpReqAlign3 增量
     已结果（req2_backward_kl_step 主定理三点恒等式 + r2_backward_kl_step_le
     Print Assumptions 保持 Closed。
     （= u2_rlhf_optimal_seed_discharge 节参数一次喂定；FEP 装配吃
     r2_F_align_kl_diff + w_rel_ent_self_zero + req2_gibbs_inequality（登记表 5），
     Print Assumptions 保持 Closed）。
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
Require Import UpReqDist.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real, and the field names below are bound to the global constants. *)
Notation R := Real.
Notation req := real_eq.
Notation req_refl := real_eq_refl.
Notation req_sym := real_eq_sym.
Notation req_trans := real_eq_trans.
Notation zero := real_zero.
Notation one := real_one.
Notation plus := real_plus.
Notation mult := real_mult.
Notation opp := real_opp.
Notation lt := real_lt.
Notation le := real_le.
Notation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Notation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Notation req_opp_compat := RealSetoid.real_eq_opp_compat.
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation plus_opp := real_plus_opp.
Notation mult_comm := real_mult_comm.
Notation mult_one := real_mult_one.
Notation mult_zero := real_mult_zero.
Notation le_refl := real_le_refl.
Notation le_antisym := real_le_antisym.
Notation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Notation le_id_l := RealSetoid.real_le_id_l.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation inv_pos := real_inv_pos.
Notation le_plus_compat := real_le_plus_compat.
Notation opp_le_compat := real_opp_le_compat.
Notation inv_pos_pos := real_inv_pos_pos.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation log := real_log.
Notation log_inv := real_log_inv.

(* ============================================================ *)
(* 保底 1：log_req_compat —— ReqLogBridge 扩展（文件级成品引理） *)
(* ============================================================ *)

(* 单参桥版：req 兼容场 ⟸ log 单调 le 桥。
   路线：req x y 经 lt_le_iff 右支升 le，双支 le_antisym 完成。
   real_log_le_mono 同形，可被 T2 模板 ② 显式应用消解（见 log_req_compat_real）。 *)
Lemma log_req_compat : 
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    le x y -> le (log x Hx) (log y Hy)) ->
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros Hmono x y Hx Hy Hxy.
  apply (le_antisym (log x Hx) (log y Hy)).
  - apply (Hmono x y Hx Hy).
    exact (lt_le_iff x y (inr Hxy)).
  - apply (Hmono y x Hy Hx).
    exact (lt_le_iff y x (inr (req_sym x y Hxy))).
Qed.

(* 保底 1a：log 见证无关性——同点双正性见证转换（x ≡ x 特例；
   吃 Align3 形态兼容槽，零单调需求）。 *)
Lemma log_req_witness_compat : 
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)) ->
  forall (x : R) (Hx : lt zero x) (Hx' : lt zero x),
    req (log x Hx) (log x Hx').
Proof.
  intros Hcompat x Hx Hx'.
  exact (Hcompat x x Hx Hx' (req_refl x)).
Qed.

(* 保底 1b：具体实例消解（T2 模板 ②）——Real 层无条件闭合。
   种子：real_log_le_mono（L112104）显式应用抽象桥单参位。 *)
Lemma log_req_compat_real : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (log_req_compat (fun (a b : Real) (Ha : lt zero a) (Hb : lt zero b) (Hab : le a b) => real_log_le_mono a b Ha Hb Hab) x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* 保底 2：req_u2_kl_arg2_ext —— KL 对第二参数逐点 req 外延                     *)
(*（Id u2_kl_arg2_ext @23369 的 (b) 化改述：逐点 req 前提版）                   *)
(* ============================================================ *)
(* 诚实签名变化：log 前提化（Hp/Hq 显式）+ Hq' 正性由 req_lt_compat 运输导出。  *)
Lemma req_u2_kl_arg2_ext :
  forall  (S : Set)
         (sumf : (S -> R) -> R),
    (forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
      req x y -> req (log x Hx) (log y Hy)) ->
    forall (p q q' : S -> R) (Hp : forall s : S, lt zero (p s))
                            (Hq : forall s : S, lt zero (q s))
                            (Hq' : forall s : S, lt zero (q' s)),
      (forall s : S, req (q s) (q' s)) ->
      req (req2_rel_ent S sumf p q Hp Hq)
          (req2_rel_ent S sumf p q' Hp Hq').
Proof.
  intros S sumf Hext Hlog p q q' Hp Hq Hq' Hqq'.
  unfold req2_rel_ent.
  apply (Hext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
              (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q' s) (Hq' s))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
                         (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))
                         (req_minus (log (p s) (Hp s)) (log (q' s) (Hq' s)))
                         (req_refl (p s))).
  exact (req2_minus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                           (log (q s) (Hq s)) (log (q' s) (Hq' s))
                           (req_refl (log (p s) (Hp s)))
                           (Hlog (q s) (q' s) (Hq s) (Hq' s) (Hqq' s))).
Qed.

(* ============================================================ *)
(* 保底 3：u2_rlhf_optimal_seed_discharge —— rlhf_optimal_seed 槽 FEP 装配消解  *)
(*（Id rlhf_optimal @19049 的 req 对位；沿 UpSigMigrate2.a_rlhf_optimal         *)
(*  消解手法：FEP 分解 ⟹ F(pistar) ≤ F(p) ⟹ opp 保序取负。                          *)


(*  对 u := pistar 复用该分解，KL(pistar‖pistar) == 0（w_rel_ent_self_zero）消去首项得      *)

(*  KL ≥ 0 = req2_gibbs_inequality 槽（登记表 5，本件不改其显式假设）+ β>0 保序；     *)
(*  完成 = le_id_l/r 转换 + req_minus δ 展开（plus·opp）+ opp_le_compat。       *)
(*  假设位降级：节内 rlhf_optimal_seed 由 Hypothesis 改 Definition 使用本件       *)
(*  （节参数一次喂定，零重证）；U2a/U2e 使用链 Print Assumptions 保持 Closed。   *)
(* ============================================================ *)
Lemma u2_rlhf_optimal_seed_discharge :
  forall  (S : Set)
         (sumf : (S -> R) -> R),
    (forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
    (forall f g : S -> R,
      req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))) ->
    (forall (a : R) (f : S -> R),
      req (sumf (fun s => mult a (f s))) (mult a (sumf f))) ->
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
      req x y -> req (log x Hx) (log y Hy)) ->
    (forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
    forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (ZAL_pos : lt zero (req2_Z_align S sumf reward beta beta_pos
                                             pi_ref)),
      (forall (q r : S -> R) (Hq : req2_pos_dist S q)
                              (Hr : req2_pos_dist S r),
        le zero (req2_rel_ent S sumf q r Hq Hr)) ->
      forall (p : S -> R) (Hn : req2_norm_one S sumf p)
             (Hp : req2_pos_dist S p),
        le (req2_J S sumf reward beta pi_ref pi_ref_pos p Hp)
           (req2_J S sumf reward beta pi_ref pi_ref_pos
                    (req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos)
                    (req2_pi_star_pos S sumf reward beta beta_pos pi_ref
                                       pi_ref_pos ZAL_pos)).
Proof.
  intros S sumf Hext Hadd Hlin Hlog Hinv reward beta beta_pos
         pi_ref pi_ref_pos ZAL_pos Hgibbs p Hn Hp.
  set (PSTR := req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos).
  set (PSTR_pos := req2_pi_star_pos S sumf reward beta beta_pos pi_ref
                                     pi_ref_pos ZAL_pos).
  set (ZAL := req2_Z_align S sumf reward beta beta_pos pi_ref).
  set (LOGZ := mult beta (log ZAL ZAL_pos)).
  set (FAP := req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp).
  set (FAPI := req2_F_align S sumf reward beta pi_ref pi_ref_pos
                             PSTR PSTR_pos).
  set (KLp := req2_rel_ent S sumf p PSTR Hp PSTR_pos).
  set (KLself := req2_rel_ent S sumf PSTR PSTR PSTR_pos PSTR_pos).
  
  assert (HdecP : req FAP (req_minus (mult beta KLp) LOGZ))
    by exact (r2_F_align_kl_diff S sumf Hext Hadd Hlin Hlog Hinv
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 p Hp Hn).
  (* 2. 同一分解吃在 pistar 处（pistar 归一化 = w_pi_star_normalized） *)
  assert (HPSTRn : req2_norm_one S sumf PSTR)
    by exact (w_pi_star_normalized S sumf Hlin reward beta beta_pos pi_ref
                                   ZAL_pos).
  assert (HdecI : req FAPI (req_minus (mult beta KLself) LOGZ))
    by exact (r2_F_align_kl_diff S sumf Hext Hadd Hlin Hlog Hinv
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 PSTR PSTR_pos HPSTRn).
  (* 3. KL(pistar‖pistar) == 0（w_rel_ent_self_zero）⟹ β·KL(pistar‖pistar) == 0
     ⟹ F(pistar) == −β·log ZAL *)
  assert (Hklself : req KLself zero)
    by exact (w_rel_ent_self_zero S sumf Hext Hlin PSTR PSTR_pos).
  assert (HbK0 : req (mult beta KLself) zero)
    by exact (req_trans (mult beta KLself) (mult beta zero) zero
                 (req_mult_compat beta beta KLself zero (req_refl beta) Hklself)
                 (mult_zero beta)).
  assert (HFAPI : req FAPI (opp LOGZ))
    by exact (req_trans FAPI (req_minus (mult beta KLself) LOGZ) (opp LOGZ) HdecI
         (req_trans (req_minus (mult beta KLself) LOGZ) (req_minus zero LOGZ)
                    (opp LOGZ)
                    (req2_minus_compat (mult beta KLself) zero LOGZ LOGZ
                                       HbK0 (req_refl LOGZ))
                    (req_trans (req_minus zero LOGZ) (plus zero (opp LOGZ))
                               (opp LOGZ)
                               (req_refl (req_minus zero LOGZ))
                               (req_plus_zero_l (opp LOGZ))))).
  (* 4. KL ≥ 0（槽）+ β>0 保序 ⟹ 0 ≤ β·KL(p‖pistar) *)
  assert (Hdkl : le zero (mult beta KLp))
    by exact (r2_le_mult_nonneg beta KLp
                                (lt_le_iff zero beta (inl beta_pos))
                                (Hgibbs p PSTR Hp PSTR_pos)).
  (* 5. F(pistar) ≤ F(pistar) + β·KL == F(p)（le_plus_compat 保左 + 转换完成） *)
  assert (Hfin : le FAPI (plus FAPI (mult beta KLp)))
    by exact (le_id_l FAPI (plus FAPI zero) (plus FAPI (mult beta KLp))
                      (req_sym (plus FAPI zero) FAPI (plus_zero FAPI))
                      (le_plus_compat FAPI FAPI zero (mult beta KLp)
                                      (le_refl FAPI) Hdkl)).
  assert (Hconv : req (plus FAPI (mult beta KLp)) FAP)
    by exact (req_sym FAP (plus FAPI (mult beta KLp))
               (req_trans FAP (req_minus (mult beta KLp) LOGZ)
                          (plus FAPI (mult beta KLp))
                          HdecP
                          (req_trans (req_minus (mult beta KLp) LOGZ)
                                     (plus (mult beta KLp) FAPI)
                                     (plus FAPI (mult beta KLp))
                                     (req_trans (req_minus (mult beta KLp) LOGZ)
                                                (plus (mult beta KLp)
                                                      (opp LOGZ))
                                                (plus (mult beta KLp) FAPI)
                                                (req_refl (req_minus
                                                             (mult beta KLp)
                                                             LOGZ))
                                                (req_plus_compat
                                                   (mult beta KLp)
                                                   (mult beta KLp)
                                                   (opp LOGZ) FAPI
                                                   (req_refl (mult beta KLp))
                                                   (req_sym FAPI (opp LOGZ)
                                                            HFAPI)))
                                     (plus_comm (mult beta KLp) FAPI)))).
  (* 6. 取负（opp 保序）：J(p) = −F(p) ≤ −F(pistar) = J(pistar) *)
  exact (opp_le_compat FAPI FAP
                       (le_id_r FAPI (plus FAPI (mult beta KLp)) FAP
                                Hconv Hfin)).
Qed.

(* ============================================================ *)
(* ReqU2FixedPoint：U2 主体节（节参数与 UpReqAlign3.Req3AlignCore 同骨）        *)
(* ============================================================ *)
Section ReqU2FixedPoint.

Context {RIS : RealInterfaceEnhancedSetoid}.
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.

(* ---- ReqLogBridge 同位桥槽（保底件给出归约与消解） ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
(* ---- req_gibbs_equality 出口桥槽（plain-le 深水区） ---- *)
Hypothesis log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis log_eq_linear :
  forall (x : R) (Hx : lt zero x), req (log x Hx) (req_minus x one) -> req x one.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* ---- 本节局部别名（全部为上游 req2 定义的 δ 透明薄包装，同 UpReqAlign3） ---- *)
Definition pos3 (p : S -> R) : Set := req2_pos_dist S p.
Definition nrm (p : S -> R) : Set := req2_norm_one S sumf p.
Definition AL (s : S) : R :=
  req2_align_energy S reward beta pi_ref pi_ref_pos s.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  req2_rel_ent S sumf p q Hp Hq.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  req2_J S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition FA (p : S -> R) (Hp : pos3 p) : R :=
  req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  req2_pi_next S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition ZAL : R :=
  req2_Z_align S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  req2_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.

(* 透明证人（Set 值关系的证人参数是数据：必须是 Definition，不得
   Qed 包装——否则与上游语句中的原始应用不可转换） *)
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  req2_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.

(* ---- 诚实桥槽（依赖 PSTR/NPX，定义后声明） ---- *)
Hypothesis req2_gibbs_inequality :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    le zero (KLE p q Hp Hq).
(* ---- req_backward_kl_step_le（原假设位 6，已消解降级为使用件——非假设位） ----
   UpReqAlign3 增量结果已证明：req2_backward_kl_step 主定理 + r2_backward_kl_step_le
   （le 形同位件，Id policy_iter_backward_kl_step_le @22790 同位）已落
   本节 req2_gibbs_inequality 槽与 ZAL_pos 证人在参面），@ 全显节参数
   一次喂定，零重证、零适配；U2c 使用点零改动。 *)
Definition req_backward_kl_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
       (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
             (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))) :=
  r2_backward_kl_step_le S sumf
    sum_ext sum_add sum_linear sum_pos
    log_req_compat log_inv_exp_neg_req
    reward beta beta_pos pi_ref pi_ref_pos eta
    eta_pos ZAL_pos req2_gibbs_inequality.
(* ---- rlhf_optimal_seed（原假设位，已消解降级为使用件——非假设位） ----
   FEP 装配消解 = u2_rlhf_optimal_seed_discharge（文件级保底 3）：
   r2_F_align_kl_diff 分解 + w_rel_ent_self_zero + req2_gibbs_inequality 槽
   + β>0 保序 + opp 保序取负（a_rlhf_optimal 手法）。节参数一次喂定，零重证；
   登记表 7 同步改写；U2a/U2e 使用链 Print Assumptions 保持 Closed。 *)
Definition rlhf_optimal_seed :
  forall (p : S -> R) (Hn : nrm p) (Hp : pos3 p),
    le (JJ p Hp) (JJ PSTR PSTR_pos) :=
  u2_rlhf_optimal_seed_discharge  S sumf sum_ext sum_add sum_linear
                                 log_req_compat log_inv_exp_neg_req
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 req2_gibbs_inequality.

(* ---- 见证转换件（正性见证是数据：log 见证进值，FA/JJ 对见证 req 外延。
   在前提见证 ps_pos 世界——经本件转换后完成） ---- *)
Lemma r2u_FA_witness_ext :
  forall (p : S -> R) (Hp Hq : pos3 p), req (FA p Hp) (FA p Hq).
Proof.
  intros p Hp Hq.
  unfold FA, req2_F_align.
  apply (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                         (sumf (fun s => mult (p s) (AL s)))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hq s)))))).
  - exact (req_refl (sumf (fun s => mult (p s) (AL s)))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                           (sumf (fun s => mult (p s) (log (p s) (Hq s))))
                           (req_refl beta)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (p s) (log (p s) (Hq s)))).
    intro s.
    exact (req_mult_compat (p s) (p s) (log (p s) (Hp s)) (log (p s) (Hq s))
                           (req_refl (p s))
                           (log_req_compat (p s) (p s) (Hp s) (Hq s)
                                           (req_refl (p s)))).
Qed.

Lemma r2u_JJ_witness_ext :
  forall (p : S -> R) (Hp Hq : pos3 p), req (JJ p Hp) (JJ p Hq).
Proof.
  intros p Hp Hq.
  exact (req_opp_compat (FA p Hp) (FA p Hq) (r2u_FA_witness_ext p Hp Hq)).
Qed.

(* ---- 上游件使用包装（节参数一次喂定；零重证） ---- *)
Lemma w2_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t), req (sumf (NPX pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  exact (w_pi_next_normalized S sumf sum_linear sum_pos reward beta beta_pos                              pi_ref pi_ref_pos eta pi_t Hpi_t).
Qed.

Lemma w2_pi_star_normalized : req (sumf PSTR) one.
Proof.
  exact (w_pi_star_normalized S sumf sum_linear reward beta beta_pos pi_ref ZAL_pos).
Qed.

Lemma w2_rel_ent_self_zero :
  forall (p : S -> R) (Hp : pos3 p), req (KLE p p Hp Hp) zero.
Proof.
  intros p Hp.
  exact (w_rel_ent_self_zero S sumf sum_ext sum_linear p Hp).
Qed.

Lemma w2_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (JJ pi_t Hpi_t) (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  exact (r2_policy_improvement_mono S sumf sum_ext sum_add sum_linear sum_pos                                    log_req_compat log_inv_exp_neg_req                                    reward beta beta_pos pi_ref pi_ref_pos                                    eta eta_pos eta_le_one                                    req2_gibbs_inequality pi_t Hpi_t Hn).
Qed.

Lemma w2_gap_diff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
        (mult beta
              (plus (mult (req_minus (inv_pos eta eta_pos) one)
                          (KLE (NPX pi_t Hpi_t) pi_t
                               (npx_pos pi_t Hpi_t) Hpi_t))
                    (mult (inv_pos eta eta_pos)
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (r2_gap_diff S sumf sum_ext sum_add sum_linear sum_pos                     log_req_compat log_inv_exp_neg_req                     reward beta beta_pos pi_ref pi_ref_pos eta eta_pos                     pi_t Hpi_t Hn).
Qed.

(* req_gibbs_equality 出口组装：sum_zero_nonneg + log 桥槽一次喂定。
   log_inv_one_inv 假设位以 req_log_inv_one_inv（Algebra ReqLogBridge 成品）
   假设位要求任意 Hi——经 log_req_witness_compat 转换后对齐）。 *)
Lemma w2_gibbs_eq :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    nrm p -> nrm q -> req (KLE p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl0 s.
  exact (req_gibbs_equality S sumf sum_ext sum_add sum_linear sum_zero_nonneg                            (fun (x : R) (Hx : lt zero x)                                     (Hi : lt zero (inv_pos x Hx)) =>                               req_trans (log (inv_pos x Hx) Hi)                                         (log (inv_pos x Hx) (inv_pos_pos x Hx))                                         (opp (log x Hx))                                 (log_req_witness_compat  log_req_compat                                                         (inv_pos x Hx)                                                         Hi (inv_pos_pos x Hx))                                 (req_log_inv_one_inv log_req_compat x Hx))                            log_le_linear log_eq_linear p q Hp Hq                            Hnp Hnq Hkl0 s).
Qed.

(* ============================================================ *)
(* 主体 1：对齐目标对策略逐点 req 外延（Id u2_align_objective_ext @23396 同位） *)
(*   Id 证明：unfold align_objective; id_cong opp; free_energy_ext。           *)
(*   req 对位：JJ ≡ opp(req2_F_align)，FA 外延 = sum_ext + log_req_compat 组装。 *)
(* ============================================================ *)
Theorem req_u2_align_objective_ext :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    (forall s : S, req (p s) (q s)) -> req (JJ p Hp) (JJ q Hq).
Proof.
  intros p q Hp Hq Hpq.
  unfold JJ, req2_J.
  apply (req_opp_compat (req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp)
                        (req2_F_align S sumf reward beta pi_ref pi_ref_pos q Hq)).
  unfold req2_F_align.
  apply (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                         (sumf (fun s => mult (q s) (AL s)))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - apply (sum_ext (fun s => mult (p s) (AL s))
                   (fun s => mult (q s) (AL s))).
    intro s.
    exact (req_mult_compat (p s) (q s) (AL s) (AL s) (Hpq s) (req_refl (AL s))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                           (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                           (req_refl beta)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (q s) (log (q s) (Hq s)))).
    intro s.
    exact (req_mult_compat (p s) (q s) (log (p s) (Hp s)) (log (q s) (Hq s))
                           (Hpq s)
                           (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpq s))).
Qed.

(* ============================================================ *)
(* U2a：pi_star 是单步改进算子 NPX 的不动点                                     *)
(*   （Id u2_pi_next_pi_star_fixed @23425 同位；六步链逐位对应：               *)
(*     夹逼 J 等值 → gap 恒等式 → beta 消去 → 非负性 → 非负和为零 →            *)
(*     gibbs_equality 逐点化）                                                  *)
(* ============================================================ *)
Theorem req_u2_pi_next_pi_star_fixed :
  forall (ps_pos : pos3 PSTR) (ps_norm : nrm PSTR),
    forall s : S, req (NPX PSTR ps_pos s) (PSTR s).
Proof.
  intros ps_pos ps_norm s0.
  set (Np := NPX PSTR ps_pos).
  set (K1 := KLE Np PSTR (npx_pos PSTR ps_pos) ps_pos).
  set (K2 := KLE PSTR Np ps_pos (npx_pos PSTR ps_pos)).
  assert (HNp_norm : nrm Np) by exact (w2_pi_next_normalized PSTR ps_pos).
  (* 1. 夹逼：J(NPX pi_star) <= J(pi_star) 且 J(pi_star) <= J(NPX pi_star)
       PSTR_pos——经 r2u_JJ_witness_ext 转换到 ps_pos 世界后完成） *)
  assert (Hopt : le (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR PSTR_pos))
    by exact (rlhf_optimal_seed Np HNp_norm (npx_pos PSTR ps_pos)).
  assert (HoptR : le (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
    by exact (le_id_r (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR PSTR_pos)
                      (JJ PSTR ps_pos)
                      (r2u_JJ_witness_ext PSTR PSTR_pos ps_pos) Hopt).
  assert (Hmono : le (JJ PSTR ps_pos) (JJ Np (npx_pos PSTR ps_pos)))
    by exact (w2_policy_improvement_mono PSTR ps_pos ps_norm).
  assert (Hjeq : req (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
    by exact (le_antisym _ _ HoptR Hmono).
  assert (Hdiff0 : req (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                  (JJ PSTR ps_pos)) zero)
    by exact (req_minus_self_zero _ _ Hjeq).
  (* 2. gap 恒等式：J(NPX pi_star) − J(pi_star) == beta·[(1/eta−1)·K1 + (1/eta)·K2] *)
  assert (Hgap : req (req_minus (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
                    (mult beta
                          (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2))))
    by exact (w2_gap_diff PSTR ps_pos ps_norm).
  (* 3. beta > 0 消去（req_mult_cancel_l）：括号内 == 0 *)
  assert (HX0 : req (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                          (mult (inv_pos eta eta_pos) K2)) zero).
  { apply (req_mult_cancel_l beta
                             (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                   (mult (inv_pos eta eta_pos) K2))
                             zero beta_pos).
    exact (req_trans (mult beta
                           (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                 (mult (inv_pos eta eta_pos) K2)))
                     (req_minus (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
                     (mult beta zero)
                     (req_sym (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                         (JJ PSTR ps_pos))
                              (mult beta
                                    (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                          (mult (inv_pos eta eta_pos) K2)))
                              Hgap)
                     (req_trans (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                           (JJ PSTR ps_pos))
                                zero
                                (mult beta zero)
                                Hdiff0
                                (req_sym (mult beta zero) zero
                                         (mult_zero beta)))). }
  (* 4. 非负性：(1/eta−1) >= 0（r2_inv_ge_one 一步达）、K1 >= 0、K2 >= 0 *)
  assert (HP : le zero (req_minus (inv_pos eta eta_pos) one))
    by exact (req_le_minus_nonneg one (inv_pos eta eta_pos)
                                  (r2_inv_ge_one eta eta_pos eta_le_one)).
  assert (HK1 : le zero K1)
    by exact (req2_gibbs_inequality Np PSTR (npx_pos PSTR ps_pos) ps_pos).
  assert (HK2 : le zero K2)
    by exact (req2_gibbs_inequality PSTR Np ps_pos (npx_pos PSTR ps_pos)).
  assert (HPK1 : le zero (mult (req_minus (inv_pos eta eta_pos) one) K1))
    by exact (r2_le_mult_nonneg _ _ HP HK1).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2))
    by exact (r2_le_mult_nonneg _ _
             (lt_le_iff zero (inv_pos eta eta_pos) (inl (inv_pos_pos eta eta_pos)))
             HK2).
  (* 5. 非负和为零 => (1/eta)·K2 == 0 =>（1/eta > 0）K2 == 0 *)
  assert (HQK2z : req (mult (inv_pos eta eta_pos) K2) zero).
  { apply (req_u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                                  (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                  HQK2 HPK1).
    exact (req_trans (plus (mult (inv_pos eta eta_pos) K2)
                           (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                           (mult (inv_pos eta eta_pos) K2))
                     zero
                     (plus_comm (mult (inv_pos eta eta_pos) K2)
                                (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     HX0). }
  assert (HK2z : req K2 zero).
  { apply (req_mult_cancel_l (inv_pos eta eta_pos) K2 zero
                             (inv_pos_pos eta eta_pos)).
    exact (req_trans (mult (inv_pos eta eta_pos) K2)
                     zero
                     (mult (inv_pos eta eta_pos) zero)
                     HQK2z
                     (req_sym (mult (inv_pos eta eta_pos) zero) zero
                              (mult_zero (inv_pos eta eta_pos)))). }
  (* 6. gibbs_equality：K2 == 0 => pi_star == NPX pi_star 逐点 => 结论（req_sym） *)
  assert (Hpi : forall s : S, req (PSTR s) (Np s))
    by (intro s;
        exact (w2_gibbs_eq PSTR Np ps_pos (npx_pos PSTR ps_pos)
                           ps_norm HNp_norm HK2z s)).
  exact (req_sym (PSTR s0) (Np s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* U2b：无进展 => 不动点（Id u2_no_progress_fixed_point @23517 同位；           *)
(*   与 U2a 第 3–6 步同构，目标等值直接给出 J 差 == 0，无需夹逼）               *)
(* ============================================================ *)
Theorem req_u2_no_progress_fixed_point :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
    forall s : S, req (NPX pi_t Hpi_t s) (pi_t s).
Proof.
  intros pi_t Hpi_t Hn Hno s0.
  set (Np := NPX pi_t Hpi_t).
  set (K1 := KLE Np pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  assert (HNp_norm : nrm Np) by exact (w2_pi_next_normalized pi_t Hpi_t).
  (* 1. 目标差 == 0（无进展假设） *)
  assert (Hdiff0 : req (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t)) zero)
    by exact (req_minus_self_zero _ _ Hno).
  (* 2. gap 恒等式 *)
  assert (Hgap : req (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
                    (mult beta
                          (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2))))
    by exact (w2_gap_diff pi_t Hpi_t Hn).
  (* 3. beta > 0 消去 *)
  assert (HX0 : req (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                          (mult (inv_pos eta eta_pos) K2)) zero).
  { apply (req_mult_cancel_l beta
                             (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                   (mult (inv_pos eta eta_pos) K2))
                             zero beta_pos).
    exact (req_trans (mult beta
                           (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                 (mult (inv_pos eta eta_pos) K2)))
                     (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
                     (mult beta zero)
                     (req_sym (req_minus (JJ Np (npx_pos pi_t Hpi_t))
                                         (JJ pi_t Hpi_t))
                              (mult beta
                                    (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                          (mult (inv_pos eta eta_pos) K2)))
                              Hgap)
                     (req_trans (req_minus (JJ Np (npx_pos pi_t Hpi_t))
                                           (JJ pi_t Hpi_t))
                                zero
                                (mult beta zero)
                                Hdiff0
                                (req_sym (mult beta zero) zero
                                         (mult_zero beta)))). }
  (* 4. 非负性 *)
  assert (HP : le zero (req_minus (inv_pos eta eta_pos) one))
    by exact (req_le_minus_nonneg one (inv_pos eta eta_pos)
                                  (r2_inv_ge_one eta eta_pos eta_le_one)).
  assert (HK1 : le zero K1)
    by exact (req2_gibbs_inequality Np pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  assert (HK2 : le zero K2)
    by exact (req2_gibbs_inequality pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  assert (HPK1 : le zero (mult (req_minus (inv_pos eta eta_pos) one) K1))
    by exact (r2_le_mult_nonneg _ _ HP HK1).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2))
    by exact (r2_le_mult_nonneg _ _
             (lt_le_iff zero (inv_pos eta eta_pos) (inl (inv_pos_pos eta eta_pos)))
             HK2).
  (* 5. (1/eta)·K2 == 0 => K2 == 0 *)
  assert (HQK2z : req (mult (inv_pos eta eta_pos) K2) zero).
  { apply (req_u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                                  (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                  HQK2 HPK1).
    exact (req_trans (plus (mult (inv_pos eta eta_pos) K2)
                           (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                           (mult (inv_pos eta eta_pos) K2))
                     zero
                     (plus_comm (mult (inv_pos eta eta_pos) K2)
                                (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     HX0). }
  assert (HK2z : req K2 zero).
  { apply (req_mult_cancel_l (inv_pos eta eta_pos) K2 zero
                             (inv_pos_pos eta eta_pos)).
    exact (req_trans (mult (inv_pos eta eta_pos) K2)
                     zero
                     (mult (inv_pos eta eta_pos) zero)
                     HQK2z
                     (req_sym (mult (inv_pos eta eta_pos) zero) zero
                              (mult_zero (inv_pos eta eta_pos)))). }
  (* 6. gibbs_equality：K2 == 0 => pi_t == NPX pi_t 逐点 => 结论（req_sym） *)
  assert (Hpi : forall s : S, req (pi_t s) (Np s))
    by (intro s;
        exact (w2_gibbs_eq pi_t Np Hpi_t (npx_pos pi_t Hpi_t)
                           Hn HNp_norm HK2z s)).
  exact (req_sym (pi_t s0) (Np s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* U2c：不动点唯一 => pi_star（Id u2_fixed_point_unique @23576 同位）           *)
(*   证明：Hfix 同余换形 KLE(pi_star‖NPX) == A、KLE(pi_t‖NPX) == 0；            *)
(*     向后 KL 单步 <=（使用件 req_backward_kl_step_le，原槽 6 已消解）         *)
(*     化简为 A <= (1−eta)·A；                                                   *)
(*     Hma：(1−eta)·A == A − eta·A，故 A <= A − eta·A；u2_minus_minus 与        *)
(*     req_le_minus_nonneg 得 0 <= −eta·A，opp 保序两次反号得 eta·A <= 0；      *)
(*     req2_gibbs 槽给 0 <= A => 夹逼 eta·A == 0 =>（eta > 0 消去）A == 0 =>    *)
(*     w2_gibbs_eq 逐点化 => pi_t == pi_star 逐点。                             *)
(* ============================================================ *)
Theorem req_u2_fixed_point_unique :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    (forall s : S, req (NPX pi_t Hpi_t s) (pi_t s)) ->
    forall s : S, req (pi_t s) (PSTR s).
Proof.
  intros pi_t Hpi_t Hn Hfix s0.
  set (Np := NPX pi_t Hpi_t).
  set (A := KLE PSTR pi_t PSTR_pos Hpi_t).
  set (ANp := KLE PSTR Np PSTR_pos (npx_pos pi_t Hpi_t)).
  set (TNp := KLE pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  (* 1. 同余换形：KL(pi_star‖Np) == A 且 KL(pi_t‖Np) == 0 *)
  assert (Hc1 : req ANp A)
    by exact (req_u2_kl_arg2_ext  S sumf sum_ext log_req_compat
                                 PSTR Np pi_t PSTR_pos
                                 (npx_pos pi_t Hpi_t) Hpi_t Hfix).
  assert (Hc2 : req TNp (KLE pi_t pi_t Hpi_t Hpi_t))
    by exact (req_u2_kl_arg2_ext  S sumf sum_ext log_req_compat
                                 pi_t Np pi_t Hpi_t
                                 (npx_pos pi_t Hpi_t) Hpi_t Hfix).
  assert (HC0 : req TNp zero)
    by exact (req_trans TNp (KLE pi_t pi_t Hpi_t Hpi_t) zero Hc2
                         (w2_rel_ent_self_zero pi_t Hpi_t)).
  (* 2. 向后 KL 单步（<= 桥槽）：KL(pi_star‖Np) <= (1−eta)·A + KL(pi_t‖Np) *)
  assert (H1 : le ANp (plus (mult (req_minus one eta) A) TNp))
    by exact (req_backward_kl_step_le pi_t Hpi_t Hn).
  assert (H3 : le A (plus (mult (req_minus one eta) A) TNp))
    by exact (le_id_l A ANp (plus (mult (req_minus one eta) A) TNp)
                       (req_sym ANp A Hc1) H1).
  assert (H4 : req (plus (mult (req_minus one eta) A) TNp)
                   (mult (req_minus one eta) A)).
  { exact (req_trans (plus (mult (req_minus one eta) A) TNp)
                     (plus (mult (req_minus one eta) A) zero)
                     (mult (req_minus one eta) A)
                     (req_plus_compat (mult (req_minus one eta) A)
                                      (mult (req_minus one eta) A)
                                      TNp zero
                                      (req_refl (mult (req_minus one eta) A))
                                      HC0)
                     (plus_zero (mult (req_minus one eta) A))). }
  assert (HleA : le A (mult (req_minus one eta) A))
    by exact (le_id_r A (plus (mult (req_minus one eta) A) TNp)
                      (mult (req_minus one eta) A) H4 H3).
  (* 3. (1−eta)·A == A − eta·A，故 A <= A − eta·A *)
  assert (Hma : req (mult (req_minus one eta) A) (req_minus A (mult eta A))).
  { exact (req_trans (mult (req_minus one eta) A)
                     (req_minus (mult one A) (mult eta A))
                     (req_minus A (mult eta A))
                     (req_mult_minus_distr_r one eta A)
                     (req2_minus_compat (mult one A) A (mult eta A) (mult eta A)
                                        (req_trans (mult one A) (mult A one) A
                                                   (mult_comm one A)
                                                   (mult_one A))
                                        (req_refl (mult eta A)))). }
  assert (HleB : le A (req_minus A (mult eta A)))
    by exact (le_id_r A (mult (req_minus one eta) A)
                      (req_minus A (mult eta A)) Hma HleA).
  (* 4. 0 <= −eta·A（req_le_minus_nonneg + (A − eta·A) − A == −eta·A） *)
  assert (Hz1 : le zero (req_minus (req_minus A (mult eta A)) A))
    by exact (req_le_minus_nonneg A (req_minus A (mult eta A)) HleB).
  assert (Hz2 : le zero (opp (mult eta A))).
  { exact (le_id_r zero (req_minus (req_minus A (mult eta A)) A)
                   (opp (mult eta A))
                   (req_u2_minus_minus A (mult eta A)) Hz1). }
  (* 5. eta·A <= 0（opp 保序两次反号；opp zero == zero 自证） *)
  assert (Hoppz : req (opp zero) zero).
  { exact (req_plus_cancel_l zero (opp zero) zero
             (req_trans (plus zero (opp zero)) zero (plus zero zero)
                        (plus_opp zero)
                        (req_sym (plus zero zero) zero (plus_zero zero)))). }
  assert (Hopp0 : le (opp (opp (mult eta A))) (opp zero))
    by exact (opp_le_compat zero (opp (mult eta A)) Hz2).
  assert (Hopp1 : le (opp (opp (mult eta A))) zero)
    by exact (le_id_r (opp (opp (mult eta A))) (opp zero) zero Hoppz Hopp0).
  assert (Heta_le0 : le (mult eta A) zero)
    by exact (le_id_l (mult eta A) (opp (opp (mult eta A))) zero
                      (req_sym (opp (opp (mult eta A))) (mult eta A)
                               (req_double_neg (mult eta A)))
                      Hopp1).
  (* 6. 0 <= eta·A（req2_gibbs 槽：0 <= A；eta >= 0 => 0 <= eta·A） *)
  assert (HA0 : le zero A)
    by exact (req2_gibbs_inequality PSTR pi_t PSTR_pos Hpi_t).
  assert (Heta0 : le zero eta)
    by exact (lt_le_iff zero eta (inl eta_pos)).
  assert (HX0 : le zero (mult eta A))
    by exact (r2_le_mult_nonneg eta A Heta0 HA0).
  (* 7. eta·A == 0 =>（eta > 0 消去）A == 0 => w2_gibbs_eq => pi_t == pi_star *)
  assert (HXz : req (mult eta A) zero)
    by exact (req_sym zero (mult eta A)
                      (le_antisym zero (mult eta A) HX0 Heta_le0)).
  assert (HAz : req A zero).
  { exact (req_mult_cancel_l eta A zero eta_pos
             (req_trans (mult eta A) zero (mult eta zero) HXz
                        (req_sym (mult eta zero) zero (mult_zero eta)))). }
  assert (HPSTRn : nrm PSTR) by exact w2_pi_star_normalized.
  assert (Hpi : forall s : S, req (PSTR s) (pi_t s))
    by (intro s;
        exact (w2_gibbs_eq PSTR pi_t PSTR_pos Hpi_t HPSTRn Hn HAz s)).
  exact (req_sym (PSTR s0) (pi_t s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* 推论：无进展 => 已最优（Id u2_no_progress_optimal @23718 同位；              *)
(*   U2b + U2c 组装）                                                           *)
(* ============================================================ *)
Theorem req_u2_no_progress_optimal :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
    forall s : S, req (pi_t s) (PSTR s).
Proof.
  intros pi_t Hpi_t Hn Hno s0.
  assert (Hfp : forall s : S, req (NPX pi_t Hpi_t s) (pi_t s))
    by (intro s; exact (req_u2_no_progress_fixed_point pi_t Hpi_t Hn Hno s)).
  exact (req_u2_fixed_point_unique pi_t Hpi_t Hn Hfp s0).
Qed.

(* ============================================================ *)
(* 反向：已最优 => 无进展（Id u2_optimal_no_progress @23737 同位；              *)
(*   逐点相等 + 目标外延 => J(pi_t) == J(pi_star)；rlhf 槽 + mono 夹逼）        *)
(* ============================================================ *)
Theorem req_u2_optimal_no_progress :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    (forall s : S, req (pi_t s) (PSTR s)) ->
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hn Hpi.
  assert (HNp_norm : nrm (NPX pi_t Hpi_t))
    by exact (w2_pi_next_normalized pi_t Hpi_t).
  assert (Hext : req (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos))
    by exact (req_u2_align_objective_ext pi_t PSTR Hpi_t PSTR_pos Hpi).
  assert (Hopt : le (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ PSTR PSTR_pos))
    by exact (rlhf_optimal_seed (NPX pi_t Hpi_t) HNp_norm
                                (npx_pos pi_t Hpi_t)).
  assert (Hmono : le (JJ pi_t Hpi_t)
                     (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
    by exact (w2_policy_improvement_mono pi_t Hpi_t Hn).
  assert (Hle1 : le (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ pi_t Hpi_t))
    by exact (le_id_r (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                      (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)
                      (req_sym (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos) Hext)
                      Hopt).
  exact (le_antisym (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ pi_t Hpi_t) Hle1 Hmono).
Qed.

(* ============================================================ *)
(* 等值刻画（双向，Set 层 And := A*B 乘积；Id u2_objective_eq_optimal_iff       *)
(* @23769 同位）                                                                *)
(* ============================================================ *)
Theorem req_u2_objective_eq_optimal_iff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
  And (req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
        forall s : S, req (pi_t s) (PSTR s))
      ((forall s : S, req (pi_t s) (PSTR s)) ->
        req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  split.
  - intro H. exact (req_u2_no_progress_optimal pi_t Hpi_t Hn H).
  - intro H. exact (req_u2_optimal_no_progress pi_t Hpi_t Hn H).
Qed.

End ReqU2FixedPoint.
