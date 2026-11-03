(* ConstructiveWorld-Set — finite merge group: log/exp primitive proof lemmas. *)

(** * G05_LogSmall: merged statement family for log/exp primitive proof
      lemmas (series G5, [logd_] prefix).

    Mission.  A finite merge group (members merged verbatim) carrying the
      log/exp primitive proof lemmas of series G5 (the [logd_] family):
      the unconditional request-layer reduction lattice, positivity
      transport, compatibility slots, and the Real-layer unconditional
      closures ([logd_log_compat_real], [logd_log_exp_neg_real],
      [logd_log_inv_one_inv_real], [logd_log_inv_exp_neg_real],
      [logd_log_witness_real], [logd_exp_neg_ext_real]).

    Dependencies.  The library files listed in the Require face below.

    References.  Elementary log/exp identities over constructive reals
      (monotonicity, inverse cancellation, exponential laws).

    Constructivity.  All proofs close by [Qed]; zero admission words; no
      classical axioms; the statement face is carried by the [Set] layer
      (all conclusions are [req]/[lt]/[le] interface values, zero Prop
      leakage).

    Build.  [coqc -native-compiler no -q -Q . "" G05_LogSmall.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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
Notation req_opp_compat := RealSetoid.real_eq_opp_compat.
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_assoc := real_plus_assoc.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation plus_opp := real_plus_opp.
Notation mult_comm := real_mult_comm.
Notation le_antisym := real_le_antisym.
Notation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation inv_pos := real_inv_pos.
Notation inv_pos_correct := real_inv_pos_correct.
Notation one_pos := real_lt_zero_one.
Notation mult_positive := real_mult_positive.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation exp_neg_plus := real_exp_neg_plus.
Notation exp_neg_le_decr := real_exp_neg_le_decr.
Notation log := real_log.
Notation log_mult := real_log_mult.
Notation log_one := real_log_one.
Notation log_inv := real_log_inv.
Notation log_inv_log := real_log_inv_log.
Notation exp_neg_log_inv := real_exp_neg_log_inv.

(* ============================================================ *)
(* Part 0：req 代数小件（接口字段纯推导，零 destruct）                 *)
(* ============================================================ *)

(* P0-a：req ⟹ le（lt_le_iff 右支；req 层单向升格基元，本文件新发现——
   与 real_le→real_le_b 同为单向，逆向 Or 闭合不可证不动） *)
Lemma logd_req_to_le : forall 
    (x y : R), req x y -> le x y.
Proof.
  intros x y H.
  exact (lt_le_iff x y (inr H)).
Qed.

(* P0-b：加法左零（zero + a ≡ a；plus_zero 右零形经 comm 换位） *)
Lemma logd_req_plus_zero_l : forall 
    (a : R), req (plus zero a) a.
Proof.
  intros a.
  apply (req_trans (plus zero a) (plus a zero) a).
  - exact (plus_comm zero a).
  - exact (plus_zero a).
Qed.

(* P0-c：opp 对合（opp (opp a) ≡ a；plus_opp 双例 + assoc/comm/zero 链） *)
Lemma logd_req_opp_opp : forall 
    (a : R), req (opp (opp a)) a.
Proof.
  intros a.
  assert (H1 : req (plus (opp a) (opp (opp a))) zero) by exact (plus_opp (opp a)).
  assert (H2 : req (plus a (opp a)) zero) by exact (plus_opp a).
  apply (req_trans (opp (opp a)) (plus zero (opp (opp a))) a).
  - apply req_sym. exact (logd_req_plus_zero_l  (opp (opp a))).
  - apply (req_trans (plus zero (opp (opp a)))
                     (plus (plus a (opp a)) (opp (opp a))) a).
    + apply (req_plus_compat zero (plus a (opp a)) (opp (opp a)) (opp (opp a))).
      * apply req_sym. exact H2.
      * apply req_refl.
    + apply (req_trans (plus (plus a (opp a)) (opp (opp a)))
                       (plus a (plus (opp a) (opp (opp a)))) a).
      * apply req_sym. exact (plus_assoc a (opp a) (opp (opp a))).
      * apply (req_trans (plus a (plus (opp a) (opp (opp a))))
                         (plus a zero) a).
        -- apply (req_plus_compat a a (plus (opp a) (opp (opp a))) zero
                    (req_refl a) H1).
        -- exact (plus_zero a).
Qed.

(* P0-d：加法右零消去（a + b ≡ zero ⟹ b ≡ opp a） *)
Lemma logd_req_plus_zero_r : forall 
    (a b : R), req (plus a b) zero -> req b (opp a).
Proof.
  intros a b H.
  apply (req_trans b (plus zero b) (opp a)).
  - apply req_sym. exact (logd_req_plus_zero_l  b).
  - apply (req_trans (plus zero b) (plus (plus (opp a) a) b) (opp a)).
    + apply (req_plus_compat zero (plus (opp a) a) b b).
      * apply req_sym.
        apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
        -- exact (plus_comm (opp a) a).
        -- exact (plus_opp a).
      * apply req_refl.
    + apply (req_trans (plus (plus (opp a) a) b)
                       (plus (opp a) (plus a b)) (opp a)).
      * apply req_sym. exact (plus_assoc (opp a) a b).
      * apply (req_trans (plus (opp a) (plus a b))
                         (plus (opp a) zero) (opp a)).
        -- apply (req_plus_compat (opp a) (opp a) (plus a b) zero
                    (req_refl (opp a)) H).
        -- exact (plus_zero (opp a)).
Qed.

(* ============================================================ *)
(* Part 1：接口层基元（泛型 RIS；条件形供给槽显式位）                    *)
(* ============================================================ *)

(* P1-a：exp_neg 对 req 兼容——接口层无条件真定理（证明
   req_exp_neg_ext@UpSigMigrate:521 整族）。
   路线：req 经 lt_le_iff 右支升 le 双向，exp_neg_le_decr 反向各得一支，
   le_antisym 闭合。全接口字段，零额外供给。 *)
Lemma logd_exp_neg_ext : forall 
    (x y : R), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le  y x).
    exact (req_sym x y Hxy).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le  x y).
    exact Hxy.
Qed.

(* P1-b：lt 正性沿 req 运输（req_lt_compat 零点特化） *)
Lemma logd_lt_req_transport : forall 
    (a b : R), req a b -> lt zero a -> lt zero b.
Proof.
  intros a b H Hlt.
  exact (req_lt_compat zero zero a b (req_refl zero) H Hlt).
Qed.

(* P1-c：逐点正性运输（证明 expf_pos@UpReqFEPAttn:264——条件证明，
   供给槽 = expf_agree（req (expf x) (exp_pos_fn_setoid x)）+
   exp_pos_fn_setoid 正性（exp_neg 族字段直推）。expf_agree 本身 =
   expf 抽象算子的规格（N 槽，不可证明），见判定表。） *)
Lemma logd_pos_of_agree : forall 
    (ef tgt : R -> R),
  (forall x : R, req (ef x) (tgt x)) ->
  (forall x : R, lt zero (tgt x)) ->
  forall x : R, lt zero (ef x).
Proof.
  intros ef tgt Hagree Hpos x.
  apply (logd_lt_req_transport  (tgt x) (ef x)).
  - apply req_sym. exact (Hagree x).
  - exact (Hpos x).
Qed.

(* P2-a：log 相容 ⟸ log 单调 le 单槽（UpReqU2 log_req_compat 同位先例，
   logd_ 独立重建；req 升 le 双向 + le_antisym 闭合） *)
Lemma logd_log_compat_of_mono :
  
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

(* P2-b：log(1/x) ≡ −log x ⟸ log 相容槽（log_mult 分解 + 相容运输至
   log one + 加法零消去；UpReqFEPAttn/UpReqDist 同名槽的归约件） *)
Lemma logd_log_inv_one_inv_of_compat :
  
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)) ->
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros Hcompat x Hx Hi.
  assert (Hponelt : lt zero one) by exact one_pos.
  assert (Hprod : req (mult (inv_pos x Hx) x) one).
  { apply (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one).
    - exact (mult_comm (inv_pos x Hx) x).
    - exact (inv_pos_correct x Hx). }
  assert (Hlog1 : req (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x Hi Hx)) zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                       (mult_positive (inv_pos x Hx) x Hi Hx))
                     (log one one_pos) zero).
    - exact (Hcompat (mult (inv_pos x Hx) x) one
               (mult_positive (inv_pos x Hx) x Hi Hx) one_pos Hprod).
    - exact (log_one one_pos). }
  assert (Hdec : req (plus (log (inv_pos x Hx) Hi) (log x Hx)) zero).
  { exact (req_trans (plus (log (inv_pos x Hx) Hi) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                        (mult_positive (inv_pos x Hx) x Hi Hx)) zero
                     (req_sym (log (mult (inv_pos x Hx) x)
                            (mult_positive (inv_pos x Hx) x Hi Hx))
                        (plus (log (inv_pos x Hx) Hi) (log x Hx))
                        (log_mult (inv_pos x Hx) x Hi Hx))
                     Hlog1). }
  apply (req_sym (opp (log x Hx)) (log (inv_pos x Hx) Hi)).
  apply (req_trans (opp (log x Hx)) (opp (opp (log (inv_pos x Hx) Hi)))
                   (log (inv_pos x Hx) Hi)).
  - apply req_sym.
    apply req_opp_compat.
    apply req_sym.
    exact (logd_req_plus_zero_r  (log (inv_pos x Hx) Hi) (log x Hx) Hdec).
  - exact (logd_req_opp_opp  (log (inv_pos x Hx) Hi)).
Qed.

(* P2-c：log_inv∘exp_neg ≡ id ⟸ log∘exp_neg ≡ −id 槽
   （log_inv_log 换形 + opp 对合；对内互归约之正向） *)
Lemma logd_log_inv_exp_neg_of_log_exp_neg :
  
  (forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u)) ->
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intros Hlen x.
  apply (req_trans (log_inv (exp_neg x) (exp_neg_pos x))
                   (opp (log (exp_neg x) (exp_neg_pos x))) x).
  - exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - apply (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                     (opp (opp x)) x).
    + apply req_opp_compat. exact (Hlen x).
    + exact (logd_req_opp_opp  x).
Qed.

(* P2-d：log∘exp_neg ≡ −id ⟸ log_inv∘exp_neg ≡ id 槽（P2-c 逆向对称；
   二槽对内互推，对外任一为根供给——Real 层根 = real_log_exp_neg@42231） *)
Lemma logd_log_exp_neg_of_log_inv_exp_neg :
  
  (forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intros Hinv x.
  apply (req_sym (opp x) (log (exp_neg x) (exp_neg_pos x))).
  apply (req_trans (opp x) (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (log (exp_neg x) (exp_neg_pos x))).
  - apply req_opp_compat.
    apply (req_trans x (log_inv (exp_neg x) (exp_neg_pos x))
                      (opp (log (exp_neg x) (exp_neg_pos x)))).
    + apply req_sym. exact (Hinv x).
    + exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - exact (logd_req_opp_opp  (log (exp_neg x) (exp_neg_pos x))).
Qed.

(* ============================================================ *)
(* Part 2：Real 层无条件闭合（ 模板②槽形；CW_ConstructiveWorld_219 根基元直接提供）           *)
(* ============================================================ *)

(* B1-a：log 参数 req 兼容（mono 链形：real_log_le_mono@CW_ConstructiveWorld_219:112106 直接提供
   P2-a；证明族 log_req_compat 等 15 槽） *)
Lemma logd_log_compat_real : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (logd_log_compat_of_mono
           (fun (a b : Real) (Ha : lt zero a) (Hb : lt zero b)
              (Hab : le a b) => real_log_le_mono a b Ha Hb Hab)).
  exact Hxy.
Qed.

(* B1-b：同语句双形（real_log_wd@CW_ConstructiveWorld_219:42277 直接提供；殊途同归，双形并存） *)
Lemma logd_log_compat_real_wd : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* B2：log(e^{-x}) ≡ −x（real_log_exp_neg@CW_ConstructiveWorld_219:42231 逐字同形直接提供；
   证明族 log_exp_neg/dist_log_exp_neg/b_log_exp_neg/req_log_exp_neg
   = 6 槽；Real 层根供给，P2-c/d 之对外根） *)
Lemma logd_log_exp_neg_real : forall (x : Real),
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (real_log_exp_neg x).
Qed.

(* B3：log(1/x) ≡ −log x（P2-b 组装 B1；证明族 log_inv_one_inv(2)/
   dist_log_inv_one_inv(3) = 5 槽；UpStepKL kl_log_inv@574 cw_log 形
   同形先例，本件 req 槽形独立组装） *)
Lemma logd_log_inv_one_inv_real : forall (x : Real) (Hx : lt zero x)
    (Hi : lt zero (inv_pos x Hx)),
  req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_of_compat
           logd_log_compat_real x Hx Hi).
Qed.

(* B4：log_inv(e^{-x}) ≡ x（P2-c 组装 B2；证明族 log_inv_exp_neg_req(5)/
   ralt_log_inv_exp_neg_req/rdl_log_inv_exp_neg_req = 7 槽） *)
Lemma logd_log_inv_exp_neg_real : forall (x : Real),
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  apply (logd_log_inv_exp_neg_of_log_exp_neg).
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* B5：log 见证无关（同点双正性见证转换 req 形；UpReqU2
   log_req_witness_compat 同位双形；Real 层根 = real_log_proof_irrel@42291） *)
Lemma logd_log_witness_real : forall (x : Real) (Hx Hx' : lt zero x),
  req (log x Hx) (log x Hx').
Proof.
  intros x Hx Hx'.
  exact (logd_log_compat_real x x Hx Hx' (req_refl x)).
Qed.

(* B6：exp_neg 外延 Real 实例化（P1-a 模板②特化，与 UpSigMigrate:521
   槽形逐位同形） *)
Lemma logd_exp_neg_ext_real : forall (x y : Real), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y H.
  exact (logd_exp_neg_ext x y H).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全部主证明件 Print Assumptions）                   *)
(* ============================================================ *)
Print Assumptions logd_exp_neg_ext.
Print Assumptions logd_pos_of_agree.
Print Assumptions logd_log_compat_of_mono.
Print Assumptions logd_log_inv_one_inv_of_compat.
Print Assumptions logd_log_inv_exp_neg_of_log_exp_neg.
Print Assumptions logd_log_exp_neg_of_log_inv_exp_neg.
Print Assumptions logd_log_compat_real.
Print Assumptions logd_log_compat_real_wd.
Print Assumptions logd_log_exp_neg_real.
Print Assumptions logd_log_inv_one_inv_real.
Print Assumptions logd_log_inv_exp_neg_real.
Print Assumptions logd_log_witness_real.
Print Assumptions logd_exp_neg_ext_real.

(* ======== G05_LogSmall 成员件：UpReqLogLinD（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqLogLinD.v —— 假设位证明系列 #2：log_le_linear 四站点同构族扫清      *)
(*   （承 E-GIBBSD-1：上游会话 G08_Gibbs.v Part A/C 缺口件跨模块复用）    *)
(* ------------------------------------------------------------------ *)
(*   站点 1  UpReqU2.v         L313  Hypothesis log_le_linear          *)
(*   站点 2  UpReqFEPAttn.v    L90   Hypothesis log_le_linear          *)
(*   站点 3  UpReqTempEntropy.v L60  Hypothesis dist_log_le_linear     *)
(*   站点 4  UpFirewallReq.v   L101  Variable  dist_log_le_linear      *)
(*   四槽语句逐字同形：forall x Hx, le (log x Hx) (req_minus x one)。   *)
(* ------------------------------------------------------------------ *)
(*   槽输出序为接口 le（RealEnhancedReal 实例 le 字段 := real_le，      *)
(*   CW_ConstructiveWorld_219:41130 Or 编码）；B 形引擎 real_log_le_linear_B               *)
(*   （UpRealLeB:535）输出 real_le_b（Bishop 形）。逆向桥              *)
(*   real_le_b → real_le 即 Or 形精确闭合，构造性不可证                  *)
(*   （UpRealLeB 尾注登记表；上游会话 系列工作 #1 同判定）。按普查 §380 落点      *)
(*   纪律，四站点证明件一律升格为「Real 实例化定理」：序以 real_le_b    *)
(*   给出，参数位由引擎直接提供；若接口扩展批补 le_b 形参数位，本文件四件     *)
(*   给定形直连（零改动）。                                             *)
(* ------------------------------------------------------------------ *)
(*   站点 1：w2_gibbs_eq @UpReqU2:477 → req_gibbs_equality              *)
(*           @UpReqDist:2148（槽+log_eq_linear 双参数位）。              *)
(*   站点 2：req_attention_minimizes_free_energy_unique @UpReqFEPAttn:  *)
(*           211 → req_min_free_energy_is_boltzmann（≤ 肢，参数位）+      *)
(*           req_free_energy_min_unique（唯一肢，槽+eq_linear 双位）。   *)
(*   站点 3：件 2/件 4（L554/L592）使用 req_gibbs_inequality（参数位）；  *)
(*           件 5（L593）使用 req_gibbs_equality（槽+eq_linear 双位）。  *)
(*   站点 4：件 5/件 6（L312/L378）使用 @req_gibbs_inequality（参数位，   *)
(*           (fw_bt t1, fw_bt t2) 温度对）。                             *)
(* 阻塞裁决（兜底，逐站如实报）：                                        *)
(*   a. 四站点下游终局件（gibbs_equality / min_energy_unique）全量       *)
(*      Real 复演共同卡两缺件，本文件零越权：                              *)
(*      (i)  E-GIBBSD-2 边界——下游 KL 项为 p·(log p−log q) 形           *)
(*           （req2_rel_ent @UpReqAlign2:111 / req_relative_entropy     *)
(*           同形），与 real_kl_term 规范形恒等需 log 逆消去             *)
(*           （log(inv p)==−log p），CW_ConstructiveWorld_219 未备；                       *)
(*      (ii) req 层 fsum_zero_nonneg 的 Bishop 对位（Σd==0 + 逐点        *)
(*           0 ≤_B d ⟹ d s==0）需 In-machinery 部分和机，Part A/C 未备。*)
(*   b. 抽象 sumf 下游定理 @ 实例化路同判 ZPosD 档：real_list_sum_pos   *)
(*      携非空 datum 前提（CW_ConstructiveWorld_219:41666），无法喂抽象 fsum_pos 参数位    *)
(*      （δ 前提形不匹配）——故站点 3/4 温度对以本文件 BTReal 节具体     *)
(*      重放（判例装法先例）。                                          *)
(*   c. datum 非空前提为既有先例签名形（zposd_Z_pos @G12_ZPosFam:82      *)
(*      「Not (enum = nil) 基座 Set 版 Not」，CW_ConstructiveWorld_219 real_list_sum_pos    *)
(*      同位），零放大主张。                                             *)
(* ------------------------------------------------------------------ *)
(* 给出：                                                              *)
(*   [共享地基层] lld_lt_zero_sub_r / lld_le_b_zero_sub——              *)
(*     lt 减形正性 + Bishop 序减形升格（Part A 缺口延伸 2 件）。         *)
(*   [四站点给定件] lld_{u2,fep,tempent,fw}_log_le_linear_B——四站点    *)
(*     槽的 Real 实例化 Bishop 形（引擎直接提供，同构四连）。                *)
(*   [站点 1] lld_u2_gibbs_eq_step1_B——req_gibbs_equality 首步肢       *)
(*     （Hd_nonneg：0 ≤ d(s) 逐点）Bishop 形，gibbsd_gibbs_pointwise_B  *)
(*     一次给定。                                                        *)
(*   [站点 2] FEPReal 节：softmax/boltzmann carrier对 Real 具体形          *)
(*     （base/invT/Zf/softmax/boltz 五 Definition 逐位同构站点参数位，  *)
(*     datum 形）+ 逐点正性 3 件 + lld_fep_softmax_boltz_pointwise_B    *)
(*     （件 4 主定理carrier对的范式实例位）。                                 *)
(*   [站点 3] BTReal 节温度 Boltzmann 族（lld_btz/lld_bt 具体形 +       *)
(*     正性/归一化）+ lld_tempent_kl_nonneg_B（L554 肢 Bishop 形）+     *)
(*     lld_tempent_entropy_neg_sum_B（req_entropy_neg_sum 使用位        *)
(*     eq 伴随件，实_list_sum 层）。                                     *)
(*   [站点 4] lld_fw_kl_boltz_pair_nonneg_B——件 5/件 6 Hkl/Hkl21 肢    *)
(*     （req_gibbs_inequality 温度对）Bishop 形。                        *)
(*   / le_b_id_l / minus_flip / le_b_mult_pos_r）+ Part C 和层机六件    *)
(*   经本系列工作下游裁决面全数消解可复用性；Part D 范本 D0 直接提供形于四站点   *)
(*   给定件逐字复演。                                                    *)
(* 红线：Set 层零 Prop（real_le_b / real_eq / real_lt 全 Set 值； datum  *)
(*   前提为 zposd 先例口径单列）；全 Qed 闭合；零公理；既有文件零改；    *)
(*   lld_ 前缀全库防同名冲突（建前 grep 实测零命中）。                         *)
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
Require Import UpRealLeB.
Require Import G08_Gibbs.
Require Import UpReqU2.
Require Import UpReqFEPAttn.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part H：共享地基层（Part A 缺口延伸 2 件）                            *)
(* ============================================================ *)

(* H1：lt 减形正性：a < c ⟹ 0 < c − a（Bishop 减形入口） *)
Lemma lld_lt_zero_sub_r : forall a c : Real,
  real_lt a c -> real_lt real_zero (real_plus c (real_opp a)).
Proof.
  intros a c Hac.
  apply (RealSetoid.real_lt_compat
           (real_plus (real_opp a) a) real_zero
           (real_plus (real_opp a) c) (real_plus c (real_opp a))).
  - apply (real_eq_trans (real_plus (real_opp a) a)
                         (real_plus a (real_opp a)) real_zero).
    + exact (real_plus_comm (real_opp a) a).
    + exact (real_plus_opp a).
  - exact (real_plus_comm (real_opp a) c).
  - exact (real_lt_plus_translate (real_opp a) a c Hac).
Qed.

(* H2：Bishop 序减形升格：a ≤_B b ⟹ 0 ≤_B b − a                          *)
(*   （站点 1 step1 肢的引擎位；swap_mid + plus_zero 换形闭合）           *)
Lemma lld_le_b_zero_sub : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H. unfold real_le_b. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           real_zero real_zero
           (real_plus (real_plus b eps) (real_opp a))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply real_eq_refl.
  - exact (real_eq_trans
             (real_plus (real_plus b eps) (real_opp a))
             (real_plus (real_plus b eps) (real_plus (real_opp a) real_zero))
             (real_plus (real_plus b (real_opp a)) eps)
             (RealSetoid.real_eq_plus_compat
                (real_plus b eps) (real_opp a)
                (real_plus b eps) (real_plus (real_opp a) real_zero)
                (real_eq_refl (real_plus b eps))
                (real_eq_sym (real_plus (real_opp a) real_zero)
                             (real_opp a)
                             (real_plus_zero (real_opp a))))
             (real_eq_trans
                (real_plus (real_plus b eps)
                           (real_plus (real_opp a) real_zero))
                (real_plus (real_plus b (real_opp a))
                           (real_plus eps real_zero))
                (real_plus (real_plus b (real_opp a)) eps)
                (real_plus_swap_mid b eps (real_opp a) real_zero)
                (RealSetoid.real_eq_plus_compat
                   (real_plus b (real_opp a)) (real_plus eps real_zero)
                   (real_plus b (real_opp a)) eps
                   (real_eq_refl (real_plus b (real_opp a)))
                   (real_plus_zero eps)))).
  - exact (lld_lt_zero_sub_r a (real_plus b eps) (H eps Heps)).
Qed.

(* ============================================================ *)
(* Part S：四站点给定件（槽的 Real 实例化 Bishop 形，同构四连）           *)
(*   四槽语句逐字同形（E-GIBBSD-1 坐标 源码实读），给定形同构——          *)
(* ============================================================ *)

(* 站点 1（UpReqU2.v L313 log_le_linear）给定形 *)
Lemma lld_u2_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 2（UpReqFEPAttn.v L90 log_le_linear）给定形 *)
Lemma lld_fep_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 3（UpReqTempEntropy.v L60 dist_log_le_linear）给定形 *)
Lemma lld_tempent_log_le_linear_B :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 4（UpFirewallReq.v L101 dist_log_le_linear）给定形 *)
Lemma lld_fw_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part U2：站点 1（UpReqU2.v L313）下游首步肢                           *)
(*   槽使用位 w2_gibbs_eq（UpReqU2:477）→ req_gibbs_equality            *)
(*   （UpReqDist:2148）首步 Hd_nonneg：0 ≤ d(s) 逐点（req le 形）——     *)
(*   Bishop 形由 gibbsd_gibbs_pointwise_B（Part D 范本 D0）+ H2 升格。   *)
(*   终局复演阻塞裁决见头注 a(i)(ii)。                                   *)
(* ============================================================ *)

Lemma lld_u2_gibbs_eq_step1_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b real_zero
    (real_plus (real_kl_term (p s) (q s) Hps Hqs)
               (real_opp (real_plus (p s) (real_opp (q s))))).
Proof.
  intros X p q s Hps Hqs.
  apply lld_le_b_zero_sub.
  exact (gibbsd_gibbs_pointwise_B X p q s Hps Hqs).
Qed.

(* ============================================================ *)
(* Part FEP：站点 2（UpReqFEPAttn.v L90）carrier对具体形                     *)
(*   站点节参数（base/invT/Zf/softmax_z/boltz_z，UpReqFEPAttn:107-121）  *)
(*   逐位 Real 同构；sumf := real_list_sum（datum 形，zposd 先例口径）； *)
(*   exp_pos_fn_setoid y == exp_neg (opp y)（CW_ConstructiveWorld_219:66191）——站点        *)
(*   softmax 的 exp 项经 base := opp z 逐位归位（δ 透明）。              *)
(* ============================================================ *)

Section FEPReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable zz : X -> Real.
Variable TT : Real.
Variable TT_pos : real_lt real_zero TT.

Definition lld_fep_base (s : X) : Real := real_opp (zz s).
Definition lld_fep_invT : Real := real_inv_pos TT TT_pos.
Definition lld_fep_Zf : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX.

(* 辅件 1：Boltzmann 因子逐项正性（站点 Zf_pos 的 sum_pos 肢） *)
Lemma lld_fep_boltz_factor_pos : forall s : X,
  real_lt real_zero (real_exp_neg (real_mult lld_fep_invT (zz s))).
Proof.
  intro s. exact (real_exp_neg_pos (real_mult lld_fep_invT (zz s))).
Qed.

(* 配分函数正性（站点 Zf_pos 的 datum 形） *)
Lemma lld_fep_Zf_pos : real_lt real_zero lld_fep_Zf.
Proof.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX
           lld_fep_boltz_factor_pos lX_ne).
Qed.

(* softmax_z / boltz_z 逐位同构（站点 UpReqFEPAttn:118/120） *)
Definition lld_fep_softmax (s : X) : Real :=
  real_mult (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
            (real_inv_pos lld_fep_Zf lld_fep_Zf_pos).
Definition lld_fep_boltz (s : X) : Real :=
  real_mult (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
            (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s))).

Lemma lld_fep_softmax_pos : forall s : X, real_lt real_zero (lld_fep_softmax s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)).
Qed.

Lemma lld_fep_boltz_pos : forall s : X, real_lt real_zero (lld_fep_boltz s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))).
Qed.

(* 主定理carrier对范式实例位：件 4（req_attention_minimizes_free_energy_     *)
(* unique 的 softmax/boltz 对）逐点 Gibbs 切线 Bishop 形——Part D 范本   *)
(* D0 在站点 2 carrier上的 @ 全显装配。≤ 肢/唯一肢全量复演阻塞见头注 a。    *)
Lemma lld_fep_softmax_boltz_pointwise_B : forall s : X,
  real_le_b (real_plus (lld_fep_softmax s) (real_opp (lld_fep_boltz s)))
            (real_kl_term (lld_fep_softmax s) (lld_fep_boltz s)
                          (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Proof.
  intro s.
  exact (gibbsd_gibbs_pointwise_B X lld_fep_softmax lld_fep_boltz s
           (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Qed.

End FEPReal.

(* ============================================================ *)
(* Part BT：站点 3/4 共用温度 Boltzmann 族（Real 具体形）                 *)
(*   站点 3 tB（UpReqTempEntropy:71）/站点 4 fw_bt（UpFirewallReq:105）  *)
(*   的 real_list_sum 具体形（reqd_boltzmann_dist_temp 的 Real 重放，   *)
(*   判例装法：抽象 fsum_pos 参数位 δ 不匹配，沿 ZPosD 先例具体重放）。 *)
(* ============================================================ *)

Section BTReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable be : X -> Real.

(* 温度配分函数 Z_t（站点 Z_temp_spec 的具体形） *)
Definition lld_btz (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX.

Lemma lld_btz_pos : forall (t : Real) (Ht : real_lt real_zero t),
  real_lt real_zero (lld_btz t Ht).
Proof.
  intros t Ht.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX
           (fun s : X => real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           lX_ne).
Qed.

(* 温度 Boltzmann 分布（站点 tB / fw_bt 的具体形） *)
Definition lld_bt (t : Real) (Ht : real_lt real_zero t) (s : X) : Real :=
  real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)).

Lemma lld_bt_pos : forall (t : Real) (Ht : real_lt real_zero t) (s : X),
  real_lt real_zero (lld_bt t Ht s).
Proof.
  intros t Ht s.
  exact (real_mult_positive
           (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
           (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
Qed.

(* 归一化（站点 tBnorm / fw_norm 的具体形；线性提因子 + 逆元闭合） *)
Lemma lld_bt_norm : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (real_list_sum X (lld_bt t Ht) lX) real_one.
Proof.
  intros t Ht.
  apply (real_eq_trans
           (real_list_sum X (lld_bt t Ht) lX)
           (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                      (lld_btz t Ht))
           real_one).
  - apply (real_eq_trans
             (real_list_sum X (lld_bt t Ht) lX)
             (real_list_sum X
                (fun s : X => real_mult (real_inv_pos (lld_btz t Ht)
                                                          (lld_btz_pos t Ht))
                                        (real_exp_neg
                                           (real_mult (real_inv_pos t Ht)
                                                      (be s)))) lX)
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))).
    + apply real_list_sum_ext. intro s.
      exact (real_mult_comm (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
                            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
    + exact (real_list_sum_linear X
               (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
               (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
               lX).
  - apply (real_eq_trans
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))
             (real_mult (lld_btz t Ht)
                        (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)))
             real_one).
    + exact (real_mult_comm (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                            (lld_btz t Ht)).
    + exact (real_inv_pos_correct (lld_btz t Ht) (lld_btz_pos t Ht)).
Qed.

(* ============================================================ *)
(* 站点 3 件：L554 肢（req_gibbs_inequality p (tB t)，UpReqTempEntropy   *)
(*   件 2/件 4 槽使用位）的 Real 实例化 Bishop 形——Part D 范本 D1 在     *)
(*   站点 3 使用对 (p, lld_bt t) 上的 @ 全显装配。                       *)
(* ============================================================ *)

Lemma lld_tempent_kl_nonneg_B : forall (t : Real) (Ht : real_lt real_zero t)
  (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
  (Hnormp : real_eq (real_list_sum X p lX) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (lld_bt t Ht s)
                     (Hp s) (lld_bt_pos t Ht s)) lX).
Proof.
  intros t Ht p Hp Hnormp.
  exact (gibbsd_gibbs_inequality X lX p (lld_bt t Ht)
           Hp (lld_bt_pos t Ht) Hnormp (lld_bt_norm t Ht)).
Qed.

(* 站点 3 eq 伴随件：req_entropy_neg_sum（UpReqDist:1947，站点熵链      *)
(*   使用位）的 real_list_sum 层对位——Σ p·log p == −Σ p·(−log p)。      *)
Lemma lld_tempent_entropy_neg_sum_B : forall (p : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
          (real_opp (real_list_sum X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX)).
Proof.
  intros p Hp.
  apply (real_eq_trans
           (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
           (real_list_sum X
              (fun s : X => real_opp (real_mult (p s)
                                                (real_opp (real_log (p s) (Hp s))))) lX)
           (real_opp (real_list_sum X
              (fun s : X => real_mult (p s)
                                      (real_opp (real_log (p s) (Hp s)))) lX))).
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s)))))).
    + exact (real_eq_sym (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp_opp (real_mult (p s) (real_log (p s) (Hp s))))).
    + exact (RealSetoid.real_eq_opp_compat
               (real_opp (real_mult (p s) (real_log (p s) (Hp s))))
               (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
               (real_opp_mult (p s) (real_log (p s) (Hp s)))).
  - exact (real_list_sum_opp X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX).
Qed.

(* ============================================================ *)
(* 站点 4 件：L312/L378 肢（@req_gibbs_inequality (fw_bt t1) (fw_bt t2)，*)
(*   件 5 Hkl / 件 6 Hkl21 槽使用位）的 Real 实例化 Bishop 形——Part D    *)
(*   范本 D1 在站点 4 温度对上的 @ 全显装配。                            *)
(* ============================================================ *)

Lemma lld_fw_kl_boltz_pair_nonneg_B : forall (t1 t2 : Real)
  (Ht1 : real_lt real_zero t1) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (lld_bt t1 Ht1 s) (lld_bt t2 Ht2 s)
                     (lld_bt_pos t1 Ht1 s) (lld_bt_pos t2 Ht2 s)) lX).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (gibbsd_gibbs_inequality X lX (lld_bt t1 Ht1) (lld_bt t2 Ht2)
           (lld_bt_pos t1 Ht1) (lld_bt_pos t2 Ht2)
           (lld_bt_norm t1 Ht1) (lld_bt_norm t2 Ht2)).
Qed.

End BTReal.

(* ============================================================ *)
(* 核对（假设位证明系列 #2 结果清单，18 Qed）：                              *)
(*   共享地基 2 件：lld_lt_zero_sub_r / lld_le_b_zero_sub（Part A       *)
(*   缺口延伸：lt 减形正性 + Bishop 序减形升格）。                       *)
(*   四站点给定件 4 件：lld_{u2,fep,tempent,fw}_log_le_linear_B          *)
(*   站点 1：lld_u2_gibbs_eq_step1_B（gibbs_equality 首步肢 Bishop 形）。*)
(*   站点 2：FEPReal 节 5 Qed（boltz_factor_pos / Zf_pos / softmax_pos / *)
(*   boltz_pos / softmax_boltz_pointwise_B）+ 5 Definition carrier同构。    *)
(*   站点 3：BTReal 节内 lld_tempent_kl_nonneg_B +                       *)
(*   lld_tempent_entropy_neg_sum_B；BT 族 3 件（btz_pos/bt_pos/bt_norm） *)
(*   为站点 3/4 共用。                                                   *)
(*   站点 4：lld_fw_kl_boltz_pair_nonneg_B。                             *)
(*   E-LOGLIN-1：log_le_linear 四站点同构槽证明——Part A/C 复用确认       *)
(*   （E-GIBBSD-1 预言全数消解）；下游终局共同阻塞双缺件：log 逆消去     *)
(*   （E-GIBBSD-2 边界再证，p·(log p−log q) 形四站全同）+ Bishop         *)
(*   fsum_zero_nonneg（In-machinery 部分和机）；抽象 fsum_pos @ 实例化   *)
(*   δ 判定沿 ZPosD 系判例装法先例（datum 非空前提单列口径）。            *)
(*   E-LOGLIN-2：Bishop 减形升格器 lld_le_b_zero_sub（a ≤_B b ⟹         *)
(*   0 ≤_B b−a）——槽证明族通用入轨件，实_lt_zero_sub_r + swap_mid        *)
(*   闭合，建议入 Part A 复用清单。                                      *)
(* ============================================================ *)

(* ======== G05_LogSmall 成员件：UpReqLogD（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqLogD.v —— 假设位证明系列 G6：log 不等式族证明（S 族 17 槽）          *)
(*   广义主定理链 G6 执行模块                                   *)
(* ------------------------------------------------------------------ *)
(* 引擎坐标实读（普查 G6 节 L85-101 + §四 L380 落点纪律执行记录）：      *)
(*   ① Real 层 B 形引擎（UpRealLeB）：real_log_le_linear_B@535 /        *)
(*      real_gibbs_inequality_B@592 / real_le_to_le_b@78 /              *)
(*      real_log_one_plus_le_B@543 / real_exp_ge_linear_B@526。         *)
(*   ② 根件（CW_ConstructiveWorld_219 源码实读）：real_log_le_linear_eps@41058（Or 形逐    *)
(*      eps，接口字段 log_le_linear_eps@41134 在案——判例旧判定「接口  *)
(*      real_log_mult@40403 / real_log_one / real_two_pos@41807 /       *)
(*      real_gibbs_inequality_eps@41704 / real_kl_term@41696 /          *)
(*      real_boltzmann_dist_r@43686（Section RealRLHFMain 出口）。       *)
(*   ③ G5 供给（UpReqLogPrimD）：logd_log_inv_one_inv_real（log(1/x)    *)
(*      ≡ −log x）——G08_Gibbs 登记表 E-GIBBSD-2 记名缺口件，本文件到位。  *)
(*   ④ 桥核对（红线）：real_le_to_le_b@78 / latb_real_lt_to_le_b@87 /   *)
(*      real_lt_le_bridge@G01_CoreMicro:16 全单向（real_le/lt → real_le_b）；*)
(*      逆向 real_le_b → real_le = Or 形精确闭合，构造性不可证。req 层   *)
(*      Or 形无条件槽（log_le_linear 全字面形）据此不证明，改逐 eps /    *)
(*      le_b 语言给出（§380 纪律 fallback，落点=Real 实例化定理）。      *)
(* ------------------------------------------------------------------ *)
(* 给出（槽证明件 = 槽被引擎填充的具体实例， 模板 ② 形态）：            *)
(*   [槽族 1：log_le_linear / dist_log_le_linear 双形，5 参数位]           *)
(*    logd_log_le_linear_eps —— 逐 eps Or 形（req 槽语句最近可达形；     *)
(*      real_log_le_linear_eps 直接提供）；                                  *)
(*    logd_log_le_linear_B —— le_b 形（real_log_le_linear_B 直接提供）。     *)
(*   [槽族 2：log 严格单调三槽] logd_log_lt_mono_real（UpReqCauchy:819   *)
(*      log_lt_mono_cc / UpReqAlignRestA:80 ralt_log_lt_mono 字面形；    *)
(*      real_log_lt_mono 直接提供）；logd_log_two_pos_real（UpPredRelaxReq:  *)
(*      221 字面形；1<2 平移 + real_log_lt_mono + real_log_one 组装）。  *)
(*   [槽族 3：KL 字面形桥——G6 主定理] logd_kl_term_minus_form：            *)
(*      real_kl_term p q ≡ p·(log p − log q)（real_log_mult 分解 + G5    *)
(*      log 逆消去）；b_gibbs_pos/b_gibbs_sum_eps（UpSigMigrate2 kl_a    *)
(*      = Σ p·(log p − log q) 字面形）与 req2_gibbs_inequality 的 Real   *)
(*      实例化供给组件：logd_list_sum_kl_minus_form /                      *)
(*      logd_gibbs_inequality_minus_B（0 ≤_B Σ 字面形）/                 *)
(*      logd_gibbs_inequality_minus_eps（0 ≤ Σ 字面形 + eps）。          *)
(*      字面形桥接留待」——本文件经 G5 件闭合，字面形全通。                 *)
(*   [槽族 4：real_gibbs_sum_eps@UpRealLeB:206 槽]                       *)
(*      logd_gibbs_sum_eps_boltzmann_list —— real_sum_over_S :=          *)
(*      real_list_sum 实例化填件（q := real_boltzmann_dist_r；供给槽     *)
(*      Hnormb=Σp_b==1 显式位——诚实条件证明，G5 logd_pos_of_agree 同型； *)
(*      real_rlhf_optimal_B 供给链到此闭合）。                           *)
(*   证明（Real 实例化）：log_le_linear / dist_log_le_linear /           *)
(*    log_lt_mono_cc / ralt_log_lt_mono / log_two_pos / real_gibbs_sum_  *)
(*    eps（条件）= 6；字面形供给（gibbs 族补强）：b_gibbs_pos /           *)
(*    b_gibbs_sum_eps / req2_gibbs_inequality = 3。                       *)
(*   X 阻塞（等号情形，红线不越）：log_eq_linear / dist_log_eq_linear /   *)
(*    b_gibbs_eq / bridge_free_energy_min_unique = 4——需 log 严格凹性    *)
(*    闭合（CW_ConstructiveWorld_219 L41199 注记：需强三分/LPO，构造性不可证）。            *)
(*   S 阻塞（复合，供给链已明）：entropy_tangent（entropy_gradient 抽象   *)
(*    无 spec，N 参）/ req_energy_exp_temp_mono /                        *)
(*    req_energy_exp_temp_strict_mono（fw_et 温度复合，供给=req_entropy_ *)
(*    temp_explicit 槽本身 S 阻塞，G5 判定表）/ bridge_min_free_energy    *)
(*    （Real 实例化已在盘=real_rlhf_optimal_B@UpRealLeB:237，req Or 形    *)
(*    阻塞=序桥红线）= 4。                                               *)
(* 防同名冲突：logd_ 前缀与 G5 UpReqLogPrimD 同族；本文件 10 个新名 + 文件名     *)
(*    全库 grep 实测零命中（建前 逐名实查）。                  *)
(* 红线：Set 层零 Prop（real_le/real_lt/real_eq/real_le_b 全 Set 值，    *)
(*    语句与证明零 Prop 泄露）；全 Qed 闭合；零公理；既有文件零改；      *)
(*    双形并存（le_b/逐 eps 双形 + kl_term/字面形双形）；        *)
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
Require Import UpRealLeB.
Require Import G08_Gibbs.

From Stdlib Require Import List.

(* ============================================================ *)
(* Part A：Bishop 序代数补件（gibbsd_le_b_id_l 的右端对偶件）            *)
(* ============================================================ *)

(* A1：Bishop 序右端 real_eq 换形（req 层 le_id_r 的 le_b 对位） *)
Lemma logd_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hab. unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat a a
           (real_plus b eps) (real_plus c eps)).
  - apply real_eq_refl.
  - exact (RealSetoid.real_eq_plus_compat b eps c eps Hab
             (real_eq_refl eps)).
  - exact (H eps Heps).
Qed.

(* ============================================================ *)
(* Part B：槽族 1——log_le_linear / dist_log_le_linear 双形证明          *)
(*   （UpReqU2:313 / UpReqFEPAttn:90 / UpReqDist:1029 /                 *)
(*     UpReqTempEntropy:60 / UpFirewallReq:101；req 层 Or 全字面形 =     *)
(*     逆向桥红线不越，本件为 §380 fallback 落点）                       *)
(* ============================================================ *)

(* B1：逐 eps Or 形（req 槽语句最近可达形；real_log_le_linear_eps        *)
Lemma logd_log_le_linear_eps : forall (x eps : Real)
    (Hx : real_lt real_zero x),
  real_lt real_zero eps ->
  real_le (real_log x Hx) (real_plus (real_plus x (real_opp real_one)) eps).
Proof.
  intros x eps Hx Heps.
  exact (RealInterfaceEnhancedMod.real_log_le_linear_eps x eps Hx Heps).
Qed.

(* B2：le_b 形（槽形语句 Bishop 序版；real_log_le_linear_B@UpRealLeB:535 *)
(*     直接提供——与 B1 双形并存） *)
Lemma logd_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx.
  exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part C：槽族 2——log 严格单调三槽（log_lt_mono_cc /                   *)
(*   ralt_log_lt_mono / log_two_pos；real_log_lt_mono@CW_ConstructiveWorld_219:39059 供给） *)
(* ============================================================ *)

(* C1：log 严格单调字面形（UpReqCauchy:819 / UpReqAlignRestA:80 槽形；   *)
(*     real_log_lt_mono 直接提供；cw_log ≡ real_log delta 换形在 exact 内）  *)
Lemma logd_log_lt_mono_real : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (real_log_lt_mono a b Ha Hb Hlt).
Qed.

(* C2：log 2 > 0（UpPredRelaxReq:221 槽形字面直接提供；2>0 见证位 =
     real_plus_positive one one one_pos one_pos 与槽逐位同形） *)
Lemma logd_log_two_pos_real :
  real_lt real_zero
    (real_log (real_plus real_one real_one)
       (real_plus_positive real_one real_one
          real_lt_zero_one real_lt_zero_one)).
Proof.
  apply (RealSetoid.real_lt_compat
           (real_log real_one real_lt_zero_one) real_zero
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))
           (real_log (real_plus real_one real_one)
              (real_plus_positive real_one real_one
                 real_lt_zero_one real_lt_zero_one))).
  - exact (real_log_one real_lt_zero_one).
  - apply real_eq_refl.
  - apply (real_log_lt_mono real_one (real_plus real_one real_one)
             real_lt_zero_one
             (real_plus_positive real_one real_one
                real_lt_zero_one real_lt_zero_one)).
    (* 1 < 2：0<1 加法平移 + one+zero==one 换形 *)
    apply (RealSetoid.real_lt_compat
             (real_plus real_one real_zero) real_one
             (real_plus real_one real_one) (real_plus real_one real_one)).
    + exact (real_plus_zero real_one).
    + apply real_eq_refl.
    + exact (real_lt_plus_translate real_one real_zero real_one
               real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Part D：槽族 3（主定理）——KL 字面形桥                                   *)
(*   real_kl_term p q（CW_ConstructiveWorld_219 规范形 p·(−log(q/p))）≡ p·(log p − log q)   *)
(*   （b_gibbs_* / req2_gibbs_inequality / fe_a 字面形）。链：            *)
(*   log(q/p) == log q + log(1/p)（real_log_mult）+ log(1/p) == −log p    *)
(*   （G5 logd_log_inv_one_inv_real——E-GIBBSD-2 记名缺口件到位）→        *)
(* ============================================================ *)

(* D1【槽证明位】：real_kl_term 与字面形逐点恒等（req_kl_term_equiv 型    *)
(*    槽的 Real 实例化——Section RealRLHFMain 诚实接口 real_kl_term_equiv *)
(*    的填件方向之逆，双形并存） *)
Lemma logd_kl_term_minus_form : forall (p q : Real)
    (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp)
                                  (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (Hi := real_inv_pos_pos p Hp).
  set (Hr := real_mult_positive q (real_inv_pos p Hp) Hq Hi).
  (* log(q/p) == log q + (−log p)（log_mult 分解 + G5 log 逆消去） *)
  assert (Hlog : real_eq
                   (real_log (real_mult q (real_inv_pos p Hp)) Hr)
                   (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
  { apply (real_eq_trans
             (real_log (real_mult q (real_inv_pos p Hp)) Hr)
             (real_plus (real_log q Hq) (real_log (real_inv_pos p Hp) Hi))
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
    - exact (real_log_mult q (real_inv_pos p Hp) Hq Hi).
    - apply (RealSetoid.real_eq_plus_compat (real_log q Hq)
               (real_log (real_inv_pos p Hp) Hi) (real_log q Hq)
               (real_opp (real_log p Hp))).
      + apply real_eq_refl.
      + exact (logd_log_inv_one_inv_real p Hp Hi). }
  (* p·(−log(q/p)) == p·(log p − log q)：取负 + 换序 + opp 对合 *)
  apply (RealSetoid.real_eq_mult_compat p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr)) p
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp)) Hr))
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    + apply (RealSetoid.real_eq_opp_compat
               (real_log (real_mult q (real_inv_pos p Hp)) Hr)
               (real_plus (real_log q Hq) (real_opp (real_log p Hp)))).
      exact Hlog.
    + apply (real_eq_trans
               (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq))
                          (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      * exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log q Hq))
                            (real_opp (real_opp (real_log p Hp))))
                 (real_plus (real_opp (real_opp (real_log p Hp)))
                            (real_opp (real_log q Hq)))
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
        -- apply real_plus_comm.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_opp (real_opp (real_log p Hp)))
                     (real_opp (real_log q Hq))
                     (real_log p Hp) (real_opp (real_log q Hq))).
           ++ exact (real_opp_opp (real_log p Hp)).
           ++ apply real_eq_refl.
Qed.

(* D2：求和层字面形恒等（real_list_sum_ext 逐点提升） *)
Lemma logd_list_sum_kl_minus_form :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq.
  apply real_list_sum_ext.
  intro s.
  exact (logd_kl_term_minus_form (p s) (q s) (Hp s) (Hq s)).
Qed.

(* D3【保底主件】：0 ≤_B Σ p·(log p − log q)——b_gibbs_pos 字面形的     *)
(*    Real 实例化（gibbsd_gibbs_inequality 规范形 + D2 换形；与 E.13     *)
(*    real_gibbs_inequality_B 规范形双形并存） *)
Lemma logd_gibbs_inequality_minus_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_mult (p s)
                      (real_plus (real_log (p s) (Hp s))
                                 (real_opp (real_log (q s) (Hq s))))) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  apply (logd_le_b_id_r real_zero
           (real_list_sum X
              (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_list_sum X
              (fun s : X => real_mult (p s)
                             (real_plus (real_log (p s) (Hp s))
                                        (real_opp (real_log (q s) (Hq s))))) l)).
  - exact (gibbsd_gibbs_inequality X l p q Hp Hq Hnormp Hnormq).
  - exact (logd_list_sum_kl_minus_form X l p q Hp Hq).
Qed.

(* D4：0 ≤ Σ p·(log p − log q) + eps——b_gibbs_sum_eps 字面形的          *)
(*    Real 实例化（real_gibbs_inequality_eps 规范形 + D2 换形；与 D3     *)
(*    双形并存：Or 逐 eps 形 / Bishop 形） *)
Lemma logd_gibbs_inequality_minus_eps :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s)
                         (real_plus (real_log (p s) (Hp s))
                                    (real_opp (real_log (q s) (Hq s))))) l)
       eps).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq eps Heps.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
              eps)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s)
                                (real_plus (real_log (p s) (Hp s))
                                           (real_opp (real_log (q s) (Hq s))))) l)
              eps)).
  - exact (RealSetoid.real_eq_plus_compat
             (real_list_sum X
                (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
             eps
             (real_list_sum X
                (fun s : X => real_mult (p s)
                               (real_plus (real_log (p s) (Hp s))
                                          (real_opp (real_log (q s) (Hq s))))) l)
             eps
             (logd_list_sum_kl_minus_form X l p q Hp Hq)
             (real_eq_refl eps)).
  - exact (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq eps Heps).
Qed.

(* ============================================================ *)
(* Part E：槽族 4——real_gibbs_sum_eps@UpRealLeB:206 槽填件               *)
(*   （Section RealRLHFLeB 供给槽；real_sum_over_S := real_list_sum      *)
(*     实例化；q := real_boltzmann_dist_r；供给槽 Hnormb = Σ p_b == 1    *)
(*     显式位——诚实条件证明（G5 logd_pos_of_agree 同型手法），           *)
(*     real_rlhf_optimal_B 供给链到此闭合到一条解析件）                   *)
(* ============================================================ *)

Lemma logd_gibbs_sum_eps_boltzmann_list :
  forall (X : Type) (base : X -> Real) (D : Real)
    (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z)
    (l : list X) (p : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s) l)
                real_one)
    (eps : Real), real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_list_sum X
          (fun s : X => real_kl_term (p s)
                          (real_boltzmann_dist_r X base D D_pos Z Z_pos s)
                          (Hp s)
                          (real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)) l)
       eps).
Proof.
  intros X base D D_pos Z Z_pos l p Hp Hnormp Hnormb eps Heps.
  exact (real_gibbs_inequality_eps X l p
           (fun s : X => real_boltzmann_dist_r X base D D_pos Z Z_pos s)
           Hp
           (fun s : X => real_boltzmann_dist_r_pos X base D D_pos Z Z_pos s)
           Hnormp Hnormb eps Heps).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全部证明件 Print Assumptions + 提取常数面）         *)
(* ============================================================ *)
Print Assumptions logd_le_b_id_r.
Print Assumptions logd_log_le_linear_eps.
Print Assumptions logd_log_le_linear_B.
Print Assumptions logd_log_lt_mono_real.
Print Assumptions logd_log_two_pos_real.
Print Assumptions logd_kl_term_minus_form.
Print Assumptions logd_list_sum_kl_minus_form.
Print Assumptions logd_gibbs_inequality_minus_B.
Print Assumptions logd_gibbs_inequality_minus_eps.
Print Assumptions logd_gibbs_sum_eps_boltzmann_list.

From Stdlib Require Import Extraction.
(* G3 全量提取面（10 件；magic 普查=73，全部位于 coq_RealEnhancedReal    *)
(*    类实例封装常量与 G5 UpReqLogPrimD 类投影链——本文件 10 件自身证明体   *)
(*    零 magic，唯一触点=D1 使用 G5 logd_log_inv_one_inv_real 的强制     *)
(*    转型一处；见技术报告 G3 节） *)
Extraction "_logd_g3_extract.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real
  logd_kl_term_minus_form logd_list_sum_kl_minus_form
  logd_gibbs_inequality_minus_B logd_gibbs_inequality_minus_eps
  logd_gibbs_sum_eps_boltzmann_list.
(* G3 纯净面（5 件，零类实例依赖；magic=0 门证据件） *)
Extraction "_logd_g3_pure.ml" logd_le_b_id_r logd_log_le_linear_eps
  logd_log_le_linear_B logd_log_lt_mono_real logd_log_two_pos_real.

(* ============================================================ *)
(*   槽族 1（log_le_linear 双形，5 参数位）：                              *)
(*    - log_le_linear@UpReqU2:313 / @UpReqFEPAttn:90 —— Real 实例化证明  *)
(*      （B1/B2 双形）；req 层 Or 全字面形 = 逆向桥红线不越（§380）。    *)
(*    - dist_log_le_linear@UpReqDist:1029 / @UpReqTempEntropy:60 /       *)
(*      @UpFirewallReq:101 —— 同上（同语句独立声明，落点逐文件）。       *)
(*   槽族 2（log 严格单调，3 槽）：                                      *)
(*    - log_lt_mono_cc@UpReqCauchy:819 / ralt_log_lt_mono@               *)
(*      UpReqAlignRestA:80 —— 字面形证明（C1 直接提供）。                    *)
(*    - log_two_pos@UpPredRelaxReq:221 —— 字面形证明（C2 组装）。        *)
(*   槽族 3（gibbs 字面形桥，4 槽）：                                    *)
(*    - b_gibbs_pos@UpSigMigrate2:913 / b_gibbs_sum_eps@916 —— 字面形    *)
(*      Real 实例化证明（D3/D4；kl_a 字面形逐位对齐）。                  *)
(*    - req2_gibbs_inequality@UpReqAlign3:1451 / @UpReqU2:356 —— 同上    *)
(*      供给（KLE 字面形=kl_a 同构；req 层 Or 形阻塞判定与                *)
(*      UpReqAlign3 登记表「plain-le 形态不可由接口逐 eps 字段导出」一致）。*)
(*   X 阻塞 4 槽（等号情形，构造性不可证——CW_ConstructiveWorld_219 L41199 注记强三分/LPO）： *)
(*    - log_eq_linear@UpReqU2:315 / @UpReqFEPAttn:92；                   *)
(*      dist_log_eq_linear@UpReqDist:1031 / @UpReqTempEntropy:62；       *)
(*      b_gibbs_eq@UpSigMigrate2:921；                                   *)
(*      bridge_free_energy_min_unique@UpReqAlign:288（FEP 唯一极小=      *)
(*      KL 等号情形）。普查 §373 模块 l「可能留槽」预判成立。               *)
(*   S 阻塞 4 槽（复合/抽象，供给链已明）：                              *)
(*    - entropy_tangent@UpEntropyGainReq:77 / @UpReqCauchy:1383 ——       *)
(*      entropy_gradient 抽象无 spec（N 参「抽象 entropy 凹性」）。       *)
(*    - req_energy_exp_temp_mono@UpFirewallReq:135 /                     *)
(*      req_energy_exp_temp_strict_mono@138 —— fw_et 温度复合；供给=     *)
(*      req_entropy_temp_explicit 槽本身 S 阻塞（G5 判定表）；严格版另   *)
(*      需 KL>0 的 Or-lt 形（等号层 X）。                                *)
(*    - bridge_min_free_energy@UpReqAlign:285 —— Real 实例化已在盘       *)
(*      （real_rlhf_optimal_B@UpRealLeB:237，le_b 形；供给链经本文件       *)
(*      Part E 闭合到唯一解析件 Σp_b==1）；req 层 Or 形=红线阻塞。        *)
(*   槽族 4：real_gibbs_sum_eps@UpRealLeB:206 —— 条件证明（Part E；      *)
(*      供给槽 Σ p_b == 1 的解析实例化留档）。                            *)
(*   log_mult / exp_neg_plus 在案，req 逐 eps 形直接提供成立；E-GIBBSD-2     *)
(*   real_kl_term ↔ p·(log p − log q) 字面形桥全通（Part D），           *)
(*   Section RealRLHFMain 诚实接口 real_kl_term_equiv 槽自此可填。        *)
(*   E-LOGD-2：Bishop 序右端换形件 logd_le_b_id_r 为 gibbsd_le_b_id_l    *)
(*   对偶（Part A 可跨模块复用）；b_gibbs_* 字面形族证明只需              *)
(*   gibbsd 和层机 + 单点 D1，无需重建和层。                             *)
(* ============================================================ *)
