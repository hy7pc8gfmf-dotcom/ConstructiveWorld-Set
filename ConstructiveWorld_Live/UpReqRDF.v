(* ==========================================================================)
   UpReqRDF.v — req 可微函数接口：RDF 记录与运算微分定理
   使命: ReqDiffPlain 类与 reqRDF 记录、req_rdf_plus/mult/opp/minus/compose/affine 运算微分定理族、req_cross_entropy_softmax_diff/req_mse_diff 两应用件、ReqEntropyDiff 节（熵可微）与 MV 区（reqRDFMV 记录、内积 Lipschitz、伴随梯度拉回）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSLM；Stdlib List。
   对标: 微分运算规则（和/积/链式/伴随）在 req 接口上的形式化。
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
Require Import UpReqAlgebra.
Require Import UpReqSLM.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* 载体钉定（UpReqSLM.v 同款）：RealInterfaceEnhancedSetoid 在本树为无参 Class
   （S07_RealSetoidExpLog.v:8075）·字段经全局 Real 实例 RealEnhancedReal 解析；
   生成期带参 binder 已删，载体 R 由下行 Notation 钉定为全局 Real。
   关系字段 req/lt/le 经 Notation 直接绑定具体 S02_CauchyComplete 形
   real_eq/real_lt/real_le（恰为全局实例对这些字段的赋值·语句面 elaboration 同项）——
   盒装类字段投影在提取期为擦除面、与具体载体混用生成 Obj.magic 转写；
   绑定后提取载荷为真数据（ConcMixSelFeed.v 同款）。 *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ===================================================================== *)
(* Part 0：桥假设位组（T2① 假设位道，头注登记表第 4 条）                            *)
(* ===================================================================== *)

(* R 接口被逐 eps 化字段的 plain 对应副本槽（三槽）+ log 全称对应副本槽（一槽）
   + r_max plain 槽（一槽，增量节登记：裁决书 clip_lower 行
   「需补 r_max_ge_plain : le a (r_max a b) 槽」——min 双槽不覆盖 r_max 侧，
   本槽为 Id RealInterfaceEnhanced r_max_le_l 字段 plain 对应副本，T2① 零证明槽）。
   逐槽核对：abs_triangle_plain <- Id RealInterfaceEnhanced abs_triangle；
   min_le_l_plain/min_le_r_plain <- Id min_le_l/min_le_r；
   log_inv_exp_neg_slot <- Id log_inv_exp_neg（req 接口仅反向 exp_neg_log_inv）；
   r_max_ge_plain <- Id r_max_le_l。 *)
Class ReqDiffPlain := {
  abs_triangle_plain : forall a b : R, le (abs (plus a b)) (plus (abs a) (abs b));
  min_le_l_plain : forall a b : R, le (min a b) a;
  min_le_r_plain : forall a b : R, le (min a b) b;
  r_max_ge_plain : forall a b : R, le a (r_max a b);
  log_inv_exp_neg_slot : forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x
}.

(* ===================================================================== *)
(* Part 0.5：reqRDF 记录桥（Id Differentiable L1439 逐字段对应副本）                *)
(* ===================================================================== *)

Record reqRDF (f : R -> R) : Set := {
  rdf_df : R -> R;
  rdf_correct : forall (x eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : R, lt (abs h) delta ->
        le (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df x) h))))
           (mult eps (abs h))))
}.

(* ===================================================================== *)
(* Part 1：公共机器件（helpers；全簇使用）                                     *)
(* ===================================================================== *)

Section ReqRDFBase.

(* 载体 R 已钉定为全局 Real；接口字段经全局实例 RealEnhancedReal 解析——本节无抽象载体/实例参数。 *)
(* 诚实接口披露（红线⑤·Variable 形·UpReqConcMixSel.lt_plus_compat_lt_le 同形）：
   plain 非负槽 real_le zero (abs a)（真前提·类 abs_nonneg 仅 eps 形不可消解）；
   语义同 UpReqSLM 的同名 plain 槽，承载取具体 real_le 面以保证
   提取载荷为真数据（盒装类字段投影为擦除面·与具体载体混用即 Obj.magic 转写）。 *)
Variable abs_nonneg_plain : forall a : R, le zero (abs a).
Context {RDP : ReqDiffPlain}.

(* req_minus 双侧兼容（Id 系无对应：req_minus 非接口字段的公共机） *)
Lemma req_rdf_minus_compat_r : forall a x y : R, req x y -> req (req_minus a x) (req_minus a y).
Proof.
  intros a x y H. unfold req_minus.
  exact (req_plus_compat a a (opp x) (opp y) (req_refl a) (req_opp_compat x y H)).
Qed.

Lemma req_rdf_minus_compat_l : forall a b x : R, req a b -> req (req_minus a x) (req_minus b x).
Proof.
  intros a b x H. unfold req_minus.
  exact (req_plus_compat a b (opp x) (opp x) H (req_refl (opp x))).
Qed.

(* eps/2 正性（req_two_pos 规范见证形；见证相关性——Qed 不透明常量间零转换，
   必须字段直证而非重述 UpReqAlgebra req_half_pos 的内嵌见证形） *)
Lemma req_rdf_half_pos : forall e : R, lt zero e ->
  lt zero (mult (inv_pos (plus one one) req_two_pos) e).
Proof.
  intros e He.
  apply mult_positive.
  - apply inv_pos_pos.
  - exact He.
Qed.

(* 0 ≤ eps·|h|（eps>0；abs_nonneg_plain 槽使用位） *)
Lemma req_rdf_zero_le_mult_abs : forall eps h : R, lt zero eps -> le zero (mult eps (abs h)).
Proof.
  intros eps h Heps.
  apply (le_id_l zero (mult zero (abs h)) (mult eps (abs h))).
  - exact (req_sym (mult zero (abs h)) zero
             (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                        (mult_comm zero (abs h)) (mult_zero (abs h)))).
  - exact (le_mult_compat_weak zero eps (abs h) (abs_nonneg_plain h)
             (lt_le_iff zero eps (inl Heps))).
Qed.

(* E ≡ 0 ⟹ |E| ≤ eps·|h|（零误差件统一完成：const/id/power_nat 基例/ce/mse 头/      *)
(* mv_const/mv_linear 共七处使用） *)
Lemma req_rdf_abs_zero_le : forall E eps h : R,
  lt zero eps -> req E zero -> le (abs E) (mult eps (abs h)).
Proof.
  intros E eps h Heps HE.
  apply (le_trans (abs E) (abs zero) (mult eps (abs h))).
  - exact (le_id_l (abs E) (abs zero) (abs zero) (req_abs_compat E zero HE)
             (le_refl (abs zero))).
  - exact (le_id_l (abs zero) zero (mult eps (abs h)) abs_zero
             (req_rdf_zero_le_mult_abs eps h Heps)).
Qed.

(* |x| + 1 > 0（mult/compose 的 Lipschitz 常数正性位） *)
Lemma req_rdf_abs_plus_one_pos : forall a : R, lt zero (plus (abs a) one).
Proof.
  intro a.
  exact (req_plus_le_lt_pos (abs a) one (abs_nonneg_plain a) one_pos).
Qed.

(* 0 ≤ |a+b|（abs_triangle_plain 槽直引壳——零内容别名，使用侧签名短） *)
Lemma req_rdf_abs_triangle : forall a b : R, le (abs (plus a b)) (plus (abs a) (abs b)).
Proof.
  intros a b. exact (abs_triangle_plain a b).
Qed.

(* L·(inv L·t) == t（L>0；compose/mv_compose/mv_vec 的 inv 消去位，三处使用） *)
Lemma req_rdf_inv_cancel : forall (L t : R) (HL : lt zero L),
  lt zero t -> req (mult L (mult (inv_pos L HL) t)) t.
Proof.
  intros L t HL Ht.
  apply (req_trans (mult L (mult (inv_pos L HL) t))
                   (mult (mult L (inv_pos L HL)) t) t).
  - apply mult_assoc.
  - apply (req_trans (mult (mult L (inv_pos L HL)) t) (mult one t) t).
    + apply (req_mult_compat (mult L (inv_pos L HL)) one t t).
      * exact (inv_pos_correct L HL).
      * apply req_refl.
    + exact (req_trans (mult one t) (mult t one) t (mult_comm one t) (mult_one t)).
Qed.

(* (inv L·e4)·L ≤ e4（L>0；compose 的 eps_f·L ≤ eps4 与 mv 簇同形位，两处使用） *)
Lemma req_rdf_inv_scale_le : forall (L e4 : R) (HL : lt zero L),
  le (mult (mult (inv_pos L HL) e4) L) e4.
Proof.
  intros L e4 HL.
  apply (le_id_l (mult (mult (inv_pos L HL) e4) L) e4 e4).
  - apply (req_trans (mult (mult (inv_pos L HL) e4) L)
                     (mult (inv_pos L HL) (mult e4 L)) e4).
    + exact (req_sym (mult (inv_pos L HL) (mult e4 L))
                     (mult (mult (inv_pos L HL) e4) L) (mult_assoc (inv_pos L HL) e4 L)).
    + apply (req_trans (mult (inv_pos L HL) (mult e4 L))
                       (mult (inv_pos L HL) (mult L e4)) e4).
      * apply (req_mult_compat (inv_pos L HL) (inv_pos L HL) (mult e4 L) (mult L e4)).
        -- apply req_refl.
        -- apply mult_comm.
      * apply (req_trans (mult (inv_pos L HL) (mult L e4))
                         (mult (mult (inv_pos L HL) L) e4) e4).
        -- apply mult_assoc.
        -- apply (req_trans (mult (mult (inv_pos L HL) L) e4)
                            (mult (mult L (inv_pos L HL)) e4) e4).
           ++ apply (req_mult_compat (mult (inv_pos L HL) L) (mult L (inv_pos L HL)) e4 e4).
              ** apply mult_comm.
              ** apply req_refl.
           ++ apply (req_trans (mult (mult L (inv_pos L HL)) e4) (mult one e4) e4).
              ** apply (req_mult_compat (mult L (inv_pos L HL)) one e4 e4).
                 --- exact (inv_pos_correct L HL).
                 --- apply req_refl.
              ** exact (req_trans (mult one e4) (mult e4 one) e4 (mult_comm one e4) (mult_one e4)).
  - apply le_refl.
Qed.

(* eps/2·s + eps/2·s == eps·s（plus 完成核算） *)
Lemma req_rdf_half_pair_req : forall e s : R,
  req (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
            (mult (mult (inv_pos (plus one one) req_two_pos) e) s))
      (mult e s).
Proof.
  intros e s.
  apply (req_sym (mult e s)
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                       (mult (mult (inv_pos (plus one one) req_two_pos) e) s))).
  apply (req_trans (mult e s)
                   (mult (plus (mult (inv_pos (plus one one) req_two_pos) e)
                               (mult (inv_pos (plus one one) req_two_pos) e)) s)).
  - apply (req_mult_compat e (plus (mult (inv_pos (plus one one) req_two_pos) e)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s s).
    + exact (req_sym (plus (mult (inv_pos (plus one one) req_two_pos) e)
                           (mult (inv_pos (plus one one) req_two_pos) e)) e
                     (req_half_twice e req_two_pos)).
    + apply req_refl.
  - exact (req_mult_plus_distr_r (mult (inv_pos (plus one one) req_two_pos) e)
                                 (mult (inv_pos (plus one one) req_two_pos) e) s).
Qed.

Lemma req_rdf_half_pair_le : forall e s : R,
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
           (mult (mult (inv_pos (plus one one) req_two_pos) e) s))
     (mult e s).
Proof.
  intros e s.
  apply (le_id_l _ (mult e s) (mult e s)).
  - exact (req_rdf_half_pair_req e s).
  - apply le_refl.
Qed.

(* eps/4·s + eps/4·s == (eps/2)·s（mult/compose 完成核算第一级） *)
Lemma req_rdf_quarter_pair_req : forall e s : R,
  req (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) e)) s)
            (mult (mult (inv_pos (plus one one) req_two_pos)
                        (mult (inv_pos (plus one one) req_two_pos) e)) s))
      (mult (mult (inv_pos (plus one one) req_two_pos) e) s).
Proof.
  intros e s.
  apply (req_sym (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s)
                       (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s))).
  apply (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                   (mult (plus one one)
                         (mult (mult (inv_pos (plus one one) req_two_pos)
                                     (mult (inv_pos (plus one one) req_two_pos) e)) s))).
  - exact (req_sym (mult (plus one one)
                         (mult (mult (inv_pos (plus one one) req_two_pos)
                                     (mult (inv_pos (plus one one) req_two_pos) e)) s))
                   (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
             (req_two_times_quarter e s req_two_pos)).
  - exact (req_two_mult (mult (mult (inv_pos (plus one one) req_two_pos)
                                    (mult (inv_pos (plus one one) req_two_pos) e)) s)).
Qed.

Lemma req_rdf_quarter_pair_le : forall e s : R,
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s)
           (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s))
     (mult (mult (inv_pos (plus one one) req_two_pos) e) s).
Proof.
  intros e s.
  apply (le_id_l _ (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                   (mult (mult (inv_pos (plus one one) req_two_pos) e) s)).
  - exact (req_rdf_quarter_pair_req e s).
  - apply le_refl.
Qed.

(* half_le_one L25729 req 对位（req_rdf_half_le_self 使用位） *)
Lemma req_rdf_half_le_one : le (inv_pos (plus one one) req_two_pos) one.
Proof.
  apply (le_id_l (inv_pos (plus one one) req_two_pos)
                 (mult (inv_pos (plus one one) req_two_pos) one) one).
  - exact (req_sym (mult (inv_pos (plus one one) req_two_pos) one)
                   (inv_pos (plus one one) req_two_pos)
                   (mult_one (inv_pos (plus one one) req_two_pos))).
  - apply (le_id_r (mult (inv_pos (plus one one) req_two_pos) one)
                   (mult (inv_pos (plus one one) req_two_pos) (plus one one)) one).
    + exact (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                       (mult (plus one one) (inv_pos (plus one one) req_two_pos)) one
                       (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                       (inv_pos_correct (plus one one) req_two_pos)).
    + exact (req_le_mult_compat_r (inv_pos (plus one one) req_two_pos) one (plus one one)
              (lt_le_iff zero (inv_pos (plus one one) req_two_pos)
                         (inl (inv_pos_pos (plus one one) req_two_pos)))
              (req_le_plus_nonneg_r one one (lt_le_iff zero one (inl one_pos)))).
Qed.


(* eps/2·s ≤ eps·s（half_le_self L25748 req 对位；系数非负使用位） *)
Lemma req_rdf_half_le_self : forall a : R,
  le zero a -> le (mult (inv_pos (plus one one) req_two_pos) a) a.
Proof.
  intros a Ha.
  apply (le_trans (mult (inv_pos (plus one one) req_two_pos) a) (mult one a) a).
  - exact (le_mult_compat_weak (inv_pos (plus one one) req_two_pos) one a Ha
             (req_rdf_half_le_one)).
  - exact (le_id_l (mult one a) a a
             (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a))
             (le_refl a)).
Qed.

Lemma req_rdf_quarter_pair_le_final : forall e s : R,
  lt zero e -> le zero s ->
  le (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                       (mult (inv_pos (plus one one) req_two_pos) e)) s)
           (mult (mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) e)) s))
     (mult e s).
Proof.
  intros e s Heps Hs.
  apply (le_trans (plus (mult (mult (inv_pos (plus one one) req_two_pos)
                                   (mult (inv_pos (plus one one) req_two_pos) e)) s)
                        (mult (mult (inv_pos (plus one one) req_two_pos)
                                    (mult (inv_pos (plus one one) req_two_pos) e)) s))
                  (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                  (mult e s)).
  - exact (req_rdf_quarter_pair_le e s).
  - apply (le_trans (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                    (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                    (mult e s)).
    + exact (RealSetoid.real_eq_le (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                           (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                           (req_sym (mult (inv_pos (plus one one) req_two_pos) (mult e s))
                                    (mult (mult (inv_pos (plus one one) req_two_pos) e) s)
                                    (mult_assoc (inv_pos (plus one one) req_two_pos) e s))).
    + exact (req_rdf_half_le_self (mult e s)
                                  (le_id_l zero (mult zero s) (mult e s)
                                   (req_sym (mult zero s) zero
                                    (req_trans (mult zero s) (mult s zero) zero
                                     (mult_comm zero s) (mult_zero s)))
                                   (le_mult_compat_weak zero e s Hs
                                    (lt_le_iff zero e (inl Heps))))).
Qed.



(* |X·Y| ≤ |X|·|Y|（abs_mult 字段的 le 壳——mult/compose 核算统一入口） *)
Lemma req_rdf_abs_mult_le : forall a b : R, le (abs (mult a b)) (mult (abs a) (abs b)).
Proof.
  intros a b.
  exact (le_id_l (abs (mult a b)) (mult (abs a) (abs b)) (mult (abs a) (abs b))
                 (abs_mult a b) (le_refl (mult (abs a) (abs b)))).
Qed.

(* 增量界：|u−(v+d·h)| ≤ e·|h| ⟹ |u−v| ≤ (|d|+e)·|h|
   （mult 的 Hdf_bound/Hdg_bound 与 compose 的 |Dg| ≤ L·|h| 三处使用；
   Id 证明体 minus_split+三角+核算的重排压缩） *)
Lemma req_rdf_delta_bound : forall u v d e hh : R,
  le (abs (req_minus u (plus v (mult d hh)))) (mult e (abs hh)) ->
  le (abs (req_minus u v)) (mult (plus (abs d) e) (abs hh)).
Proof.
  intros u v d e hh Hb.
  apply (le_id_l (abs (req_minus u v))
                 (abs (plus (req_minus u (plus v (mult d hh))) (mult d hh)))
                 (mult (plus (abs d) e) (abs hh))).
  - exact (req_abs_compat (req_minus u v)
             (plus (req_minus u (plus v (mult d hh))) (mult d hh))
             (req_minus_split u v (mult d hh))).
  - apply (le_trans _ (plus (abs (req_minus u (plus v (mult d hh))))
                            (abs (mult d hh)))).
    + exact (req_rdf_abs_triangle (req_minus u (plus v (mult d hh))) (mult d hh)).
    + apply (le_id_r (plus (abs (req_minus u (plus v (mult d hh)))) (abs (mult d hh)))
                     (plus (mult e (abs hh)) (mult (abs d) (abs hh)))
                     (mult (plus (abs d) e) (abs hh))).
      * exact (req_trans (plus (mult e (abs hh)) (mult (abs d) (abs hh)))
                         (plus (mult (abs d) (abs hh)) (mult e (abs hh)))
                         (mult (plus (abs d) e) (abs hh))
                         (plus_comm (mult e (abs hh)) (mult (abs d) (abs hh)))
                         (req_sym (mult (plus (abs d) e) (abs hh))
                                  (plus (mult (abs d) (abs hh)) (mult e (abs hh)))
                                  (req_mult_plus_distr_r (abs d) e (abs hh)))).
      * exact (le_plus_compat (abs (req_minus u (plus v (mult d hh))))
                              (mult e (abs hh))
                              (abs (mult d hh))
                              (mult (abs d) (abs hh))
                              Hb (req_rdf_abs_mult_le d hh)).
Qed.

End ReqRDFBase.

(* ===================================================================== *)
(* Part 2：标量簇 §4 (c) 10 件 + entropy 1 件（逐件核对清单 1-11）                 *)
(* ===================================================================== *)

Section ReqRDFScalar.

(* 载体 R 已钉定为全局 Real；接口字段经全局实例 RealEnhancedReal 解析——本节无抽象载体/实例参数。 *)
(* 诚实接口披露（红线⑤·Variable 形·UpReqConcMixSel.lt_plus_compat_lt_le 同形）：
   plain 非负槽 real_le zero (abs a)（真前提·类 abs_nonneg 仅 eps 形不可消解）；
   语义同 UpReqSLM 的同名 plain 槽，承载取具体 real_le 面以保证
   提取载荷为真数据（盒装类字段投影为擦除面·与具体载体混用即 Obj.magic 转写）。 *)
Variable abs_nonneg_plain : forall a : R, le zero (abs a).
Context {RDP : ReqDiffPlain}.

(* ---- 件 1：differentiable_const L25035 -> req_rdf_const ------------------- *)

Lemma req_rdf_const : forall c : R, reqRDF (fun _ => c).
Proof.
  intro c.
  exists (fun _ => zero).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Hz : req (mult zero h) zero).
    { exact (req_trans (mult zero h) (mult h zero) zero
               (mult_comm zero h) (mult_zero h)). }
    assert (Herr : req (req_minus c (plus c (mult zero h))) zero).
    { assert (Hs1 : req (plus c (opp (plus c (mult zero h)))) (plus c (opp (plus c zero)))).
      { exact (req_plus_compat c c (opp (plus c (mult zero h))) (opp (plus c zero))
                               (req_refl c)
                               (req_opp_compat (plus c (mult zero h)) (plus c zero)
                                               (req_plus_compat c c (mult zero h) zero
                                                                (req_refl c) Hz))). }
      assert (Hs2 : req (plus c (opp (plus c zero))) (plus c (opp c))).
      { exact (req_plus_compat c c (opp (plus c zero)) (opp c)
                               (req_refl c)
                               (req_opp_compat (plus c zero) c (plus_zero c))). }
      exact (req_trans _ _ _ Hs1 (req_trans _ _ _ Hs2 (plus_opp c))). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus c (plus c (mult zero h))) eps h Heps Herr).
Qed.

(* ---- 件 2：differentiable_id L25069 -> req_rdf_id ------------------------- *)

Lemma req_rdf_id : reqRDF (fun x => x).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus (plus x h) (plus x (mult one h))) zero).
    { apply (req_minus_self_zero (plus x h) (plus x (mult one h))).
      exact (req_plus_compat x x h (mult one h)
                             (req_refl x)
                             (req_sym (mult one h) h
                                      (req_trans (mult one h) (mult h one) h
                                                 (mult_comm one h) (mult_one h)))). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (plus x h) (plus x (mult one h))) eps h Heps Herr).
Qed.

(* ---- 件 3：differentiable_plus L25098 -> req_rdf_plus --------------------- *)

Theorem req_rdf_plus : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => plus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  exists (fun x => plus (rdf_df f Hf x) (rdf_df g Hg x)).
  intros x eps Heps.
  destruct (rdf_correct f Hf x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dgd [Hg1 Hg2]].
  exists (min dfd dgd).
  split.
  - exact (min_pos dfd dgd Hd1 Hg1).
  - intros h Hh.
    assert (Hh1 : lt (abs h) dfd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dfd Hh (min_le_l_plain dfd dgd)). }
    assert (Hh2 : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dgd Hh (min_le_r_plain dfd dgd)). }
    apply (le_id_l (abs (req_minus (plus (f (plus x h)) (g (plus x h)))
                                   (plus (plus (f x) (g x))
                                         (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))))
                   (abs (plus (req_minus (f (plus x h))
                                          (plus (f x) (mult (rdf_df f Hf x) h)))
                              (req_minus (g (plus x h))
                                         (plus (g x) (mult (rdf_df g Hg x) h)))))
                   (mult eps (abs h))).
    + exact (req_abs_compat
               (req_minus (plus (f (plus x h)) (g (plus x h)))
                          (plus (plus (f x) (g x))
                                (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)))
               (plus (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))
                     (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))
               (req_trans (req_minus (plus (f (plus x h)) (g (plus x h)))
                                     (plus (plus (f x) (g x))
                                           (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)))
                          (req_minus (plus (f (plus x h)) (g (plus x h)))
                                     (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                           (plus (g x) (mult (rdf_df g Hg x) h))))
                          (plus (req_minus (f (plus x h))
                                           (plus (f x) (mult (rdf_df f Hf x) h)))
                                (req_minus (g (plus x h))
                                           (plus (g x) (mult (rdf_df g Hg x) h))))
                          (req_rdf_minus_compat_r (plus (f (plus x h)) (g (plus x h)))
                             (plus (plus (f x) (g x))
                                   (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))
                             (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                   (plus (g x) (mult (rdf_df g Hg x) h)))
                             (req_trans (plus (plus (f x) (g x))
                                              (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h))
                                        (plus (plus (f x) (g x))
                                              (plus (mult (rdf_df f Hf x) h)
                                                    (mult (rdf_df g Hg x) h)))
                                        (plus (plus (f x) (mult (rdf_df f Hf x) h))
                                              (plus (g x) (mult (rdf_df g Hg x) h)))
                                        (req_plus_compat (plus (f x) (g x))
                                                         (plus (f x) (g x))
                                                         (mult (plus (rdf_df f Hf x) (rdf_df g Hg x)) h)
                                                         (plus (mult (rdf_df f Hf x) h)
                                                               (mult (rdf_df g Hg x) h))
                                                         (req_refl (plus (f x) (g x)))
                                                         (req_mult_plus_distr_r (rdf_df f Hf x)
                                                                                (rdf_df g Hg x) h))
                                        (req_plus_swap_mid (f x) (g x)
                                           (mult (rdf_df f Hf x) h)
                                           (mult (rdf_df g Hg x) h))))
                          (req_minus_plus_distr (f (plus x h)) (g (plus x h))
                                                (plus (f x) (mult (rdf_df f Hf x) h))
                                                (plus (g x) (mult (rdf_df g Hg x) h))))).
    + apply (le_trans _
               (plus (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))
                     (abs (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))))).
      * exact (req_rdf_abs_triangle
                 (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))
                 (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))).
      * apply (le_trans _
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h)))).
        -- exact (le_plus_compat
                   (abs (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (abs (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps) (abs h))
                   (Hd2 h Hh1) (Hg2 h Hh2)).
        -- exact (req_rdf_half_pair_le eps (abs h)).
Qed.

(* ---- 公共机器件 2：乘积份额/四项积/inv 完成（mult 主件使用） ---------------- *)

(* |a| ≤ m 且 m·e == E4、0 ≤ hh ⟹ |a|·(e·hh) ≤ E4·hh
   （Id Hshare+Hsh2 两段核算的压缩壳；mult 两处使用，hh 恒为 |h| 位） *)
Lemma req_rdf_share : forall a m e E4 hh : R,
  le (abs a) m -> lt zero e -> req (mult m e) E4 -> le zero hh ->
  le (mult (abs a) (mult e hh)) (mult E4 hh).
Proof.
  intros a m e E4 hh Hle_am He Hreq Hnn.
  apply (le_trans (mult (abs a) (mult e hh)) (mult (mult (abs a) e) hh) (mult E4 hh)).
  - exact (le_id_l (mult (abs a) (mult e hh)) (mult (mult (abs a) e) hh)
                   (mult (mult (abs a) e) hh) (mult_assoc (abs a) e hh)
                   (le_refl (mult (mult (abs a) e) hh))).
  - apply (le_trans (mult (mult (abs a) e) hh) (mult (mult m e) hh) (mult E4 hh)).
    + exact (le_mult_compat_weak (mult (abs a) e) (mult m e) hh Hnn
               (le_mult_compat (abs a) m e He Hle_am)).
    + exact (le_id_l (mult (mult m e) hh) (mult E4 hh) (mult E4 hh)
               (req_mult_compat (mult m e) E4 hh hh Hreq (req_refl hh))
               (le_refl (mult E4 hh))).
Qed.

(* (a1·s)·(a2·s) == (a1·a2)·(s·s)（Id Hs1-Hs6 六步链的压缩壳；mult Hthird 使用） *)
Lemma req_rdf_four_mult : forall a1 a2 s : R,
  req (mult (mult a1 s) (mult a2 s)) (mult (mult a1 a2) (mult s s)).
Proof.
  intros a1 a2 s.
  apply (req_trans (mult (mult a1 s) (mult a2 s))
                   (mult a1 (mult s (mult a2 s)))
                   (mult (mult a1 a2) (mult s s))).
  - exact (req_sym (mult a1 (mult s (mult a2 s)))
                   (mult (mult a1 s) (mult a2 s)) (mult_assoc a1 s (mult a2 s))).
  - apply (req_trans (mult a1 (mult s (mult a2 s)))
                     (mult a1 (mult (mult s a2) s))
                     (mult (mult a1 a2) (mult s s))).
    + exact (req_mult_compat a1 a1 (mult s (mult a2 s)) (mult (mult s a2) s)
                             (req_refl a1) (mult_assoc s a2 s)).
    + apply (req_trans (mult a1 (mult (mult s a2) s))
                       (mult a1 (mult (mult a2 s) s))
                       (mult (mult a1 a2) (mult s s))).
      * exact (req_mult_compat a1 a1 (mult (mult s a2) s) (mult (mult a2 s) s)
                               (req_refl a1)
                               (req_mult_compat (mult s a2) (mult a2 s) s s
                                                (mult_comm s a2) (req_refl s))).
      * apply (req_trans (mult a1 (mult (mult a2 s) s))
                         (mult (mult a1 (mult a2 s)) s)
                         (mult (mult a1 a2) (mult s s))).
        -- exact (mult_assoc a1 (mult a2 s) s).
        -- apply (req_trans (mult (mult a1 (mult a2 s)) s)
                            (mult (mult (mult a1 a2) s) s)
                            (mult (mult a1 a2) (mult s s))).
           ++ exact (req_mult_compat (mult a1 (mult a2 s)) (mult (mult a1 a2) s) s s
                                     (mult_assoc a1 a2 s) (req_refl s)).
           ++ exact (req_sym (mult (mult a1 a2) (mult s s))
                             (mult (mult (mult a1 a2) s) s)
                             (mult_assoc (mult a1 a2) s s)).
Qed.

(* D·((inv D·e2)·hh) == e2·hh（D>0；mult Hdq 与 compose 预算完成同形使用） *)
Lemma req_rdf_inv_pair : forall (D : R) (HD : lt zero D) (e2 hh : R),
  req (mult D (mult (mult (inv_pos D HD) e2) hh)) (mult e2 hh).
Proof.
  intros D HD e2 hh.
  assert (Hinner : req (mult D (mult (inv_pos D HD) e2)) (mult one e2)).
  { apply (req_trans (mult D (mult (inv_pos D HD) e2))
                     (mult (mult D (inv_pos D HD)) e2)
                     (mult one e2)).
    - exact (mult_assoc D (inv_pos D HD) e2).
    - exact (req_mult_compat (mult D (inv_pos D HD)) one e2 e2
                             (inv_pos_correct D HD) (req_refl e2)). }
  apply (req_trans (mult D (mult (mult (inv_pos D HD) e2) hh))
                   (mult (mult D (mult (inv_pos D HD) e2)) hh)
                   (mult e2 hh)).
  - exact (mult_assoc D (mult (inv_pos D HD) e2) hh).
  - exact (req_trans (mult (mult D (mult (inv_pos D HD) e2)) hh)
                     (mult (mult one e2) hh)
                     (mult e2 hh)
                     (req_mult_compat (mult D (mult (inv_pos D HD) e2)) (mult one e2)
                                      hh hh Hinner (req_refl hh))
                     (req_mult_compat (mult one e2) e2 hh hh
                                      (req_trans (mult one e2) (mult e2 one) e2
                                                 (mult_comm one e2) (mult_one e2))
                                      (req_refl hh))).
Qed.

(* ---- 件 4：differentiable_mult L25172 -> req_rdf_mult（Id 版 321 行主件；     *)
(*      误差分解使用 req_mult_diff_decomp@UpReqAlgebra L1162） ------------------ *)

Theorem req_rdf_mult : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => mult (f x) (g x)).
Proof.
  intros f g Hf Hg.
  exists (fun x => plus (mult (rdf_df f Hf x) (g x)) (mult (f x) (rdf_df g Hg x))).
  intros x eps Heps.
  pose (i2 := inv_pos (plus one one) req_two_pos).
  pose (eps4 := mult i2 (mult i2 eps)).
  pose (eps2 := mult i2 eps).
  assert (Heps4 : lt zero eps4).
  { exact (mult_positive i2 (mult i2 eps) (inv_pos_pos (plus one one) req_two_pos)
             (req_rdf_half_pos eps Heps)). }
  pose (Mf := plus (abs (f x)) one).
  assert (Hmf : lt zero Mf) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (f x)).
  pose (Mg := plus (abs (g x)) one).
  assert (Hmg : lt zero Mg) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (g x)).
  pose (eps_f := mult (inv_pos Mg Hmg) eps4).
  assert (Hef : lt zero eps_f).
  { exact (mult_positive (inv_pos Mg Hmg) eps4 (inv_pos_pos Mg Hmg) Heps4). }
  pose (eps_g := mult (inv_pos Mf Hmf) eps4).
  assert (Heg : lt zero eps_g).
  { exact (mult_positive (inv_pos Mf Hmf) eps4 (inv_pos_pos Mf Hmf) Heps4). }
  destruct (rdf_correct f Hf x eps_f Hef) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x eps_g Heg) as [dgd [Hg1 Hg2]].
  pose (Den := mult (plus (abs (rdf_df f Hf x)) eps_f) (plus (abs (rdf_df g Hg x)) eps_g)).
  assert (HD1 : lt zero (plus (abs (rdf_df f Hf x)) eps_f)).
  { exact (req_plus_le_lt_pos (abs (rdf_df f Hf x)) eps_f
             (abs_nonneg_plain (rdf_df f Hf x)) Hef). }
  assert (HD2 : lt zero (plus (abs (rdf_df g Hg x)) eps_g)).
  { exact (req_plus_le_lt_pos (abs (rdf_df g Hg x)) eps_g
             (abs_nonneg_plain (rdf_df g Hg x)) Heg). }
  assert (HDpos : lt zero Den).
  { exact (mult_positive (plus (abs (rdf_df f Hf x)) eps_f)
                         (plus (abs (rdf_df g Hg x)) eps_g) HD1 HD2). }
  pose (eps3 := mult (inv_pos Den HDpos) eps2).
  assert (He3 : lt zero eps3).
  { exact (mult_positive (inv_pos Den HDpos) eps2 (inv_pos_pos Den HDpos)
             (req_rdf_half_pos eps Heps)). }
  exists (min (min dfd dgd) eps3).
  split.
  - exact (min_pos (min dfd dgd) eps3 (min_pos dfd dgd Hd1 Hg1) He3).
  - intros h Hh.
    assert (Hh_d : lt (abs h) dfd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dfd
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) (min dfd dgd) Hh
                            (min_le_l_plain (min dfd dgd) eps3))
               (min_le_l_plain dfd dgd)). }
    assert (Hh_dg : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dfd dgd) dgd
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) (min dfd dgd) Hh
                            (min_le_l_plain (min dfd dgd) eps3))
               (min_le_r_plain dfd dgd)). }
    assert (Hh_le3 : le (abs h) eps3).
    { exact (lt_le_iff (abs h) eps3 (inl
               (lt_le_trans (abs h) (min (min dfd dgd) eps3) eps3 Hh
                            (min_le_r_plain (min dfd dgd) eps3)))). }
    assert (Hdf_bound : le (abs (req_minus (f (plus x h)) (f x)))
                           (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))).
    { exact (req_rdf_delta_bound (f (plus x h)) (f x) (rdf_df f Hf x) eps_f h
               (Hd2 h Hh_d)). }
    assert (Hdg_bound : le (abs (req_minus (g (plus x h)) (g x)))
                           (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
    { exact (req_rdf_delta_bound (g (plus x h)) (g x) (rdf_df g Hg x) eps_g h
               (Hg2 h Hh_dg)). }
    apply (le_id_l (abs (req_minus (mult (f (plus x h)) (g (plus x h)))
                                   (plus (mult (f x) (g x))
                                         (mult (plus (mult (rdf_df f Hf x) (g x))
                                                     (mult (f x) (rdf_df g Hg x))) h))))
                   (abs (plus (mult (f x) (req_minus (g (plus x h))
                                                      (plus (g x) (mult (rdf_df g Hg x) h))))
                              (plus (mult (g x) (req_minus (f (plus x h))
                                                           (plus (f x) (mult (rdf_df f Hf x) h))))
                                    (mult (req_minus (f (plus x h)) (f x))
                                          (req_minus (g (plus x h)) (g x))))))
                   (mult eps (abs h))).
    + exact (req_abs_compat
               (req_minus (mult (f (plus x h)) (g (plus x h)))
                          (plus (mult (f x) (g x))
                                (mult (plus (mult (rdf_df f Hf x) (g x))
                                            (mult (f x) (rdf_df g Hg x))) h)))
               (plus (mult (f x) (req_minus (g (plus x h))
                                            (plus (g x) (mult (rdf_df g Hg x) h))))
                     (plus (mult (g x) (req_minus (f (plus x h))
                                                  (plus (f x) (mult (rdf_df f Hf x) h))))
                           (mult (req_minus (f (plus x h)) (f x))
                                 (req_minus (g (plus x h)) (g x)))))
               (req_mult_diff_decomp f g (rdf_df f Hf) (rdf_df g Hg) x h)).
    + apply (le_trans _
               (plus (abs (mult (f x) (req_minus (g (plus x h))
                                                 (plus (g x) (mult (rdf_df g Hg x) h)))))
                     (abs (plus (mult (g x) (req_minus (f (plus x h))
                                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                                (mult (req_minus (f (plus x h)) (f x))
                                      (req_minus (g (plus x h)) (g x))))))).
      * exact (req_rdf_abs_triangle
                 (mult (f x) (req_minus (g (plus x h))
                                        (plus (g x) (mult (rdf_df g Hg x) h))))
                 (plus (mult (g x) (req_minus (f (plus x h))
                                              (plus (f x) (mult (rdf_df f Hf x) h))))
                       (mult (req_minus (f (plus x h)) (f x))
                             (req_minus (g (plus x h)) (g x))))).
* apply (le_trans _
               (plus (abs (mult (f x) (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h))))) (plus (abs (mult (g x) (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h))))) (abs (mult (req_minus (f (plus x h)) (f x)) (req_minus (g (plus x h)) (g x))))))).
        -- exact (le_plus_compat
                    (abs (mult (f x) (req_minus (g (plus x h))
                                                (plus (g x) (mult (rdf_df g Hg x) h)))))
                    (abs (mult (f x) (req_minus (g (plus x h))
                                                (plus (g x) (mult (rdf_df g Hg x) h)))))
                    (abs (plus (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h))))
                               (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x)))))
                    (plus (abs (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h)))))
                          (abs (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x)))))
                    (le_refl (abs (mult (f x) (req_minus (g (plus x h))
                                                         (plus (g x) (mult (rdf_df g Hg x) h))))))
                    (req_rdf_abs_triangle
                       (mult (g x) (req_minus (f (plus x h))
                                              (plus (f x) (mult (rdf_df f Hf x) h))))
                       (mult (req_minus (f (plus x h)) (f x))
                             (req_minus (g (plus x h)) (g x))))).
        -- (* 三项上界：eps4·|h|、eps4·|h|、eps2·|h| 合并 ≤ eps·|h| *)
           assert (Hb1 : le (abs (mult (f x) (req_minus (g (plus x h))
                                                        (plus (g x) (mult (rdf_df g Hg x) h)))))
                            (mult eps4 (abs h))).
           { assert (Hreqf : req (mult Mf eps_g) eps4).
             { exact (req_trans (mult Mf (mult (inv_pos Mf Hmf) eps4))
                                (mult (mult Mf (inv_pos Mf Hmf)) eps4) eps4
                       (mult_assoc Mf (inv_pos Mf Hmf) eps4)
                       (req_trans (mult (mult Mf (inv_pos Mf Hmf)) eps4)
                                  (mult one eps4) eps4
                                  (req_mult_compat (mult Mf (inv_pos Mf Hmf)) one eps4 eps4
                                                   (inv_pos_correct Mf Hmf) (req_refl eps4))
                                  (req_trans (mult one eps4) (mult eps4 one) eps4
                                             (mult_comm one eps4) (mult_one eps4)))). }
             apply (le_trans (abs (mult (f x) (req_minus (g (plus x h))
                                                         (plus (g x) (mult (rdf_df g Hg x) h)))))
                             (mult (abs (f x)) (mult eps_g (abs h)))
                             (mult eps4 (abs h))).
             - apply (le_trans (abs (mult (f x) (req_minus (g (plus x h))
                                                          (plus (g x) (mult (rdf_df g Hg x) h)))))
                               (mult (abs (f x))
                                     (abs (req_minus (g (plus x h))
                                                     (plus (g x) (mult (rdf_df g Hg x) h)))))
                               (mult (abs (f x)) (mult eps_g (abs h)))).
               + exact (req_rdf_abs_mult_le (f x)
                           (req_minus (g (plus x h)) (plus (g x) (mult (rdf_df g Hg x) h)))).
               + exact (req_le_mult_compat_r (abs (f x))
                            (abs (req_minus (g (plus x h))
                                            (plus (g x) (mult (rdf_df g Hg x) h))))
                            (mult eps_g (abs h))
                            (abs_nonneg_plain (f x)) (Hg2 h Hh_dg)).
             - exact (req_rdf_share (f x) Mf eps_g eps4 (abs h)
                        (req_abs_le_abs_plus_one (f x)) Heg Hreqf
                        (abs_nonneg_plain h)). }
           assert (Hb2 : le (abs (mult (g x) (req_minus (f (plus x h))
                                                        (plus (f x) (mult (rdf_df f Hf x) h)))))
                            (mult eps4 (abs h))).
           { assert (Hreqg : req (mult Mg eps_f) eps4).
             { exact (req_trans (mult Mg (mult (inv_pos Mg Hmg) eps4))
                                (mult (mult Mg (inv_pos Mg Hmg)) eps4) eps4
                       (mult_assoc Mg (inv_pos Mg Hmg) eps4)
                       (req_trans (mult (mult Mg (inv_pos Mg Hmg)) eps4)
                                  (mult one eps4) eps4
                                  (req_mult_compat (mult Mg (inv_pos Mg Hmg)) one eps4 eps4
                                                   (inv_pos_correct Mg Hmg) (req_refl eps4))
                                  (req_trans (mult one eps4) (mult eps4 one) eps4
                                             (mult_comm one eps4) (mult_one eps4)))). }
             apply (le_trans (abs (mult (g x) (req_minus (f (plus x h))
                                                         (plus (f x) (mult (rdf_df f Hf x) h)))))
                             (mult (abs (g x)) (mult eps_f (abs h)))
                             (mult eps4 (abs h))).
             - apply (le_trans (abs (mult (g x) (req_minus (f (plus x h))
                                                          (plus (f x) (mult (rdf_df f Hf x) h)))))
                               (mult (abs (g x))
                                     (abs (req_minus (f (plus x h))
                                                     (plus (f x) (mult (rdf_df f Hf x) h)))))
                               (mult (abs (g x)) (mult eps_f (abs h)))).
               + exact (req_rdf_abs_mult_le (g x)
                           (req_minus (f (plus x h)) (plus (f x) (mult (rdf_df f Hf x) h)))).
               + exact (req_le_mult_compat_r (abs (g x))
                            (abs (req_minus (f (plus x h))
                                            (plus (f x) (mult (rdf_df f Hf x) h))))
                            (mult eps_f (abs h))
                            (abs_nonneg_plain (g x)) (Hd2 h Hh_d)).
             - exact (req_rdf_share (g x) Mg eps_f eps4 (abs h)
                        (req_abs_le_abs_plus_one (g x)) Hef Hreqg
                        (abs_nonneg_plain h)). }
           assert (Hthird : le (abs (mult (req_minus (f (plus x h)) (f x))
                                          (req_minus (g (plus x h)) (g x))))
                               (mult eps2 (abs h))).
           { assert (HleA : le zero (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))).
             { exact (le_id_l zero (mult zero (abs h))
                        (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                        (req_sym (mult zero (abs h)) zero
                                 (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                            (mult_comm zero (abs h)) (mult_zero (abs h))))
                        (le_mult_compat_weak zero (plus (abs (rdf_df f Hf x)) eps_f) (abs h)
                         (abs_nonneg_plain h)
                         (lt_le_iff zero (plus (abs (rdf_df f Hf x)) eps_f) (inl HD1)))). }
             assert (HleB : le zero (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
             { exact (le_id_l zero (mult zero (abs h))
                        (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                        (req_sym (mult zero (abs h)) zero
                                 (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                            (mult_comm zero (abs h)) (mult_zero (abs h))))
                        (le_mult_compat_weak zero (plus (abs (rdf_df g Hg x)) eps_g) (abs h)
                         (abs_nonneg_plain h)
                         (lt_le_iff zero (plus (abs (rdf_df g Hg x)) eps_g) (inl HD2)))). }
             apply (le_trans (abs (mult (req_minus (f (plus x h)) (f x))
                                        (req_minus (g (plus x h)) (g x))))
                             (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                   (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                             (mult eps2 (abs h))).
             - apply (le_trans (abs (mult (req_minus (f (plus x h)) (f x))
                                         (req_minus (g (plus x h)) (g x))))
                               (mult (abs (req_minus (f (plus x h)) (f x)))
                                     (abs (req_minus (g (plus x h)) (g x))))
                               (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                     (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))).
               + exact (req_rdf_abs_mult_le (req_minus (f (plus x h)) (f x))
                           (req_minus (g (plus x h)) (g x))).
               + exact (le_trans (mult (abs (req_minus (f (plus x h)) (f x)))
                                       (abs (req_minus (g (plus x h)) (g x))))
                                 (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                       (abs (req_minus (g (plus x h)) (g x))))
                                 (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                       (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                            (le_mult_compat_weak (abs (req_minus (f (plus x h)) (f x)))
                              (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                              (abs (req_minus (g (plus x h)) (g x)))
                              (abs_nonneg_plain (req_minus (g (plus x h)) (g x)))
                              Hdf_bound)
                            (req_le_mult_compat_r
                              (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                              (abs (req_minus (g (plus x h)) (g x)))
                              (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                              HleA Hdg_bound)).
             - exact (le_trans (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                     (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                               (mult Den (mult (abs h) (abs h)))
                               (mult eps2 (abs h))
                       (le_id_l (mult (mult (plus (abs (rdf_df f Hf x)) eps_f) (abs h))
                                      (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)))
                                (mult Den (mult (abs h) (abs h)))
                                (mult Den (mult (abs h) (abs h)))
                                (req_rdf_four_mult (plus (abs (rdf_df f Hf x)) eps_f)
                                                   (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                                (le_refl (mult Den (mult (abs h) (abs h)))))
                       (le_trans (mult Den (mult (abs h) (abs h)))
                                 (mult Den (mult eps3 (abs h)))
                                 (mult eps2 (abs h))
                         (req_le_mult_compat_r Den (mult (abs h) (abs h)) (mult eps3 (abs h))
                          (lt_le_iff zero Den (inl HDpos))
                          (le_mult_compat_weak (abs h) eps3 (abs h)
                           (abs_nonneg_plain h) Hh_le3))
                         (le_id_l (mult Den (mult eps3 (abs h))) (mult eps2 (abs h))
                          (mult eps2 (abs h))
                          (req_rdf_inv_pair Den HDpos eps2 (abs h))
                          (le_refl (mult eps2 (abs h)))))). }
           apply (le_trans _
                     (plus (mult eps4 (abs h))
                           (plus (mult eps4 (abs h)) (mult eps2 (abs h))))).
           ++ exact (le_plus_compat
                       (abs (mult (f x) (req_minus (g (plus x h))
                                                   (plus (g x) (mult (rdf_df g Hg x) h)))))
                       (mult eps4 (abs h))
                       (plus (abs (mult (g x) (req_minus (f (plus x h))
                                                         (plus (f x) (mult (rdf_df f Hf x) h)))))
                             (abs (mult (req_minus (f (plus x h)) (f x))
                                        (req_minus (g (plus x h)) (g x)))))
                       (plus (mult eps4 (abs h)) (mult eps2 (abs h)))
                       Hb1
                       (le_plus_compat
                          (abs (mult (g x) (req_minus (f (plus x h))
                                                      (plus (f x) (mult (rdf_df f Hf x) h)))))
                          (mult eps4 (abs h))
                          (abs (mult (req_minus (f (plus x h)) (f x))
                                     (req_minus (g (plus x h)) (g x))))
                          (mult eps2 (abs h))
                          Hb2 Hthird)).
           ++ assert (Hj1 : req (plus (mult eps4 (abs h))
                                      (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                                 (mult eps (abs h))).
              { apply (req_trans (plus (mult eps4 (abs h))
                                       (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                                 (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                       (mult eps2 (abs h)))
                                 (mult eps (abs h))).
                - exact (plus_assoc (mult eps4 (abs h)) (mult eps4 (abs h))
                                    (mult eps2 (abs h))).
                - apply (req_trans (plus (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                         (mult eps2 (abs h)))
                                   (plus (mult (mult i2 eps) (abs h))
                                         (mult (mult i2 eps) (abs h)))
                                   (mult eps (abs h))).
                  + apply (req_plus_compat (plus (mult eps4 (abs h)) (mult eps4 (abs h)))
                                           (mult (mult i2 eps) (abs h))
                                           (mult eps2 (abs h)) (mult (mult i2 eps) (abs h))).
                    -- exact (req_rdf_quarter_pair_req eps (abs h)).
                    -- apply req_refl.
                  + exact (req_rdf_half_pair_req eps (abs h)).
              }
              assert (Hj2 : le zero (mult eps (abs h))).
              { exact (le_id_l zero (mult zero (abs h)) (mult eps (abs h))
                         (req_sym (mult zero (abs h)) zero
                                  (req_trans (mult zero (abs h)) (mult (abs h) zero) zero
                                             (mult_comm zero (abs h)) (mult_zero (abs h))))
                         (le_mult_compat_weak zero eps (abs h) (abs_nonneg_plain h)
                          (lt_le_iff zero eps (inl Heps)))). }
              exact (le_id_l (plus (mult eps4 (abs h))
                                   (plus (mult eps4 (abs h)) (mult eps2 (abs h))))
                             (mult eps (abs h)) (mult eps (abs h))
                             Hj1 (le_refl (mult eps (abs h)))).
Qed.


(* ---- 件 5：differentiable_opp L25551 -> req_rdf_opp ------------------------ *)

Theorem req_rdf_opp : forall f : R -> R, reqRDF f -> reqRDF (fun x => opp (f x)).
Proof.
  intros f Hf.
  exists (fun x => opp (rdf_df f Hf x)).
  intros x eps Heps.
  destruct (rdf_correct f Hf x eps Heps) as [delta [Hd1 Hd2]].
  exists delta.
  split.
  - exact Hd1.
  - intros h Hh.
    assert (Hz : req (req_minus (opp (f (plus x h)))
                                (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                     (opp (req_minus (f (plus x h))
                                     (plus (f x) (mult (rdf_df f Hf x) h))))).
    { assert (Hinner : req (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                           (plus (f x) (mult (rdf_df f Hf x) h))).
      { apply (req_trans (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                         (plus (opp (opp (f x))) (opp (mult (opp (rdf_df f Hf x)) h)))
                         (plus (f x) (mult (rdf_df f Hf x) h))).
        - exact (req_opp_plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)).
        - apply (req_plus_compat (opp (opp (f x))) (f x)
                                 (opp (mult (opp (rdf_df f Hf x)) h))
                                 (mult (rdf_df f Hf x) h)).
          + exact (req_double_neg (f x)).
          + exact (req_trans (opp (mult (opp (rdf_df f Hf x)) h))
                             (opp (opp (mult (rdf_df f Hf x) h)))
                             (mult (rdf_df f Hf x) h)
                             (req_opp_compat (mult (opp (rdf_df f Hf x)) h)
                                             (opp (mult (rdf_df f Hf x) h))
                                             (req_opp_mult_r (rdf_df f Hf x) h))
                             (req_double_neg (mult (rdf_df f Hf x) h))). }
      unfold req_minus.
      apply (req_trans (plus (opp (f (plus x h)))
                             (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h))))
                       (plus (opp (f (plus x h)))
                             (plus (f x) (mult (rdf_df f Hf x) h)))
                       (opp (plus (f (plus x h))
                                  (opp (plus (f x) (mult (rdf_df f Hf x) h)))))).
        - exact (req_plus_compat (opp (f (plus x h))) (opp (f (plus x h)))
                                 (opp (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h)))
                                 (plus (f x) (mult (rdf_df f Hf x) h))
                                 (req_refl (opp (f (plus x h)))) Hinner).
        - exact (req_sym (opp (req_minus (f (plus x h))
                                         (plus (f x) (mult (rdf_df f Hf x) h))))
                         (plus (opp (f (plus x h)))
                               (plus (f x) (mult (rdf_df f Hf x) h)))
                         (req_opp_minus (f (plus x h))
                                        (plus (f x) (mult (rdf_df f Hf x) h)))). }
    apply (le_trans (abs (req_minus (opp (f (plus x h)))
                                    (plus (opp (f x)) (mult (opp (rdf_df f Hf x)) h))))
                    (abs (req_minus (f (plus x h))
                                    (plus (f x) (mult (rdf_df f Hf x) h))))
                    (mult eps (abs h))).
      + exact (le_id_l (abs (req_minus (opp (f (plus x h)))
                                       (plus (opp (f x))
                                             (mult (opp (rdf_df f Hf x)) h))))
                       (abs (req_minus (f (plus x h))
                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                       (abs (req_minus (f (plus x h))
                                       (plus (f x) (mult (rdf_df f Hf x) h))))
                       (req_trans (abs (req_minus (opp (f (plus x h)))
                                                  (plus (opp (f x))
                                                        (mult (opp (rdf_df f Hf x)) h))))
                                  (abs (opp (req_minus (f (plus x h))
                                                       (plus (f x)
                                                             (mult (rdf_df f Hf x) h)))))
                                  (abs (req_minus (f (plus x h))
                                                  (plus (f x) (mult (rdf_df f Hf x) h))))
                                  (req_abs_compat
                                     (req_minus (opp (f (plus x h)))
                                                (plus (opp (f x))
                                                      (mult (opp (rdf_df f Hf x)) h)))
                                     (opp (req_minus (f (plus x h))
                                                     (plus (f x)
                                                           (mult (rdf_df f Hf x) h))))
                                     Hz)
                                  (abs_opp (req_minus (f (plus x h))
                                                      (plus (f x)
                                                            (mult (rdf_df f Hf x) h)))))
                       (le_refl (abs (req_minus (f (plus x h))
                                                (plus (f x)
                                                      (mult (rdf_df f Hf x) h)))))).
      + exact (Hd2 h Hh).
Qed.

(* ---- 件 6：differentiable_minus L25596 -> req_rdf_minus ------------------- *)
(*      req_minus δ 透明：plus∘opp 使用后目标转换闭合（unfold 后直接匹配） --------- *)

Theorem req_rdf_minus : forall f g : R -> R,
  reqRDF f -> reqRDF g -> reqRDF (fun x => req_minus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  pose proof (req_rdf_opp g Hg) as Hopp.
  pose proof (req_rdf_plus f (fun x => opp (g x)) Hf Hopp) as Hp.
  exists (rdf_df (fun x => plus (f x) (opp (g x))) Hp).
  intros x eps Heps.
  destruct (rdf_correct (fun x => plus (f x) (opp (g x))) Hp x eps Heps)
    as [delta [Hd1 Hd2]].
  exists delta.
  split.
  - exact Hd1.
  - exact (fun h Hh => Hd2 h Hh).
Qed.

(* ---- 件 7：differentiable_power_nat L25631 -> req_power_nat +               *)
(*        req_rdf_power_nat（归纳 + req_rdf_mult 载体重建） --------------------- *)

Fixpoint req_power_nat (n : nat) (x : R) : R :=
  match n with
  | Datatypes.O => one
  | Datatypes.S n' => mult x (req_power_nat n' x)
  end.

Theorem req_rdf_power_nat : forall n : nat,
  reqRDF (fun x => req_power_nat (Datatypes.S n) x).
Proof.
  intro n.
  induction n as [| n' IH].
  - exists (fun _ => one).
    intros x eps Heps.
    exists one.
    split.
    + exact one_pos.
    + intros h Hh.
      assert (Herr : req (req_minus (mult (plus x h) one)
                                    (plus (mult x one) (mult one h))) zero).
      { apply (req_minus_self_zero (mult (plus x h) one)
                                   (plus (mult x one) (mult one h))).
        exact (req_trans (mult (plus x h) one) (plus x h)
                         (plus (mult x one) (mult one h))
                         (mult_one (plus x h))
                         (req_sym (plus (mult x one) (mult one h)) (plus x h)
                                  (req_plus_compat (mult x one) x (mult one h) h
                                                   (mult_one x)
                                                   (req_trans (mult one h) (mult h one) h
                                                      (mult_comm one h) (mult_one h))))). }
      exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (mult (plus x h) one)
                                            (plus (mult x one) (mult one h)))
                                 eps h Heps Herr).
  - exact (req_rdf_mult (fun y => y) (fun y => req_power_nat (Datatypes.S n') y)
                        req_rdf_id IH).
Qed.

(* ---- 公共机器件 3：A == (A−Y)+Y（compose 分解引擎） ------------------------- *)

Lemma req_rdf_minus_pair : forall A Y : R, req A (plus (req_minus A Y) Y).
Proof.
  intros A Y.
  apply (req_sym (plus (req_minus A Y) Y) A).
  unfold req_minus.
  apply (req_trans (plus (plus A (opp Y)) Y) (plus A (plus (opp Y) Y)) A).
  - exact (req_sym (plus A (plus (opp Y) Y)) (plus (plus A (opp Y)) Y)
                   (plus_assoc A (opp Y) Y)).
  - apply (req_trans (plus A (plus (opp Y) Y)) (plus A zero) A).
    + exact (req_plus_compat A A (plus (opp Y) Y) zero (req_refl A) (req_plus_opp_l Y)).
    + exact (plus_zero A).
Qed.


(* (a+b)−c == a+(b−c)（Id minus_plus_zero_r L26076 req 对位，mse/compose 使用） *)
Lemma req_minus_plus_zero_r : forall a b c : R,
  req (req_minus (plus a b) c) (plus a (req_minus b c)).
Proof.
  intros a b c.
  unfold req_minus.
  exact (req_sym (plus a (plus b (opp c))) (plus (plus a b) (opp c))
                 (plus_assoc a b (opp c))).
Qed.



Lemma req_rdf_compose_diff_decomp : forall A B C D G g0 h : R,
  req (req_minus A (plus B (mult (mult C D) h)))
      (plus (req_minus A (plus B (mult C (req_minus G g0))))
            (mult C (req_minus (req_minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  apply (req_trans (req_minus A (plus B (mult (mult C D) h)))
                   (req_minus A (plus B (mult C (mult D h))))
                   (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (req_minus (req_minus G g0) (mult D h))))).
  - exact (req_rdf_minus_compat_r A (plus B (mult (mult C D) h))
             (plus B (mult C (mult D h)))
             (req_plus_compat B B (mult (mult C D) h) (mult C (mult D h))
                              (req_refl B)
                              (req_sym (mult C (mult D h)) (mult (mult C D) h)
                                       (mult_assoc C D h)))).
  - apply (req_trans (req_minus A (plus B (mult C (mult D h))))
                     (plus (req_minus A (plus B (mult C (req_minus G g0))))
                           (req_minus (plus B (mult C (req_minus G g0)))
                                      (plus B (mult C (mult D h)))))
                     (plus (req_minus A (plus B (mult C (req_minus G g0))))
                           (mult C (req_minus (req_minus G g0) (mult D h))))).
    + apply (req_trans (req_minus A (plus B (mult C (mult D h))))
                       (req_minus (plus (req_minus A (plus B (mult C (req_minus G g0))))
                                        (plus B (mult C (req_minus G g0))))
                                  (plus B (mult C (mult D h))))
                       (plus (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus (plus B (mult C (req_minus G g0)))
                                        (plus B (mult C (mult D h)))))).
      -- exact (req_rdf_minus_compat_l A
                    (plus (req_minus A (plus B (mult C (req_minus G g0))))
                          (plus B (mult C (req_minus G g0))))
                    (plus B (mult C (mult D h)))
                    (req_rdf_minus_pair A (plus B (mult C (req_minus G g0))))).
      -- exact (req_minus_plus_zero_r (req_minus A (plus B (mult C (req_minus G g0))))
                                         (plus B (mult C (req_minus G g0)))
                                         (plus B (mult C (mult D h)))).
    + apply (req_plus_compat (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus A (plus B (mult C (req_minus G g0))))
                             (req_minus (plus B (mult C (req_minus G g0)))
                                        (plus B (mult C (mult D h))))
                             (mult C (req_minus (req_minus G g0) (mult D h)))
                             (req_refl (req_minus A (plus B (mult C (req_minus G g0)))))).
      * apply (req_trans (req_minus (plus B (mult C (req_minus G g0)))
                                    (plus B (mult C (mult D h))))
                         (plus (req_minus B B)
                               (req_minus (mult C (req_minus G g0))
                                          (mult C (mult D h))))
                         (mult C (req_minus (req_minus G g0) (mult D h)))).
        -- exact (req_minus_plus_distr B (mult C (req_minus G g0)) B
                                           (mult C (mult D h))).
        -- exact (req_trans (plus (req_minus B B)
                                  (req_minus (mult C (req_minus G g0)) (mult C (mult D h))))
                            (plus zero (mult C (req_minus (req_minus G g0) (mult D h))))
                            (mult C (req_minus (req_minus G g0) (mult D h)))
                            (req_plus_compat (req_minus B B) zero
                                             (req_minus (mult C (req_minus G g0)) (mult C (mult D h)))
                                             (mult C (req_minus (req_minus G g0) (mult D h)))
                                             (req_minus_self_zero B B (req_refl B))
                                             (req_sym (mult C (req_minus (req_minus G g0) (mult D h)))
                                                      (req_minus (mult C (req_minus G g0))
                                                                 (mult C (mult D h)))
                                                      (req_mult_minus_distr_l C (req_minus G g0)
                                                                              (mult D h))))
                            (req_plus_zero_l (mult C (req_minus (req_minus G g0) (mult D h))))).
Qed.

(* ---- 件 8：differentiable_compose L25762 -> req_rdf_compose ----------------- *)

(* 函数 req-兼容槽（T2①；Id 靠 Leibniz 免费换形，req 侧诚实假设位——登记表第 5 条） *)
Theorem req_rdf_compose : forall f g : R -> R,
  reqRDF f -> reqRDF g ->
  (forall u v : R, req u v -> req (f u) (f v)) ->
  reqRDF (fun x => f (g x)).
Proof.
  intros f g Hf Hg Hfc.
  exists (fun x => mult (rdf_df f Hf (g x)) (rdf_df g Hg x)).
  intros x eps Heps.
  pose (i2 := inv_pos (plus one one) req_two_pos).
  pose (eps4 := mult i2 (mult i2 eps)).
  assert (Heps4 : lt zero eps4).
  { exact (mult_positive i2 (mult i2 eps) (inv_pos_pos (plus one one) req_two_pos)
             (req_rdf_half_pos eps Heps)). }
  pose (M := plus (abs (rdf_df f Hf (g x))) one).
  assert (HM : lt zero M) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (rdf_df f Hf (g x))).
  pose (L := plus (abs (rdf_df g Hg x)) one).
  assert (HL : lt zero L) by exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (rdf_df g Hg x)).
  pose (eps_f := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_f : lt zero eps_f).
  { exact (min_pos one (mult (inv_pos L HL) eps4) one_pos
             (mult_positive (inv_pos L HL) eps4 (inv_pos_pos L HL) Heps4)). }
  pose (eps_g := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_g : lt zero eps_g).
  { exact (min_pos one (mult (inv_pos M HM) eps4) one_pos
             (mult_positive (inv_pos M HM) eps4 (inv_pos_pos M HM) Heps4)). }
  destruct (rdf_correct f Hf (g x) eps_f Heps_f) as [dfd [Hd1 Hd2]].
  destruct (rdf_correct g Hg x eps_g Heps_g) as [dgd [Hg1 Hg2]].
  exists (min dgd (min one (mult (inv_pos L HL) dfd))).
  split.
  - exact (min_pos dgd (min one (mult (inv_pos L HL) dfd)) Hg1
             (min_pos one (mult (inv_pos L HL) dfd) one_pos
              (mult_positive (inv_pos L HL) dfd (inv_pos_pos L HL) Hd1))).
  - intros h Hh.
    assert (Hh_dgd : lt (abs h) dgd).
    { exact (lt_le_trans (abs h) (min dgd (min one (mult (inv_pos L HL) dfd))) dgd Hh
                         (min_le_l_plain dgd (min one (mult (inv_pos L HL) dfd)))). }
    assert (Hh_dfd : lt (abs h) (mult (inv_pos L HL) dfd)).
    { exact (lt_le_trans (abs h) (min one (mult (inv_pos L HL) dfd))
                         (mult (inv_pos L HL) dfd)
                         (lt_le_trans (abs h) (min dgd (min one (mult (inv_pos L HL) dfd)))
                                      (min one (mult (inv_pos L HL) dfd)) Hh
                                      (min_le_r_plain dgd (min one (mult (inv_pos L HL) dfd))))
                         (min_le_r_plain one (mult (inv_pos L HL) dfd))). }
    assert (HDg_bound : le (abs (req_minus (g (plus x h)) (g x)))
                           (mult L (abs h))).
    { assert (Hstep : le (abs (req_minus (g (plus x h)) (g x)))
                         (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))).
      { exact (req_rdf_delta_bound (g (plus x h)) (g x) (rdf_df g Hg x) eps_g h
                 (Hg2 h Hh_dgd)). }
      assert (Heg1 : le eps_g one).
      { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
      assert (Hpos : lt zero (plus (abs (rdf_df g Hg x)) eps_g)).
      { exact (req_plus_le_lt_pos (abs (rdf_df g Hg x)) eps_g
                 (abs_nonneg_plain (rdf_df g Hg x)) Heps_g). }
      assert (Hleg1 : le (plus (abs (rdf_df g Hg x)) eps_g)
                          (plus (abs (rdf_df g Hg x)) one)).
      { exact (le_id_r (plus (abs (rdf_df g Hg x)) eps_g)
                       (plus one (abs (rdf_df g Hg x)))
                       (plus (abs (rdf_df g Hg x)) one)
                       (plus_comm one (abs (rdf_df g Hg x)))
                       (le_id_l (plus (abs (rdf_df g Hg x)) eps_g)
                                (plus eps_g (abs (rdf_df g Hg x)))
                                (plus one (abs (rdf_df g Hg x)))
                                (plus_comm (abs (rdf_df g Hg x)) eps_g)
                                (le_plus_compat eps_g one (abs (rdf_df g Hg x))
                                                (abs (rdf_df g Hg x))
                                                Heg1
                                                (le_refl (abs (rdf_df g Hg x)))))). }
      assert (Hleg2 : le (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                          (mult (plus (abs (rdf_df g Hg x)) one) (abs h))).
      { exact (le_mult_compat_weak (plus (abs (rdf_df g Hg x)) eps_g)
                   (plus (abs (rdf_df g Hg x)) one) (abs h) (abs_nonneg_plain h) Hleg1). }
      assert (Hleg3 : req (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))).
      { exact (req_mult_compat (plus (abs (rdf_df g Hg x)) one) L (abs h) (abs h)
                               (req_refl (plus (abs (rdf_df g Hg x)) one)) (req_refl (abs h))). }
      assert (Hleg4 : le (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))).
      { exact (le_id_l (mult (plus (abs (rdf_df g Hg x)) one) (abs h))
                       (mult L (abs h)) (mult L (abs h)) Hleg3 (le_refl (mult L (abs h)))). }
      assert (Hleg5 : le (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h)) (mult L (abs h))).
      { exact (le_trans (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                        (mult (plus (abs (rdf_df g Hg x)) one) (abs h)) (mult L (abs h))
                        Hleg2 Hleg4). }
      exact (le_trans (abs (req_minus (g (plus x h)) (g x)))
                      (mult (plus (abs (rdf_df g Hg x)) eps_g) (abs h))
                      (mult L (abs h)) Hstep Hleg5). }
    assert (HdfDg : lt (abs (req_minus (g (plus x h)) (g x))) dfd).
    { apply (le_lt_trans (abs (req_minus (g (plus x h)) (g x)))
                         (mult L (abs h)) dfd).
      - exact HDg_bound.
      - assert (Hraw : lt (mult (abs h) L) (mult (mult (inv_pos L HL) dfd) L)).
        { exact (lt_mult_compat (abs h) (mult (inv_pos L HL) dfd) L HL Hh_dfd). }
        exact (lt_id_l (mult L (abs h)) (mult (abs h) L) dfd
                       (mult_comm L (abs h))
                       (lt_id_r (mult (abs h) L)
                                (mult (mult (inv_pos L HL) dfd) L) dfd
                                (req_trans (mult (mult (inv_pos L HL) dfd) L)
                                           (mult L (mult (inv_pos L HL) dfd)) dfd
                                           (mult_comm (mult (inv_pos L HL) dfd) L)
                                           (req_rdf_inv_cancel L dfd HL Hd1))
                                Hraw)). }
    assert (HT1 : le (abs (req_minus (f (g (plus x h)))
                                     (plus (f (g x)) (mult (rdf_df f Hf (g x))
                                                           (req_minus (g (plus x h)) (g x))))))
                        (mult eps4 (abs h))).
    { apply (le_trans (abs (req_minus (f (g (plus x h)))
                                      (plus (f (g x))
                                            (mult (rdf_df f Hf (g x))
                                                  (req_minus (g (plus x h)) (g x))))))
                      (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                      (mult eps4 (abs h))).
      - exact (le_id_l (abs (req_minus (f (g (plus x h)))
                                       (plus (f (g x))
                                             (mult (rdf_df f Hf (g x))
                                                   (req_minus (g (plus x h)) (g x))))))
                       (abs (req_minus (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                                       (plus (f (g x))
                                             (mult (rdf_df f Hf (g x))
                                                   (req_minus (g (plus x h)) (g x))))))
                       (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                       (req_abs_compat
                          (req_minus (f (g (plus x h)))
                                     (plus (f (g x))
                                           (mult (rdf_df f Hf (g x))
                                                 (req_minus (g (plus x h)) (g x)))))
                          (req_minus (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                                     (plus (f (g x))
                                           (mult (rdf_df f Hf (g x))
                                                 (req_minus (g (plus x h)) (g x)))))
                          (req_rdf_minus_compat_l (f (g (plus x h)))
                             (f (plus (g x) (req_minus (g (plus x h)) (g x))))
                             (plus (f (g x))
                                   (mult (rdf_df f Hf (g x))
                                         (req_minus (g (plus x h)) (g x))))
                             (Hfc (g (plus x h))
                                  (plus (g x) (req_minus (g (plus x h)) (g x)))
                                  (req_sym (plus (g x) (req_minus (g (plus x h)) (g x)))
                                           (g (plus x h))
                                           (req_minus_plus_cancel (g x) (g (plus x h)))))))
                       (Hd2 (req_minus (g (plus x h)) (g x)) HdfDg)).
      - assert (Hsc : le (mult eps_f L) eps4).
        { exact (le_trans (mult eps_f L)
                          (mult (mult (inv_pos L HL) eps4) L) eps4
                          (le_mult_compat_weak eps_f (mult (inv_pos L HL) eps4) L
                           (lt_le_iff zero L (inl HL))
                           (min_le_r_plain one (mult (inv_pos L HL) eps4)))
                          (req_rdf_inv_scale_le L eps4 HL)). }
        assert (Hsc2 : le (mult eps_f (mult L (abs h))) (mult eps4 (abs h))).
        { exact (le_trans (mult eps_f (mult L (abs h)))
                          (mult (mult eps_f L) (abs h)) (mult eps4 (abs h))
                          (le_id_l (mult eps_f (mult L (abs h)))
                                   (mult (mult eps_f L) (abs h))
                                   (mult (mult eps_f L) (abs h))
                                   (mult_assoc eps_f L (abs h))
                                   (le_refl (mult (mult eps_f L) (abs h))))
                          (le_mult_compat_weak (mult eps_f L) eps4 (abs h)
                           (abs_nonneg_plain h) Hsc)). }
        exact (le_trans (mult eps_f (abs (req_minus (g (plus x h)) (g x))))
                        (mult eps_f (mult L (abs h))) (mult eps4 (abs h))
                        (req_le_mult_compat_r eps_f (abs (req_minus (g (plus x h)) (g x)))
                                              (mult L (abs h))
                                              (lt_le_iff zero eps_f (inl Heps_f)) HDg_bound)
                        Hsc2). }
    assert (HT2 : le (abs (mult (rdf_df f Hf (g x))
                                (req_minus (req_minus (g (plus x h)) (g x))
                                           (mult (rdf_df g Hg x) h))))
                       (mult eps4 (abs h))).
    { apply (le_trans (abs (mult (rdf_df f Hf (g x))
                                 (req_minus (req_minus (g (plus x h)) (g x))
                                            (mult (rdf_df g Hg x) h))))
                      (mult (abs (rdf_df f Hf (g x)))
                            (mult eps_g (abs h)))
                      (mult eps4 (abs h))).
      - apply (le_trans (abs (mult (rdf_df f Hf (g x))
                                   (req_minus (req_minus (g (plus x h)) (g x))
                                              (mult (rdf_df g Hg x) h))))
                        (mult (abs (rdf_df f Hf (g x)))
                              (abs (req_minus (req_minus (g (plus x h)) (g x))
                                              (mult (rdf_df g Hg x) h))))
                        (mult (abs (rdf_df f Hf (g x))) (mult eps_g (abs h)))).
        + exact (req_rdf_abs_mult_le (rdf_df f Hf (g x))
                    (req_minus (req_minus (g (plus x h)) (g x))
                               (mult (rdf_df g Hg x) h))).
        + exact (req_le_mult_compat_r (abs (rdf_df f Hf (g x)))
                    (abs (req_minus (req_minus (g (plus x h)) (g x))
                                    (mult (rdf_df g Hg x) h)))
                    (mult eps_g (abs h))
                    (abs_nonneg_plain (rdf_df f Hf (g x)))
                    (le_id_l (abs (req_minus (req_minus (g (plus x h)) (g x))
                                             (mult (rdf_df g Hg x) h)))
                             (abs (req_minus (g (plus x h))
                                             (plus (g x) (mult (rdf_df g Hg x) h))))
                             (mult eps_g (abs h))
                             (req_abs_compat (req_minus (req_minus (g (plus x h)) (g x))
                                                        (mult (rdf_df g Hg x) h))
                                             (req_minus (g (plus x h))
                                                        (plus (g x)
                                                              (mult (rdf_df g Hg x) h)))
                                             (req_sym (req_minus (g (plus x h))
                                                                 (plus (g x)
                                                                       (mult (rdf_df g Hg x) h)))
                                                      (req_minus (req_minus (g (plus x h)) (g x))
                                                                 (mult (rdf_df g Hg x) h))
                                                      (req_minus_plus_r (g (plus x h)) (g x)
                                                                        (mult (rdf_df g Hg x) h))))
                             (Hg2 h Hh_dgd))).
      - apply (le_trans (mult (abs (rdf_df f Hf (g x))) (mult eps_g (abs h)))
                        (mult M (mult eps_g (abs h)))
                        (mult eps4 (abs h))).
        + exact (le_mult_compat_weak (abs (rdf_df f Hf (g x))) M (mult eps_g (abs h))
                   (req_rdf_zero_le_mult_abs abs_nonneg_plain eps_g h Heps_g)
                    (req_abs_le_abs_plus_one (rdf_df f Hf (g x)))).
        + assert (HreqM : le (mult M eps_g) eps4).
          { exact (le_trans (mult M eps_g)
                            (mult M (mult (inv_pos M HM) eps4)) eps4
                            (req_le_mult_compat_r M eps_g (mult (inv_pos M HM) eps4)
                             (lt_le_iff zero M (inl HM))
                             (min_le_r_plain one (mult (inv_pos M HM) eps4)))
                            (le_id_l (mult M (mult (inv_pos M HM) eps4)) eps4 eps4
                             (req_trans (mult M (mult (inv_pos M HM) eps4))
                                        (mult (mult M (inv_pos M HM)) eps4) eps4
                                        (mult_assoc M (inv_pos M HM) eps4)
                                        (req_trans (mult (mult M (inv_pos M HM)) eps4)
                                                   (mult one eps4) eps4
                                                   (req_mult_compat (mult M (inv_pos M HM)) one
                                                                    eps4 eps4
                                                                    (inv_pos_correct M HM)
                                                                    (req_refl eps4))
                                                   (req_trans (mult one eps4) (mult eps4 one) eps4
                                                              (mult_comm one eps4)
                                                              (mult_one eps4))))
                             (le_refl eps4))). }
          exact (le_trans (mult M (mult eps_g (abs h)))
                          (mult (mult M eps_g) (abs h)) (mult eps4 (abs h))
                          (le_id_l (mult M (mult eps_g (abs h)))
                                   (mult (mult M eps_g) (abs h))
                                   (mult (mult M eps_g) (abs h))
                                   (mult_assoc M eps_g (abs h))
                                   (le_refl (mult (mult M eps_g) (abs h))))
                          (le_mult_compat_weak (mult M eps_g) eps4 (abs h)
                           (abs_nonneg_plain h) HreqM)).
          }
    apply (le_id_l (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (rdf_df f Hf (g x)) (rdf_df g Hg x)) h)))) (abs (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (mult eps (abs h))).
    + exact (req_abs_compat (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (mult (rdf_df f Hf (g x)) (rdf_df g Hg x)) h))) (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (req_rdf_compose_diff_decomp (f (g (plus x h))) (f (g x)) (rdf_df f Hf (g x)) (rdf_df g Hg x) (g (plus x h)) (g x) h)).
+ exact (le_trans (abs (plus (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (plus (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (mult eps (abs h)) (req_rdf_abs_triangle (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x))))) (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (le_trans (plus (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h))))) (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps (abs h)) (le_plus_compat (abs (req_minus (f (g (plus x h))) (plus (f (g x)) (mult (rdf_df f Hf (g x)) (req_minus (g (plus x h)) (g x)))))) (mult eps4 (abs h)) (abs (mult (rdf_df f Hf (g x)) (req_minus (req_minus (g (plus x h)) (g x)) (mult (rdf_df g Hg x) h)))) (mult eps4 (abs h)) HT1 HT2) (le_trans (plus (mult eps4 (abs h)) (mult eps4 (abs h))) (mult eps (abs h)) (mult eps (abs h)) (req_rdf_quarter_pair_le_final eps (abs h) Heps (abs_nonneg_plain h)) (le_refl (mult eps (abs h)))))).
Qed.

(* ---- 辅件：(a+b)−c == a+(b−c)（mse/compose 分解引擎） ------------------------ *)

Lemma req_rdf_minus_plus_zero_r : forall a b c : R,
  req (req_minus (plus a b) c) (plus (req_minus a c) b).
Proof.
  intros a b c.
  unfold req_minus.
  apply (req_trans (plus (plus a b) (opp c)) (plus a (plus b (opp c)))
                   (plus (plus a (opp c)) b)).
  - exact (req_sym (plus a (plus b (opp c))) (plus (plus a b) (opp c))
                   (plus_assoc a b (opp c))).
  - apply (req_trans (plus a (plus b (opp c))) (plus a (plus (opp c) b))
                     (plus (plus a (opp c)) b)).
    + exact (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
                             (req_refl a) (plus_comm b (opp c))).
    + exact (plus_assoc a (opp c) b).
Qed.

(* ---- 辅件：(x+h−t)² − ((x−t)² + 2(x−t)h) == h²（Id square_diff_expand        *)


Lemma req_rdf_square_diff_expand : forall x target h : R,
  req (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
            (plus (mult (req_minus x target) (req_minus x target))
                  (mult (mult (plus one one) (req_minus x target)) h)))
       (mult h h).
Proof.
  intros x target h.
  assert (Hv : req (req_minus (plus x h) target) (plus (req_minus x target) h)).
  { exact (req_rdf_minus_plus_zero_r x h target). }
  assert (Hpair : req (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                      (mult (mult (plus one one) (req_minus x target)) h)).
  { apply (req_trans (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                     (mult (plus (req_minus x target) (req_minus x target)) h)
                     (mult (mult (plus one one) (req_minus x target)) h)).
    - exact (req_trans (plus (mult (req_minus x target) h) (mult h (req_minus x target)))
                       (plus (mult (req_minus x target) h) (mult (req_minus x target) h))
                       (mult (plus (req_minus x target) (req_minus x target)) h)
                       (req_plus_compat (mult (req_minus x target) h)
                                        (mult (req_minus x target) h)
                                        (mult h (req_minus x target))
                                        (mult (req_minus x target) h)
                                        (req_refl (mult (req_minus x target) h))
                                        (mult_comm h (req_minus x target)))
                       (req_sym (mult (plus (req_minus x target) (req_minus x target)) h)
                                (plus (mult (req_minus x target) h) (mult (req_minus x target) h))
                                (req_mult_plus_distr_r (req_minus x target) (req_minus x target) h))).
    - exact (req_mult_compat (plus (req_minus x target) (req_minus x target))
                             (mult (plus one one) (req_minus x target)) h h
                             (req_sym (mult (plus one one) (req_minus x target))
                                      (plus (req_minus x target) (req_minus x target))
                                      (req_two_mult (req_minus x target)))
                             (req_refl h)).
  }

  assert (HR : req (plus (plus (mult (req_minus x target) (req_minus x target))
                              (mult (req_minus x target) h))
                         (plus (mult h (req_minus x target)) (mult h h)))
                   (plus (plus (mult (req_minus x target) (req_minus x target))
                               (mult (mult (plus one one) (req_minus x target)) h))
                         (mult h h))).
{ exact (req_trans (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_sym (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (req_trans (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h)) (req_refl (mult (req_minus x target) (req_minus x target))) (plus_assoc (mult (req_minus x target) h) (mult h (req_minus x target)) (mult h h))) (req_trans (plus (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult h h)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h)) (req_refl (mult (req_minus x target) (req_minus x target))) (req_plus_compat (plus (mult (req_minus x target) h) (mult h (req_minus x target))) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h) Hpair (req_refl (mult h h)))) (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h))))). }
  apply (req_trans (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                              (plus (mult (req_minus x target) (req_minus x target))
                                    (mult (mult (plus one one) (req_minus x target)) h)))
                   (req_minus (plus (plus (mult (req_minus x target) (req_minus x target))
                                          (mult (req_minus x target) h))
                                    (plus (mult h (req_minus x target)) (mult h h)))
                              (plus (mult (req_minus x target) (req_minus x target))
                                    (mult (mult (plus one one) (req_minus x target)) h)))
                   (mult h h)).
  - exact (req_rdf_minus_compat_l (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (req_trans (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (mult (plus (req_minus x target) h) (plus (req_minus x target) h)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (req_mult_compat (req_minus (plus x h) target) (plus (req_minus x target) h) (req_minus (plus x h) target) (plus (req_minus x target) h) Hv Hv) (req_trans (mult (plus (req_minus x target) h) (plus (req_minus x target) h)) (plus (mult (req_minus x target) (plus (req_minus x target) h)) (mult h (plus (req_minus x target) h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (req_mult_plus_distr_r (req_minus x target) h (plus (req_minus x target) h)) (req_plus_compat (mult (req_minus x target) (plus (req_minus x target) h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (mult h (plus (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h)) (req_trans (mult (req_minus x target) (plus (req_minus x target) h)) (mult (plus (req_minus x target) h) (req_minus x target)) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (req_mult_comm_rewrite (req_minus x target) (plus (req_minus x target) h)) (req_trans (mult (plus (req_minus x target) h) (req_minus x target)) (plus (mult (req_minus x target) (req_minus x target)) (mult h (req_minus x target))) (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (req_mult_plus_distr_r (req_minus x target) h (req_minus x target)) (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (mult h (req_minus x target)) (mult (req_minus x target) h) (req_mult_comm_rewrite (req_minus x target) (req_minus x target)) (req_mult_comm_rewrite h (req_minus x target))))) (req_trans (mult h (plus (req_minus x target) h)) (mult (plus (req_minus x target) h) h) (plus (mult h (req_minus x target)) (mult h h)) (req_mult_comm_rewrite h (plus (req_minus x target) h)) (req_trans (mult (plus (req_minus x target) h) h) (plus (mult (req_minus x target) h) (mult h h)) (plus (mult h (req_minus x target)) (mult h h)) (req_mult_plus_distr_r (req_minus x target) h h) (req_plus_compat (mult (req_minus x target) h) (mult h (req_minus x target)) (mult h h) (mult h h) (req_mult_comm_rewrite (req_minus x target) h) (req_mult_comm_rewrite h h)))))))).
  - exact (req_trans (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (mult h h) (req_sym (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_minus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (req_rdf_minus_compat_l (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (req_sym (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) h)) (plus (mult h (req_minus x target)) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) HR))) (req_minus_plus_cancel_r (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h))).
Qed.

(* ---- 件 9：cross_entropy_softmax_diff L26015 -> req_cross_entropy_softmax_diff *)
(*   （log_inv_exp_neg_slot 槽使用；误差经折叠为恒等映射后归零——Id Hfold 同构）  *)

Theorem req_cross_entropy_softmax_diff :
  reqRDF (fun logit => log_inv (exp_neg logit) (exp_neg_pos logit)).
Proof.
  exists (fun _ => one).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Hz1 : req (mult one h) h).
    { exact (req_trans (mult one h) (mult h one) h (mult_comm one h) (mult_one h)). }
    assert (Herr : req (req_minus (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                  (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h)))
                       zero).
    { apply (req_minus_self_zero (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                 (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h))).
      apply (req_trans (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                       (plus x h)
                       (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h))).
      - exact (log_inv_exp_neg_slot (plus x h)).
      - exact (req_plus_compat x (log_inv (exp_neg x) (exp_neg_pos x)) h (mult one h)
                               (req_sym (log_inv (exp_neg x) (exp_neg_pos x)) x
                                        (log_inv_exp_neg_slot x))
                               (req_sym (mult one h) h Hz1)). }
    exact (req_rdf_abs_zero_le abs_nonneg_plain (req_minus (log_inv (exp_neg (plus x h)) (exp_neg_pos (plus x h)))
                                          (plus (log_inv (exp_neg x) (exp_neg_pos x)) (mult one h)))
                               eps h Heps Herr).
Qed.

(* ---- 件 10：mse_diff L26174 -> req_mse_diff -------------------------------- *)
(*   （辅件 req_rdf_square_diff_expand 已承载；delta = min one eps，             *)
(*    min_le_*_plain 双槽使用；|h^2| = |h|^2 <= eps|h| 经 le_mult_compat_weak）  *)

Theorem req_mse_diff : forall target : R,
  reqRDF (fun pred => mult (req_minus pred target) (req_minus pred target)).
Proof.
  intro target.
  exists (fun pred => mult (plus one one) (req_minus pred target)).
  intros x eps Heps.
  exists (min one eps).
  split.
  - exact (min_pos one eps one_pos Heps).
  - intros h Hh.
    assert (Hexp : req (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                  (plus (mult (req_minus x target) (req_minus x target))
                                        (mult (mult (plus one one) (req_minus x target)) h)))
                       (mult h h))
      by exact (req_rdf_square_diff_expand x target h).
    apply (le_trans (abs (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                    (plus (mult (req_minus x target) (req_minus x target))
                                          (mult (mult (plus one one) (req_minus x target)) h))))
                    (mult (abs h) (abs h))
                    (mult eps (abs h))).
    + apply (le_id_l (abs (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                     (plus (mult (req_minus x target) (req_minus x target))
                                           (mult (mult (plus one one) (req_minus x target)) h))))
                     (abs (mult h h))
                     (mult (abs h) (abs h))).
      * exact (req_abs_compat (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
                                         (plus (mult (req_minus x target) (req_minus x target))
                                               (mult (mult (plus one one) (req_minus x target)) h)))
                              (mult h h) Hexp).
      * exact (req_rdf_abs_mult_le h h).
    + apply (le_mult_compat_weak (abs h) eps (abs h)).
      * exact (abs_nonneg_plain h).
      * exact (lt_le_iff (abs h) eps
                   (inl (lt_le_trans (abs h) (min one eps) eps Hh (min_le_r_plain one eps)))).
Qed.

(* ---- 增量件（增量清单动作 4 唯一实建件）：differentiable_affine L25493       *)
(*   -> req_rdf_affine。f(x)=a·x+b，df=a，误差恒为零——req_mult_plus_distr_r      *)
(*   换形（右分配经 mult_comm 三跳换左侧）+ plus 重组三步 + req_minus_self_zero   *)
(*   完成；预算走 req_rdf_abs_zero_le abs_nonneg_plain 统一零误差道（同 req_rdf_const 形）。       *)

Theorem req_rdf_affine : forall a b : R, reqRDF (fun x => plus (mult a x) b).
Proof.
  intros a b.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    apply (req_rdf_abs_zero_le abs_nonneg_plain
             (req_minus (plus (mult a (plus x h)) b)
                        (plus (plus (mult a x) b) (mult a h))) eps h Heps).
    apply (req_minus_self_zero (plus (mult a (plus x h)) b)
                               (plus (plus (mult a x) b) (mult a h))).
    apply (req_trans (plus (mult a (plus x h)) b)
                     (plus (plus (mult a x) (mult a h)) b)
                     (plus (plus (mult a x) b) (mult a h))).
    + exact (req_plus_compat (mult a (plus x h))
                             (plus (mult a x) (mult a h))
                             b b
                             (req_trans (mult a (plus x h))
                                        (plus (mult x a) (mult h a))
                                        (plus (mult a x) (mult a h))
                                        (req_trans (mult a (plus x h))
                                                   (mult (plus x h) a)
                                                   (plus (mult x a) (mult h a))
                                                   (mult_comm a (plus x h))
                                                   (req_mult_plus_distr_r x h a))
                                        (req_plus_compat (mult x a) (mult a x)
                                                         (mult h a) (mult a h)
                                                         (mult_comm x a)
                                                         (mult_comm h a)))
                             (req_refl b)).
    + exact (req_trans (plus (plus (mult a x) (mult a h)) b)
                       (plus (mult a x) (plus (mult a h) b))
                       (plus (plus (mult a x) b) (mult a h))
                       (req_sym (plus (mult a x) (plus (mult a h) b))
                                (plus (plus (mult a x) (mult a h)) b)
                                (plus_assoc (mult a x) (mult a h) b))
                       (req_trans (plus (mult a x) (plus (mult a h) b))
                                  (plus (mult a x) (plus b (mult a h)))
                                  (plus (plus (mult a x) b) (mult a h))
                                  (req_plus_compat (mult a x) (mult a x)
                                                   (plus (mult a h) b)
                                                   (plus b (mult a h))
                                                   (req_refl (mult a x))
                                                   (plus_comm (mult a h) b))
                                  (plus_assoc (mult a x) b (mult a h)))).
Qed.

(* ---- 件 11：entropy_differentiable L26368 -> req_entropy_differentiable ----- *)
(*   （域前提位：rdf_log_diff 槽 = "正总值可微函数的 log 链闭合"——Id             *)
(*    log_differentiable 全称槽的 req 域化同位；Omega_B_wd 诚实位 = req compose  *)
(*    的函数兼容位——Id funext 免费而 req 接口无，诚实登记表登记）                  *)

Section ReqEntropyDiff.

(* R/RIS/RNN/RDP 由外层 ReqRDFScalar 节继承（嵌套节零重复声明） *)

Variable Omega_A : R -> R.
Variable Omega_B : R -> R.
Variable dOmega_A : reqRDF Omega_A.
Variable dOmega_B : reqRDF Omega_B.
Variable Omega_A_pos : forall E_A : R, lt zero (Omega_A E_A).
Variable Omega_B_pos : forall E_B : R, lt zero (Omega_B E_B).
Variable Omega_B_wd : forall u v : R, req u v -> req (Omega_B u) (Omega_B v).
Variable E_total : R.
Variable k_B : R.

Definition req_rdf_E_B_ent (E_A : R) : R := req_minus E_total E_A.
Definition req_rdf_Omega_total_ent (E_A : R) : R := mult (Omega_A E_A) (Omega_B (req_rdf_E_B_ent E_A)).
Definition Omega_total_pos_ent (E_A : R) : lt zero (req_rdf_Omega_total_ent E_A).
Proof.
  exact (mult_positive (Omega_A E_A) (Omega_B (req_rdf_E_B_ent E_A))
                       (Omega_A_pos E_A) (Omega_B_pos (req_rdf_E_B_ent E_A))).
Defined.
Definition req_rdf_entropy_ent (E_A : R) : R :=
  mult k_B (log (req_rdf_Omega_total_ent E_A) (Omega_total_pos_ent E_A)).

Variable rdf_log_diff : forall (g : R -> R) (Hg : forall y : R, lt zero (g y)),
  reqRDF (fun z => log (g z) (Hg z)).

Theorem req_entropy_differentiable : reqRDF req_rdf_entropy_ent.
Proof.
  assert (HEB_d : reqRDF req_rdf_E_B_ent).
  { exact (req_rdf_minus (fun _ => E_total) (fun x => x)
             (req_rdf_const E_total) req_rdf_id). }
  assert (HcompB : reqRDF (fun E_A => Omega_B (req_rdf_E_B_ent E_A))).
  { exact (req_rdf_compose Omega_B req_rdf_E_B_ent dOmega_B HEB_d Omega_B_wd). }
  assert (HOmega_d : reqRDF req_rdf_Omega_total_ent).
  { exact (req_rdf_mult Omega_A (fun E_A => Omega_B (req_rdf_E_B_ent E_A)) dOmega_A HcompB). }
  assert (Hlog_d : reqRDF (fun z => log (req_rdf_Omega_total_ent z) (Omega_total_pos_ent z))).
  { exact (rdf_log_diff req_rdf_Omega_total_ent Omega_total_pos_ent). }
  exact (req_rdf_mult (fun _ => k_B)
                      (fun z => log (req_rdf_Omega_total_ent z) (Omega_total_pos_ent z))
                      (req_rdf_const k_B) Hlog_d).
Qed.

End ReqEntropyDiff.

(* ===================================================================== *)
(* Part 3：MV 桥（桥C2-MV/MVVec）——reqStateSpace/reqHilbertSpace/             *)
(*   reqStateSpaceExtended 定义级转写 + reqRDFMV/reqRDFMVVec 记录桥。          *)
(*   诚实差异登记表（MV 区追加，接续头注登记表）：                                 *)
(*   5. 律字段分层修正（登记表 2 的类型级落实）：R 值律（metric_sym/sminus、        *)
(*      inner_sym/splus_l/smult_l、snorm_smult/triangle、proj_orthogonal）req 形； *)
(*      载体律（splus/smult 簇、metric_zero/clim_unique/inner_definite 结论位）    *)
(*      Id 形——载体 req 形需载体集oid字段而 16 件使用面实证全在 R 值层（逐件       *)
(*      核读），零使用即零假设，诚实从简。req 形更弱，使用安全方向。              *)
(*   6. rdf_inner_zero 槽（⟨szero,h⟩ ≡ zero）：req 接口零 id_cong——szero 入     *)
(*      inner 实参位换形无运输机（既有同族限制），T2① 假设位接续；Id 侧      *)
(*      inner_szero_l 为可证定理，其 req 对位件接口级不可复刻，登记显式假设。      *)
(* ===================================================================== *)

Record reqStateSpace := {
  rs_carrier : Set;
  rs_zero : rs_carrier;
  rs_plus : rs_carrier -> rs_carrier -> rs_carrier;
  rs_mult : R -> rs_carrier -> rs_carrier;
  rs_opp : rs_carrier -> rs_carrier;
  rs_plus_assoc : forall a b c : rs_carrier,
    Id (rs_plus a (rs_plus b c)) (rs_plus (rs_plus a b) c);
  rs_plus_comm : forall a b : rs_carrier, Id (rs_plus a b) (rs_plus b a);
  rs_plus_zero : forall a : rs_carrier, Id (rs_plus a rs_zero) a;
  rs_plus_opp : forall a : rs_carrier, Id (rs_plus a (rs_opp a)) rs_zero;
  rs_mult_one : forall a : rs_carrier, Id (rs_mult one a) a;
  rs_mult_assoc : forall (a b : R) (x : rs_carrier),
    Id (rs_mult a (rs_mult b x)) (rs_mult (mult a b) x);
  rs_mult_distrib_r : forall (a : R) (x y : rs_carrier),
    Id (rs_mult a (rs_plus x y)) (rs_plus (rs_mult a x) (rs_mult a y));
  rs_mult_distrib_l : forall (a b : R) (x : rs_carrier),
    Id (rs_mult (plus a b) x) (rs_plus (rs_mult a x) (rs_mult b x));
  rs_metric : rs_carrier -> rs_carrier -> R;
  rs_metric_sym : forall a b : rs_carrier, req (rs_metric a b) (rs_metric b a);
  rs_metric_pos : forall a b : rs_carrier, le zero (rs_metric a b);
  rs_metric_zero : forall a b : rs_carrier,
    req (rs_metric a b) zero -> Id a b;
  rs_metric_triangle : forall a b c : rs_carrier,
    le (rs_metric a c) (plus (rs_metric a b) (rs_metric b c));
  rs_clim : (nat -> rs_carrier) -> rs_carrier -> Set;
  rs_clim_unique : forall (u : nat -> rs_carrier) (l1 l2 : rs_carrier),
    rs_clim u l1 -> rs_clim u l2 -> Id l1 l2;
  rs_cauchy_complete : forall (u : nat -> rs_carrier),
    (forall eps : R, lt zero eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n -> lt (rs_metric (u m) (u n)) eps)) ->
    sigT (fun l : rs_carrier => rs_clim u l)
}.

Record reqHilbertSpace
                       (SS : reqStateSpace) := {
  rh_inner : rs_carrier SS -> rs_carrier SS -> R;
  rh_inner_sym : forall x y : rs_carrier SS, req (rh_inner x y) (rh_inner y x);
  rh_inner_pos : forall x : rs_carrier SS, le zero (rh_inner x x);
  rh_inner_definite : forall x : rs_carrier SS,
    Id (rh_inner x x) zero -> Id x (rs_zero SS);
  rh_inner_splus_l : forall x y z : rs_carrier SS,
    req (rh_inner (rs_plus SS x y) z) (plus (rh_inner x z) (rh_inner y z));
  rh_inner_smult_l : forall (a : R) (x y : rs_carrier SS),
    req (rh_inner (rs_mult SS a x) y) (mult a (rh_inner x y));
  rh_proj : rs_carrier SS -> rs_carrier SS -> rs_carrier SS;
  rh_proj_linear : forall u v w : rs_carrier SS,
    Id (rh_proj u (rs_plus SS v w))
       (rs_plus SS (rh_proj u v) (rh_proj u w));
  rh_proj_orthogonal : forall u v : rs_carrier SS,
    req (rh_inner (rs_plus SS v (rs_opp SS (rh_proj u v))) u) zero
}.

Definition req_sminus
                       (SS : reqStateSpace)
                       (u v : rs_carrier SS) : rs_carrier SS :=
  rs_plus SS u (rs_opp SS v).

Record reqStateSpaceExtended
                             (SS : reqStateSpace) := {
  re_base :> reqStateSpace;
  re_mult_zero : forall x : rs_carrier SS,
    Id (rs_mult SS zero x) (rs_zero SS);
  re_mult_opp : forall (a : R) (x : rs_carrier SS),
    Id (rs_mult SS (opp a) x) (rs_opp SS (rs_mult SS a x));
  re_snorm : rs_carrier SS -> R;
  re_snorm_pos : forall x : rs_carrier SS, le zero (re_snorm x);
  re_snorm_zero : forall x : rs_carrier SS,
    req (re_snorm x) zero -> Id x (rs_zero SS);
  re_snorm_smult : forall (a : R) (x : rs_carrier SS),
    req (re_snorm (rs_mult SS a x)) (mult (abs a) (re_snorm x));
  re_snorm_triangle : forall x y : rs_carrier SS,
    le (re_snorm (rs_plus SS x y)) (plus (re_snorm x) (re_snorm y));
  re_metric_sminus : forall u v : rs_carrier SS,
    req (rs_metric SS u v) (re_snorm (req_sminus SS u v))
}.

Record reqRDFMV
                (SS : reqStateSpace) (HS : reqHilbertSpace SS)
                (f : rs_carrier SS -> R) : Set := {
  rdfmv : rs_carrier SS -> rs_carrier SS;
  rdfmv_correct : forall (x : rs_carrier SS) (eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : rs_carrier SS,
        lt (rs_metric SS h (rs_zero SS)) delta ->
        le (abs (req_minus (f (rs_plus SS x h))
                           (plus (f x) (rh_inner SS HS (rdfmv x) h))))
           (mult eps (rs_metric SS h (rs_zero SS)))))
}.

Record reqRDFMVVec
                   (SS : reqStateSpace)
                   (f : rs_carrier SS -> rs_carrier SS) : Set := {
  rdfvec : rs_carrier SS -> rs_carrier SS -> rs_carrier SS;
  rdfvec_correct : forall (x : rs_carrier SS) (eps : R), lt zero eps ->
    sigT (fun delta : R => And (lt zero delta)
      (forall h : rs_carrier SS,
        lt (rs_metric SS h (rs_zero SS)) delta ->
        le (rs_metric SS (req_sminus SS (f (rs_plus SS x h)) (f x))
                               (rdfvec x h))
           (mult eps (rs_metric SS h (rs_zero SS)))))
}.

(* ===================================================================== *)
(* Part 4：MV 区使用件（件 12-16；清单 §5 结论逐位落实）                       *)
(* ===================================================================== *)

Section ReqRDFMV.

(* R/RIS/RNN/RDP 由外层 Section ReqRDFScalar 继承，此处不重复声明。 *)
Context (SS : reqStateSpace).
Context (HSE : reqStateSpaceExtended SS).
Context (HS : reqHilbertSpace SS).

Let Sc : Set := rs_carrier SS.
Let S0 : Sc := rs_zero SS.
Let spl : Sc -> Sc -> Sc := rs_plus SS.
Let mtr : Sc -> Sc -> R := rs_metric SS.
Let inn : Sc -> Sc -> R := rh_inner SS HS.

(* 辅件（清单 (b|桥) 显式假设接续）：inner_splus_r L26722 req 对位——字段直推       *)
Lemma req_inner_splus_r : forall x y z : Sc,
  req (inn x (spl y z)) (plus (inn x y) (inn x z)).
Proof.
  intros x y z.
  apply (req_trans (inn x (spl y z)) (inn (spl y z) x) (plus (inn x y) (inn x z))).
  - exact (rh_inner_sym SS HS x (spl y z)).
  - apply (req_trans (inn (spl y z) x) (plus (inn y x) (inn z x))
                     (plus (inn x y) (inn x z))).
    + exact (rh_inner_splus_l SS HS y z x).
    + exact (req_plus_compat (inn y x) (inn x y) (inn z x) (inn x z)
                             (rh_inner_sym SS HS y x)
                             (rh_inner_sym SS HS z x)).
Qed.

(* ---- 件 12：differentiable_mv_const L26786 -> req_rdf_mv_const ------------- *)
(*   （rdf_inner_zero 槽使用；登记表 6） --------------------------------------- *)

Variable rdf_inner_zero : forall h : Sc, req (inn S0 h) zero.

Theorem req_rdf_mv_const : forall c : R, reqRDFMV SS HS (fun _ => c).
Proof.
  intro c.
  exists (fun _ => S0).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus c (plus c (inn S0 h))) zero).
    { apply (req_minus_self_zero c (plus c (inn S0 h))).
      apply (req_trans c (plus c zero) (plus c (inn S0 h))).
      - exact (req_sym (plus c zero) c (plus_zero c)).
      - exact (req_plus_compat c c zero (inn S0 h) (req_refl c)
                 (req_sym (inn S0 h) zero (rdf_inner_zero h))). }
    assert (Hzm : le zero (mult eps (mtr h S0))).
    { apply (le_id_l zero (mult zero (mtr h S0)) (mult eps (mtr h S0))).
      - exact (req_sym (mult zero (mtr h S0)) zero
                 (req_trans (mult zero (mtr h S0)) (mult (mtr h S0) zero) zero
                            (mult_comm zero (mtr h S0)) (mult_zero (mtr h S0)))).
      - exact (le_mult_compat_weak zero eps (mtr h S0)
                   (rs_metric_pos SS h S0)
                   (lt_le_iff zero eps (inl Heps))). }
    exact (le_trans (abs (req_minus c (plus c (inn S0 h)))) (abs zero)
                    (mult eps (mtr h S0))
                    (le_id_l (abs (req_minus c (plus c (inn S0 h)))) (abs zero)
                             (abs zero)
                             (req_abs_compat (req_minus c (plus c (inn S0 h)))
                                             zero Herr)
                             (le_refl (abs zero)))
                    (le_id_l (abs zero) zero (mult eps (mtr h S0)) abs_zero Hzm)).
Qed.

(* ---- 件 13：differentiable_mv_linear L26837 -> req_rdf_mv_linear ----------- *)
(*   （注意力 logits 可微：attention_score(s) = ⟨s,key⟩，df = key；             *)
(*    req_inner_splus_r 辅件使用） ------------------------------------------- *)

Theorem req_rdf_mv_linear : forall a : Sc, reqRDFMV SS HS (fun x => inn a x).
Proof.
  intro a.
  exists (fun _ => a).
  intros x eps Heps.
  exists one.
  split.
  - exact one_pos.
  - intros h Hh.
    assert (Herr : req (req_minus (inn a (spl x h)) (plus (inn a x) (inn a h))) zero).
    { apply (req_minus_self_zero (inn a (spl x h)) (plus (inn a x) (inn a h))).
      exact (req_inner_splus_r a x h). }
    assert (Hzm : le zero (mult eps (mtr h S0))).
    { apply (le_id_l zero (mult zero (mtr h S0)) (mult eps (mtr h S0))).
      - exact (req_sym (mult zero (mtr h S0)) zero
                 (req_trans (mult zero (mtr h S0)) (mult (mtr h S0) zero) zero
                            (mult_comm zero (mtr h S0)) (mult_zero (mtr h S0)))).
      - exact (le_mult_compat_weak zero eps (mtr h S0)
                   (rs_metric_pos SS h S0)
                   (lt_le_iff zero eps (inl Heps))). }
    exact (le_trans (abs (req_minus (inn a (spl x h)) (plus (inn a x) (inn a h))))
                    (abs zero) (mult eps (mtr h S0))
                    (le_id_l (abs (req_minus (inn a (spl x h))
                                             (plus (inn a x) (inn a h))))
                             (abs zero) (abs zero)
                             (req_abs_compat (req_minus (inn a (spl x h))
                                                        (plus (inn a x) (inn a h)))
                                             zero Herr)
                             (le_refl (abs zero)))
                    (le_id_l (abs zero) zero (mult eps (mtr h S0)) abs_zero Hzm)).
Qed.

(* ---- 件 14：differentiable_mv_plus L26885 -> req_rdf_mv_plus --------------- *)
(*   （req_inner_splus_r 使用 + req_rdf_plus 同构 eps/2 核算；req 接口 min        *)
(*    plain-le 双槽（ReqDiffPlain）对应副本 Id min_le_l/min_le_r；误差分解三跳：       *)
(*    inner 线性换形 -> plus 换中 -> req_minus_plus_distr 拆两支） -------------- *)

Theorem req_rdf_mv_plus : forall f g : Sc -> R,
  reqRDFMV SS HS f -> reqRDFMV SS HS g ->
  reqRDFMV SS HS (fun x => plus (f x) (g x)).
Proof.
  intros f g Hf Hg.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => spl (df x) (dg x)).
  intros x eps Heps.
  destruct (Hdf x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dfd [Hd1 Hd2]].
  destruct (Hdg x (mult (inv_pos (plus one one) req_two_pos) eps)
              (req_rdf_half_pos eps Heps)) as [dgd [Hg1 Hg2]].
  exists (min dfd dgd).
  split.
  - exact (min_pos dfd dgd Hd1 Hg1).
  - intros h Hh.
    assert (Hh1 : lt (mtr h S0) dfd).
    { exact (lt_le_trans (mtr h S0) (min dfd dgd) dfd Hh
                         (min_le_l_plain dfd dgd)). }
    assert (Hh2 : lt (mtr h S0) dgd).
    { exact (lt_le_trans (mtr h S0) (min dfd dgd) dgd Hh
                         (min_le_r_plain dfd dgd)). }
    apply (le_id_l (abs (req_minus (plus (f (spl x h)) (g (spl x h)))
                                   (plus (plus (f x) (g x))
                                         (inn (spl (df x) (dg x)) h))))
                   (abs (plus (req_minus (f (spl x h))
                                          (plus (f x) (inn (df x) h)))
                              (req_minus (g (spl x h))
                                         (plus (g x) (inn (dg x) h)))))
                   (mult eps (mtr h S0))).
    + exact (req_abs_compat
               (req_minus (plus (f (spl x h)) (g (spl x h)))
                          (plus (plus (f x) (g x))
                                (inn (spl (df x) (dg x)) h)))
               (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                     (req_minus (g (spl x h)) (plus (g x) (inn (dg x) h))))
               (req_trans
                  (req_minus (plus (f (spl x h)) (g (spl x h)))
                             (plus (plus (f x) (g x))
                                   (inn (spl (df x) (dg x)) h)))
                  (req_minus (plus (f (spl x h)) (g (spl x h)))
                             (plus (plus (f x) (inn (df x) h))
                                   (plus (g x) (inn (dg x) h))))
                  (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                        (req_minus (g (spl x h))
                                   (plus (g x) (inn (dg x) h))))
                  (req_rdf_minus_compat_r (plus (f (spl x h)) (g (spl x h)))
                     (plus (plus (f x) (g x)) (inn (spl (df x) (dg x)) h))
                     (plus (plus (f x) (inn (df x) h))
                           (plus (g x) (inn (dg x) h)))
                     (req_trans (plus (plus (f x) (g x))
                                      (inn (spl (df x) (dg x)) h))
                                (plus (plus (f x) (g x))
                                      (plus (inn (df x) h) (inn (dg x) h)))
                                (plus (plus (f x) (inn (df x) h))
                                      (plus (g x) (inn (dg x) h)))
                                (req_plus_compat (plus (f x) (g x))
                                                 (plus (f x) (g x))
                                                 (inn (spl (df x) (dg x)) h)
                                                 (plus (inn (df x) h)
                                                       (inn (dg x) h))
                                                 (req_refl (plus (f x) (g x)))
                                                 (rh_inner_splus_l SS HS
                                                                   (df x) (dg x)
                                                                   h))
                                (req_plus_swap_mid (f x) (g x)
                                                   (inn (df x) h)
                                                   (inn (dg x) h))))
                  (req_minus_plus_distr (f (spl x h)) (g (spl x h))
                                        (plus (f x) (inn (df x) h))
                                        (plus (g x) (inn (dg x) h))))).
    + apply (le_trans _
               (plus (abs (req_minus (f (spl x h))
                                     (plus (f x) (inn (df x) h))))
                     (abs (req_minus (g (spl x h))
                                     (plus (g x) (inn (dg x) h)))))).
      * exact (req_rdf_abs_triangle
                 (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                 (req_minus (g (spl x h)) (plus (g x) (inn (dg x) h)))).
      * apply (le_trans _
                 (plus (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                             (mtr h S0))
                       (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                             (mtr h S0)))).
        -- exact (le_plus_compat
                   (abs (req_minus (f (spl x h))
                                   (plus (f x) (inn (df x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (mtr h S0))
                   (abs (req_minus (g (spl x h))
                                   (plus (g x) (inn (dg x) h))))
                   (mult (mult (inv_pos (plus one one) req_two_pos) eps)
                         (mtr h S0))
                   (Hd2 h Hh1) (Hg2 h Hh2)).
        -- exact (req_rdf_half_pair_le eps (mtr h S0)).
Qed.

(* ---- 件 15 辅件甲（R 层纯代数）：Id minus_minus_distr req 对位 -------------- *)

Lemma req_rdf_minus_minus_distr : forall A B C : R,
  req (req_minus (req_minus A B) C) (req_minus A (plus B C)).
Proof.
  intros A B C. unfold req_minus.
  exact (req_trans (plus (plus A (opp B)) (opp C))
                   (plus A (plus (opp B) (opp C)))
                   (plus A (opp (plus B C)))
                   (req_sym (plus A (plus (opp B) (opp C)))
                            (plus (plus A (opp B)) (opp C))
                            (plus_assoc A (opp B) (opp C)))
                   (req_plus_compat A A (plus (opp B) (opp C)) (opp (plus B C))
                      (req_refl A)
                      (req_sym (opp (plus B C)) (plus (opp B) (opp C))
                               (req_opp_plus B C)))).
Qed.

(* ---- 件 15/16 辅件乙（R 层纯代数）：通用误差分解 --------------------------- *)
(*   Id mv_vec_diff_decomp L27450 req 对位：A−(B+X) ≡ (A−(B+Y)) + (Y−X)。       *)
(*   零假设位（req_minus 展开后纯 plus/opp/req_opp_plus 链）。 ------------------ *)

Lemma req_rdf_mv_vec_decomp : forall A B X Y : R,
  req (req_minus A (plus B X)) (plus (req_minus A (plus B Y)) (req_minus Y X)).
Proof.
  intros A B X Y. unfold req_minus.
  assert (Hcancel : req (plus (opp (plus B Y)) Y) (opp B)).
  { exact (req_trans (plus (opp (plus B Y)) Y)
                     (plus (plus (opp B) (opp Y)) Y) (opp B)
                     (req_plus_compat (opp (plus B Y)) (plus (opp B) (opp Y))
                                      Y Y (req_opp_plus B Y) (req_refl Y))
                     (req_trans (plus (plus (opp B) (opp Y)) Y)
                                (plus (opp B) (plus (opp Y) Y)) (opp B)
                                (req_sym (plus (opp B) (plus (opp Y) Y))
                                         (plus (plus (opp B) (opp Y)) Y)
                                         (plus_assoc (opp B) (opp Y) Y))
                                (req_trans (plus (opp B) (plus (opp Y) Y))
                                           (plus (opp B) zero) (opp B)
                                           (req_plus_compat (opp B) (opp B)
                                              (plus (opp Y) Y) zero
                                              (req_refl (opp B))
                                              (req_plus_opp_l Y))
                                           (req_plus_zero_r (opp B))))). }
  assert (Hre : req (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                    (plus A (opp (plus B X)))).
  { apply (req_trans (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                     (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                     (plus A (opp (plus B X)))).
    - exact (req_trans (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                       (plus A (plus (opp (plus B Y)) (plus Y (opp X))))
                       (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                       (req_sym (plus A (plus (opp (plus B Y)) (plus Y (opp X))))
                                (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                                (plus_assoc A (opp (plus B Y)) (plus Y (opp X))))
                       (req_plus_compat A A
                          (plus (opp (plus B Y)) (plus Y (opp X)))
                          (plus (plus (opp (plus B Y)) Y) (opp X))
                          (req_refl A)
                          (plus_assoc (opp (plus B Y)) Y (opp X)))).
    - apply (req_trans (plus A (plus (plus (opp (plus B Y)) Y) (opp X)))
                       (plus A (plus (opp B) (opp X)))
                       (plus A (opp (plus B X)))).
      + exact (req_plus_compat A A (plus (plus (opp (plus B Y)) Y) (opp X))
                                 (plus (opp B) (opp X)) (req_refl A)
                                 (req_plus_compat (plus (opp (plus B Y)) Y) (opp B)
                                    (opp X) (opp X) Hcancel (req_refl (opp X)))).
      + exact (req_plus_compat A A (plus (opp B) (opp X)) (opp (plus B X))
                                 (req_refl A)
                                 (req_sym (opp (plus B X)) (plus (opp B) (opp X))
                                          (req_opp_plus B X))). }
  exact (req_sym (plus (plus A (opp (plus B Y))) (plus Y (opp X)))
                 (plus A (opp (plus B X))) Hre).
Qed.

(* ---- 件 15 辅件丙：乘积形误差分解（Id mv_compose_diff_decomp L26739 对位）--- *)

Lemma req_rdf_mv_compose_decomp : forall A B C U W : R,
  req (req_minus A (plus B (mult C W)))
      (plus (req_minus A (plus B (mult C U))) (mult C (req_minus U W))).
Proof.
  intros A B C U W.
  apply (req_trans (req_minus A (plus B (mult C W)))
                   (plus (req_minus A (plus B (mult C U)))
                         (req_minus (mult C U) (mult C W)))
                   (plus (req_minus A (plus B (mult C U)))
                         (mult C (req_minus U W)))).
  - exact (req_rdf_mv_vec_decomp A B (mult C W) (mult C U)).
  - exact (req_plus_compat (req_minus A (plus B (mult C U)))
                           (req_minus A (plus B (mult C U)))
                           (req_minus (mult C U) (mult C W))
                           (mult C (req_minus U W))
                           (req_refl (req_minus A (plus B (mult C U))))
                           (req_sym (mult C (req_minus U W))
                                    (req_minus (mult C U) (mult C W))
                                    (req_mult_minus_distr_l C U W))).
Qed.

(* ---- 内积 Lipschitz 槽（T2① 假设位；Id inner_lipschitz L26779 sigT 同构）--- *)

Variable req_inner_lipschitz : forall a : Sc,
  sigT (fun N : R => And (le zero N) (forall h : Sc,
    le (abs (inn a h)) (mult N (mtr h S0)))).

(* ---- 件 15：differentiable_mv_compose L26959 -> req_rdf_mv_compose ---------- *)
(*   （req_inner_lipschitz 槽使用；外层 g 函数兼容前提位沿件 8 req_rdf_compose    *)
(*    先例；预算 eps4=eps/4：T1 ≤ eps_g·|Dg| ≤ eps4·s（req_rdf_inv_scale_le）；   *)
(*    T2 ≤ |dg(f x)|·eps_f·s ≤ eps4·s（inv_pos_correct 核算）；                   *)
(*    完成 req_rdf_quarter_pair_le_final） ------------------------------------ *)

Theorem req_rdf_mv_compose : forall (f : Sc -> R) (g : R -> R),
  reqRDFMV SS HS f -> reqRDF g ->
  (forall u v : R, req u v -> req (g u) (g v)) ->
  reqRDFMV SS HS (fun x => g (f x)).
Proof.
  intros f g Hf Hg Hgwd.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => rs_mult SS (dg (f x)) (df x)).
  intros x eps Heps.
  destruct (req_inner_lipschitz (df x)) as [N [HN0 HN2]].
  pose (eps4 := mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive.
    - apply inv_pos_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps]. }
  pose (L := plus N one).
  assert (HL : lt zero L) by (unfold L; exact (req_plus_le_lt_pos N one HN0 one_pos)).
  pose (M := plus (abs (dg (f x))) one).
  assert (HM : lt zero M) by (unfold M; exact (req_rdf_abs_plus_one_pos abs_nonneg_plain (dg (f x)))).
  pose (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f).
  { unfold eps_f. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  pose (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g).
  { unfold eps_g. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  destruct (Hdf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hdg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    exact (min_pos dfd (min one (mult (inv_pos L HL) dgd)) Hdf1
             (min_pos one (mult (inv_pos L HL) dgd) one_pos Hltm)).
  - intros h Hh.
    pose (s := mtr h S0).
    pose (Dg := req_minus (f (spl x h)) (f x)).
    assert (Hh_dfd : lt s dfd).
    { exact (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd))) dfd Hh
             (min_le_l_plain dfd (min one (mult (inv_pos L HL) dgd)))). }
    assert (Hh_one : lt s one).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd)) one
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_l_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hh_dgds : lt s (mult (inv_pos L HL) dgd)).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd))
                         (mult (inv_pos L HL) dgd)
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_r_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hef : le eps_f one).
    { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
    assert (Hspos : le zero s) by exact (rs_metric_pos SS h S0).
    (* (a) |Dg| ≤ L·s：split + 三角 + eps_f/N 两支 + 系数 (eps_f+N) ≤ L *)
    assert (HDg : le (abs Dg) (mult L s)).
    { apply (le_id_l (abs Dg)
               (abs (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                          (inn (df x) h)))
               (mult L s)
               (req_abs_compat Dg
                  (plus (req_minus (f (spl x h)) (plus (f x) (inn (df x) h)))
                        (inn (df x) h))
                  (req_minus_split (f (spl x h)) (f x) (inn (df x) h)))).
      apply (le_trans (abs (plus (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h)))
                                 (inn (df x) h)))
                      (plus (abs (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h))))
                            (abs (inn (df x) h)))
                      (mult L s)).
      - exact (req_rdf_abs_triangle (req_minus (f (spl x h))
                                               (plus (f x) (inn (df x) h)))
                                    (inn (df x) h)).
      - apply (le_trans (plus (abs (req_minus (f (spl x h))
                                              (plus (f x) (inn (df x) h))))
                              (abs (inn (df x) h)))
                        (plus (mult eps_f s) (mult N s)) (mult L s)).
        + exact (le_plus_compat (abs (req_minus (f (spl x h))
                                                (plus (f x) (inn (df x) h))))
                                (mult eps_f s)
                                (abs (inn (df x) h)) (mult N s)
                                (Hdf2 h Hh_dfd) (HN2 h)).
        + apply (le_trans (plus (mult eps_f s) (mult N s))
                          (mult (plus eps_f N) s) (mult L s)).
          * exact (le_id_l (plus (mult eps_f s) (mult N s))
                           (mult (plus eps_f N) s) (mult (plus eps_f N) s)
                           (req_sym (mult (plus eps_f N) s)
                                    (plus (mult eps_f s) (mult N s))
                                    (req_mult_plus_distr_r eps_f N s))
                           (le_refl (mult (plus eps_f N) s))).
          * exact (le_mult_compat_weak (plus eps_f N) L s Hspos
                       (le_trans (plus eps_f N) (plus one N) L
                                 (le_plus_compat eps_f one N N Hef
                                                 (le_refl N))
                                 (le_id_l (plus one N) L L (plus_comm one N)
                                          (le_refl L)))). }
    (* |Dg| < dgd（L·s < L·(inv L·dgd) ≡ dgd） *)
    assert (HDg_lt : lt (abs Dg) dgd).
    { apply (le_lt_trans (abs Dg) (mult L s) dgd).
      - exact HDg.
      - exact (lt_id_l (mult L s) (mult s L) dgd (mult_comm L s)
                 (lt_id_r (mult s L) (mult (mult (inv_pos L HL) dgd) L) dgd
                    (req_trans (mult (mult (inv_pos L HL) dgd) L)
                               (mult L (mult (inv_pos L HL) dgd)) dgd
                               (mult_comm (mult (inv_pos L HL) dgd) L)
                               (req_rdf_inv_cancel L dgd HL Hdg1))
                    (lt_mult_compat s (mult (inv_pos L HL) dgd) L HL Hh_dgds))). }
    (* T1：外层误差 ≤ eps_g·|Dg| ≤ eps4·s *)
    assert (HT1 : le (abs (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (mult (dg (f x)) Dg))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (g (f (spl x h)))
                                      (plus (g (f x)) (mult (dg (f x)) Dg))))
                      (mult eps_g (abs Dg)) (mult eps4 s)).
      - apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                       (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (abs (req_minus (g (plus (f x) Dg))
                                       (plus (g (f x)) (mult (dg (f x)) Dg))))
                       (mult eps_g (abs Dg))
                       (req_abs_compat
                          (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (mult (dg (f x)) Dg)))
                          (req_minus (g (plus (f x) Dg))
                                     (plus (g (f x)) (mult (dg (f x)) Dg)))
                          (req_rdf_minus_compat_l (g (f (spl x h)))
                             (g (plus (f x) Dg))
                             (plus (g (f x)) (mult (dg (f x)) Dg))
                             (Hgwd (f (spl x h)) (plus (f x) Dg)
                                (req_trans (f (spl x h)) (plus Dg (f x))
                                           (plus (f x) Dg)
                                           (req_rdf_minus_pair (f (spl x h)) (f x))
                                           (plus_comm Dg (f x))))))).
        exact (Hdg2 Dg HDg_lt).
      - apply (le_trans (mult eps_g (abs Dg)) (mult eps_g (mult L s))
                        (mult eps4 s)).
        + exact (req_le_mult_compat_r eps_g (abs Dg) (mult L s)
                     (lt_le_iff zero eps_g (inl Heps_g)) HDg).
        + apply (le_trans (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                          (mult eps4 s)).
          * exact (le_id_l (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                           (mult (mult eps_g L) s) (mult_assoc eps_g L s)
                           (le_refl (mult (mult eps_g L) s))).
          * apply (le_trans (mult (mult eps_g L) s)
                            (mult (mult (mult (inv_pos L HL) eps4) L) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult eps_g L)
                          (mult (mult (inv_pos L HL) eps4) L) s Hspos
                          (le_trans (mult eps_g L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (le_mult_compat_weak eps_g
                                       (mult (inv_pos L HL) eps4) L
                                       (lt_le_iff zero L (inl HL))
                                       (min_le_r_plain one
                                          (mult (inv_pos L HL) eps4)))
                                    (le_refl (mult (mult (inv_pos L HL) eps4) L)))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos L HL) eps4) L)
                          eps4 s Hspos (req_rdf_inv_scale_le L eps4 HL)). }
    (* T2：|dg(f x)|·|Dg−⟨df x,h⟩| ≤ eps4·s *)
    assert (HT2 : le (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                      (mult eps4 s)).
    { apply (le_id_l (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                     (mult (abs (dg (f x)))
                           (abs (req_minus Dg (inn (df x) h))))
                     (mult eps4 s)
                     (abs_mult (dg (f x)) (req_minus Dg (inn (df x) h)))).
      apply (le_trans (mult (abs (dg (f x)))
                            (abs (req_minus Dg (inn (df x) h))))
                      (mult (abs (dg (f x))) (mult eps_f s)) (mult eps4 s)).
      - exact (req_le_mult_compat_r (abs (dg (f x)))
                   (abs (req_minus Dg (inn (df x) h)))
                   (mult eps_f s)
                   (abs_nonneg_plain (dg (f x)))
                   (le_id_l (abs (req_minus Dg (inn (df x) h)))
                            (abs (req_minus (f (spl x h))
                                            (plus (f x) (inn (df x) h))))
                            (mult eps_f s)
                            (req_abs_compat (req_minus Dg (inn (df x) h))
                               (req_minus (f (spl x h))
                                          (plus (f x) (inn (df x) h)))
                               (req_rdf_minus_minus_distr (f (spl x h)) (f x)
                                                          (inn (df x) h)))
                            (Hdf2 h Hh_dfd))).
      - apply (le_trans (mult (abs (dg (f x))) (mult eps_f s))
                        (mult (mult (abs (dg (f x))) eps_f) s) (mult eps4 s)).
        + exact (le_id_l (mult (abs (dg (f x))) (mult eps_f s))
                         (mult (mult (abs (dg (f x))) eps_f) s)
                         (mult (mult (abs (dg (f x))) eps_f) s)
                         (mult_assoc (abs (dg (f x))) eps_f s)
                         (le_refl (mult (mult (abs (dg (f x))) eps_f) s))).
        + apply (le_trans (mult (mult (abs (dg (f x))) eps_f) s)
                          (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                          (mult eps4 s)).
          * exact (le_trans (mult (mult (abs (dg (f x))) eps_f) s)
                            (mult (mult (abs (dg (f x)))
                                        (mult (inv_pos M HM) eps4)) s)
                            (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                            (le_mult_compat_weak (mult (abs (dg (f x))) eps_f)
                               (mult (abs (dg (f x))) (mult (inv_pos M HM) eps4)) s
                               Hspos
                               (req_le_mult_compat_r (abs (dg (f x))) eps_f
                                  (mult (inv_pos M HM) eps4)
                                  (abs_nonneg_plain (dg (f x)))
                                  (min_le_r_plain one
                                     (mult (inv_pos M HM) eps4))))
                            (le_id_l (mult (mult (abs (dg (f x)))
                                                 (mult (inv_pos M HM) eps4)) s)
                                     (mult (mult (mult (inv_pos M HM) eps4)
                                                 (abs (dg (f x)))) s)
                                     (mult (mult (mult (inv_pos M HM) eps4)
                                                 (abs (dg (f x)))) s)
                                     (req_mult_compat
                                        (mult (abs (dg (f x)))
                                              (mult (inv_pos M HM) eps4))
                                        (mult (mult (inv_pos M HM) eps4)
                                              (abs (dg (f x)))) s s
                                        (mult_comm (abs (dg (f x)))
                                                   (mult (inv_pos M HM) eps4))
                                        (req_refl s))
                                     (le_refl (mult (mult (mult (inv_pos M HM) eps4)
                                                        (abs (dg (f x)))) s)))).
          * apply (le_trans (mult (mult (mult (inv_pos M HM) eps4) (abs (dg (f x)))) s)
                            (mult (mult (mult (inv_pos M HM) eps4) M) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos M HM) eps4)
                                                (abs (dg (f x))))
                          (mult (mult (inv_pos M HM) eps4) M) s Hspos
                          (req_le_mult_compat_r (mult (inv_pos M HM) eps4)
                             (abs (dg (f x))) M
                             (le_id_l zero (mult zero eps4)
                                (mult (inv_pos M HM) eps4)
                                (req_sym (mult zero eps4) zero
                                   (req_trans (mult zero eps4) (mult eps4 zero)
                                              zero
                                              (mult_comm zero eps4)
                                              (mult_zero eps4)))
                                (le_mult_compat_weak zero (inv_pos M HM) eps4
                                   (lt_le_iff zero eps4 (inl Heps4))
                                   (lt_le_iff zero (inv_pos M HM)
                                              (inl (inv_pos_pos M HM)))))
                             (req_le_plus_nonneg_r (abs (dg (f x))) one
                                (lt_le_iff zero one (inl one_pos))))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos M HM) eps4) M)
                          eps4 s Hspos (req_rdf_inv_scale_le M eps4 HM)). }
    (* 完成：E ≡ T1 + T2，|T1+T2| ≤ eps4·s + eps4·s ≤ eps·s *)
    apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                   (plus (g (f x))
                                         (inn (rs_mult SS (dg (f x)) (df x))
                                              h))))
                   (abs (plus (req_minus (g (f (spl x h)))
                                          (plus (g (f x)) (mult (dg (f x)) Dg)))
                              (mult (dg (f x)) (req_minus Dg (inn (df x) h)))))
                   (mult eps s)).
    + exact (req_abs_compat
               (req_minus (g (f (spl x h)))
                          (plus (g (f x))
                                (inn (rs_mult SS (dg (f x)) (df x)) h)))
               (plus (req_minus (g (f (spl x h)))
                                (plus (g (f x)) (mult (dg (f x)) Dg)))
                     (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
               (req_trans
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x))
                                   (inn (rs_mult SS (dg (f x)) (df x)) h)))
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x)) (mult (dg (f x)) (inn (df x) h))))
                  (plus (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (mult (dg (f x)) Dg)))
                        (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                  (req_rdf_minus_compat_r (g (f (spl x h)))
                     (plus (g (f x))
                           (inn (rs_mult SS (dg (f x)) (df x)) h))
                     (plus (g (f x)) (mult (dg (f x)) (inn (df x) h)))
                     (req_plus_compat (g (f x)) (g (f x))
                        (inn (rs_mult SS (dg (f x)) (df x)) h)
                        (mult (dg (f x)) (inn (df x) h))
                        (req_refl (g (f x)))
                        (rh_inner_smult_l SS HS (dg (f x)) (df x) h)))
                  (req_rdf_mv_compose_decomp (g (f (spl x h))) (g (f x)) (dg (f x))
                     (req_minus (f (spl x h)) (f x)) (inn (df x) h)))).
    + apply (le_trans (abs (plus (req_minus (g (f (spl x h)))
                                                (plus (g (f x))
                                                      (mult (dg (f x)) Dg)))
                                         (mult (dg (f x))
                                               (req_minus Dg (inn (df x) h)))))
                      (plus (abs (req_minus (g (f (spl x h)))
                                            (plus (g (f x)) (mult (dg (f x)) Dg))))
                            (abs (mult (dg (f x))
                                       (req_minus Dg (inn (df x) h)))))
                      (mult eps s)).
      * exact (req_rdf_abs_triangle (req_minus (g (f (spl x h)))
                                               (plus (g (f x))
                                                     (mult (dg (f x)) Dg)))
                                    (mult (dg (f x))
                                          (req_minus Dg (inn (df x) h)))).
      * apply (le_trans (plus (abs (req_minus (g (f (spl x h)))
                                              (plus (g (f x)) (mult (dg (f x)) Dg))))
                              (abs (mult (dg (f x))
                                         (req_minus Dg (inn (df x) h)))))
                        (plus (mult eps4 s) (mult eps4 s)) (mult eps s)).
        -- exact (le_plus_compat
                    (abs (req_minus (g (f (spl x h)))
                                    (plus (g (f x)) (mult (dg (f x)) Dg))))
                    (mult eps4 s)
                    (abs (mult (dg (f x)) (req_minus Dg (inn (df x) h))))
                    (mult eps4 s) HT1 HT2).
        -- exact (req_rdf_quarter_pair_le_final eps s Heps Hspos).
Qed.

(* ---- 件 16 假设位组（T2① 假设位；Id MultivariableDifferentiable vec 区三 Variable *)
(*   同构 + 场兼容/第二参线性/度量平移三诚实位——载体 Id 无内积运输机，接口级     *)
(*   接续，登记表登记） --------------------------------------------------------- *)

Variable req_mv_adjoint : forall Ld : Sc -> Sc,
  sigT (fun Lad : Sc -> Sc => forall h w : Sc,
    req (inn (Ld h) w) (inn h (Lad w))).

Variable req_op_lipschitz : forall Ld : Sc -> Sc,
  sigT (fun N : R => And (le zero N) (forall h : Sc,
    le (mtr (Ld h) S0) (mult N (mtr h S0)))).

Variable req_sfield_wd : forall (w : Sc -> R) (u v : Sc),
  Id u v -> req (w u) (w v).

Variable req_inner_sminus_r : forall (a u v : Sc),
  req (inn a (req_sminus SS u v)) (req_minus (inn a u) (inn a v)).

Variable req_smetric_sminus_zero : forall u v : Sc,
  req (mtr (req_sminus SS u v) S0) (mtr u v).

(* ---- 件 16：differentiable_mv_vec_compose L27495 -> req_rdf_mv_vec_compose -- *)
(*   （req_mv_adjoint/req_op_lipschitz/req_inner_lipschitz/req_sfield_wd/        *)
(*    req_inner_sminus_r/req_smetric_sminus_zero 六槽使用；伴随拉回梯度；        *)
(*    通用误差分解 req_rdf_mv_vec_decomp 直接匹配；预算同件 15，T1 eps_g·|Dg| 系，     *)
(*    T2 N_a·|⟨a,Dg⟩−⟨a,dfh⟩| 系；完成 quarter_pair_le_final） ------------------ *)

Theorem req_rdf_mv_vec_compose : forall (f : Sc -> Sc) (g : Sc -> R),
  reqRDFMVVec SS f -> reqRDFMV SS HS g ->
  reqRDFMV SS HS (fun x => g (f x)).
Proof.
  intros f g Hf Hg.
  destruct Hf as [df Hdf]. destruct Hg as [dg Hdg].
  exists (fun x => projT1 (req_mv_adjoint (df x)) (dg (f x))).
  intros x eps Heps.
  destruct (req_inner_lipschitz (dg (f x))) as [Na [HNa0 HNa2]].
  destruct (req_op_lipschitz (df x)) as [Nop [HNop0 HNop2]].
  pose (eps4 := mult (inv_pos (plus one one) req_two_pos)
                     (mult (inv_pos (plus one one) req_two_pos) eps)).
  assert (Heps4 : lt zero eps4).
  { unfold eps4. apply mult_positive.
    - apply inv_pos_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps]. }
  pose (M := plus Na one).
  assert (HM : lt zero M) by (unfold M; exact (req_plus_le_lt_pos Na one HNa0 one_pos)).
  pose (L := plus Nop one).
  assert (HL : lt zero L) by (unfold L; exact (req_plus_le_lt_pos Nop one HNop0 one_pos)).
  pose (eps_f := min one (mult (inv_pos M HM) eps4)).
  assert (Heps_f : lt zero eps_f).
  { unfold eps_f. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  pose (eps_g := min one (mult (inv_pos L HL) eps4)).
  assert (Heps_g : lt zero eps_g).
  { unfold eps_g. apply min_pos.
    - apply one_pos.
    - apply mult_positive; [apply inv_pos_pos | exact Heps4]. }
  destruct (Hdf x eps_f Heps_f) as [dfd [Hdf1 Hdf2]].
  destruct (Hdg (f x) eps_g Heps_g) as [dgd [Hdg1 Hdg2]].
  exists (min dfd (min one (mult (inv_pos L HL) dgd))).
  split.
  - assert (Hltm : lt zero (mult (inv_pos L HL) dgd))
      by (apply mult_positive; [apply inv_pos_pos | exact Hdg1]).
    exact (min_pos dfd (min one (mult (inv_pos L HL) dgd)) Hdf1
             (min_pos one (mult (inv_pos L HL) dgd) one_pos Hltm)).
  - intros h Hh.
    pose (s := mtr h S0).
    pose (Dg := req_sminus SS (f (spl x h)) (f x)).
    pose (adj := projT1 (req_mv_adjoint (df x)) (dg (f x))).
    assert (Hadj : forall w : Sc, req (inn (df x w) (dg (f x))) (inn w adj)).
    { intro w. exact (projT2 (req_mv_adjoint (df x)) w (dg (f x))). }
    assert (Hh_dfd : lt s dfd).
    { exact (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd))) dfd Hh
             (min_le_l_plain dfd (min one (mult (inv_pos L HL) dgd)))). }
    assert (Hh_dgds : lt s (mult (inv_pos L HL) dgd)).
    { exact (lt_le_trans s (min one (mult (inv_pos L HL) dgd))
                         (mult (inv_pos L HL) dgd)
               (lt_le_trans s (min dfd (min one (mult (inv_pos L HL) dgd)))
                            (min one (mult (inv_pos L HL) dgd)) Hh
                            (min_le_r_plain dfd
                               (min one (mult (inv_pos L HL) dgd))))
               (min_le_r_plain one (mult (inv_pos L HL) dgd))). }
    assert (Hef : le eps_f one).
    { exact (min_le_l_plain one (mult (inv_pos M HM) eps4)). }
    assert (Hspos : le zero s) by exact (rs_metric_pos SS h S0).
    (* 载体差消去（Id splus_sminus_cancel L27272 同族；记录 Id 律字段直推） *)
    assert (Hcancel : Id (spl (f x) Dg) (f (spl x h))).
    { unfold req_sminus.
      assert (H1 : Id (spl (f x) (spl (f (spl x h)) (rs_opp SS (f x))))
                      (spl (f x) (spl (rs_opp SS (f x)) (f (spl x h)))))
        by exact (id_cong (fun z => spl (f x) z)
                          (rs_plus_comm SS (f (spl x h))
                                        (rs_opp SS (f x)))).
      assert (H2 : Id (spl (f x) (spl (rs_opp SS (f x)) (f (spl x h))))
                      (spl (spl (f x) (rs_opp SS (f x))) (f (spl x h))))
        by exact (rs_plus_assoc SS (f x) (rs_opp SS (f x))
                                (f (spl x h))).
      assert (H3 : Id (spl (spl (f x) (rs_opp SS (f x))) (f (spl x h)))
                      (spl S0 (f (spl x h))))
        by exact (id_cong (fun z => spl z (f (spl x h)))
                          (rs_plus_opp SS (f x))).
      assert (H4 : Id (spl S0 (f (spl x h))) (f (spl x h)))
        by exact (id_trans (rs_plus_comm SS S0 (f (spl x h)))
                           (rs_plus_zero SS (f (spl x h)))).
      exact (id_trans H1 (id_trans H2 (id_trans H3 H4))). }
    assert (Hgu : req (g (spl (f x) Dg)) (g (f (spl x h)))).
    { exact (req_sfield_wd g (spl (f x) Dg) (f (spl x h)) Hcancel). }
    (* (a) |Dg| ≤ L·s *)
    assert (HDg : le (mtr Dg S0) (mult L s)).
    { apply (le_trans (mtr Dg S0)
                      (plus (mtr Dg (df x h)) (mtr (df x h) S0)) (mult L s)).
      - exact (rs_metric_triangle SS Dg (df x h) S0).
      - apply (le_trans (plus (mtr Dg (df x h)) (mtr (df x h) S0))
                        (plus (mult eps_f s) (mult Nop s)) (mult L s)).
        + exact (le_plus_compat (mtr Dg (df x h)) (mult eps_f s)
                                (mtr (df x h) S0) (mult Nop s)
                                (Hdf2 h Hh_dfd) (HNop2 h)).
        + apply (le_trans (plus (mult eps_f s) (mult Nop s))
                          (mult (plus eps_f Nop) s) (mult L s)).
          * exact (le_id_l (plus (mult eps_f s) (mult Nop s))
                           (mult (plus eps_f Nop) s) (mult (plus eps_f Nop) s)
                           (req_sym (mult (plus eps_f Nop) s)
                                    (plus (mult eps_f s) (mult Nop s))
                                    (req_mult_plus_distr_r eps_f Nop s))
                           (le_refl (mult (plus eps_f Nop) s))).
          * exact (le_mult_compat_weak (plus eps_f Nop) L s Hspos
                       (le_trans (plus eps_f Nop) (plus one Nop) L
                                 (le_plus_compat eps_f one Nop Nop Hef
                                                 (le_refl Nop))
                                 (le_id_l (plus one Nop) L L (plus_comm one Nop)
                                          (le_refl L)))). }
    (* |Dg| < dgd *)
    assert (HDg_lt : lt (mtr Dg S0) dgd).
    { apply (le_lt_trans (mtr Dg S0) (mult L s) dgd).
      - exact HDg.
      - exact (lt_id_l (mult L s) (mult s L) dgd (mult_comm L s)
                 (lt_id_r (mult s L) (mult (mult (inv_pos L HL) dgd) L) dgd
                    (req_trans (mult (mult (inv_pos L HL) dgd) L)
                               (mult L (mult (inv_pos L HL) dgd)) dgd
                               (mult_comm (mult (inv_pos L HL) dgd) L)
                               (req_rdf_inv_cancel L dgd HL Hdg1))
                    (lt_mult_compat s (mult (inv_pos L HL) dgd) L HL Hh_dgds))). }
    (* T1 *)
    assert (HT1 : le (abs (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (inn (dg (f x)) Dg))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (g (f (spl x h)))
                                      (plus (g (f x)) (inn (dg (f x)) Dg))))
                      (mult eps_g (mtr Dg S0)) (mult eps4 s)).
      - apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                       (plus (g (f x)) (inn (dg (f x)) Dg))))
                       (abs (req_minus (g (spl (f x) Dg))
                                       (plus (g (f x)) (inn (dg (f x)) Dg))))
                       (mult eps_g (mtr Dg S0))
                       (req_abs_compat
                          (req_minus (g (f (spl x h)))
                                     (plus (g (f x)) (inn (dg (f x)) Dg)))
                          (req_minus (g (spl (f x) Dg))
                                     (plus (g (f x)) (inn (dg (f x)) Dg)))
                          (req_rdf_minus_compat_l (g (f (spl x h)))
                             (g (spl (f x) Dg))
                             (plus (g (f x)) (inn (dg (f x)) Dg))
                             (req_sym (g (spl (f x) Dg)) (g (f (spl x h)))
                                      Hgu)))).
        exact (Hdg2 Dg HDg_lt).
      - apply (le_trans (mult eps_g (mtr Dg S0)) (mult eps_g (mult L s))
                        (mult eps4 s)).
        + exact (req_le_mult_compat_r eps_g (mtr Dg S0) (mult L s)
                     (lt_le_iff zero eps_g (inl Heps_g)) HDg).
        + apply (le_trans (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                          (mult eps4 s)).
          * exact (le_id_l (mult eps_g (mult L s)) (mult (mult eps_g L) s)
                           (mult (mult eps_g L) s) (mult_assoc eps_g L s)
                           (le_refl (mult (mult eps_g L) s))).
          * apply (le_trans (mult (mult eps_g L) s)
                            (mult (mult (mult (inv_pos L HL) eps4) L) s)
                            (mult eps4 s)).
            -- exact (le_mult_compat_weak (mult eps_g L)
                          (mult (mult (inv_pos L HL) eps4) L) s Hspos
                          (le_trans (mult eps_g L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (mult (mult (inv_pos L HL) eps4) L)
                                    (le_mult_compat_weak eps_g
                                       (mult (inv_pos L HL) eps4) L
                                       (lt_le_iff zero L (inl HL))
                                       (min_le_r_plain one
                                          (mult (inv_pos L HL) eps4)))
                                    (le_refl (mult (mult (inv_pos L HL) eps4) L)))).
            -- exact (le_mult_compat_weak (mult (mult (inv_pos L HL) eps4) L)
                          eps4 s Hspos (req_rdf_inv_scale_le L eps4 HL)). }
    (* T2：伴随梯度内积差 ≤ N_a 系 *)
    assert (HT2 : le (abs (req_minus (inn (dg (f x)) Dg)
                                     (inn (dg (f x)) (df x h))))
                      (mult eps4 s)).
    { apply (le_trans (abs (req_minus (inn (dg (f x)) Dg)
                                      (inn (dg (f x)) (df x h))))
                      (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                      (mult eps4 s)).
      - exact (le_id_l (abs (req_minus (inn (dg (f x)) Dg)
                                       (inn (dg (f x)) (df x h))))
                       (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                       (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                       (req_abs_compat (req_minus (inn (dg (f x)) Dg)
                                                  (inn (dg (f x)) (df x h)))
                          (inn (dg (f x)) (req_sminus SS Dg (df x h)))
                          (req_sym (inn (dg (f x)) (req_sminus SS Dg (df x h)))
                                   (req_minus (inn (dg (f x)) Dg)
                                              (inn (dg (f x)) (df x h)))
                                   (req_inner_sminus_r (dg (f x)) Dg (df x h))))
                       (le_refl (abs (inn (dg (f x))
                                          (req_sminus SS Dg (df x h)))))).
      - apply (le_trans (abs (inn (dg (f x)) (req_sminus SS Dg (df x h))))
                        (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                        (mult eps4 s)).
        + exact (HNa2 (req_sminus SS Dg (df x h))).
        + apply (le_trans (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                          (mult Na (mult eps_f s)) (mult eps4 s)).
          * exact (le_id_l (mult Na (mtr (req_sminus SS Dg (df x h)) S0))
                           (mult Na (mtr Dg (df x h)))
                           (mult Na (mult eps_f s))
                           (req_mult_compat Na Na
                              (mtr (req_sminus SS Dg (df x h)) S0)
                              (mtr Dg (df x h))
                              (req_refl Na)
                              (req_smetric_sminus_zero Dg (df x h)))
                           (req_le_mult_compat_r Na (mtr Dg (df x h))
                              (mult eps_f s) HNa0 (Hdf2 h Hh_dfd))).
          * apply (le_trans (mult Na (mult eps_f s))
                            (mult (mult Na eps_f) s) (mult eps4 s)).
            -- exact (le_id_l (mult Na (mult eps_f s))
                              (mult (mult Na eps_f) s)
                              (mult (mult Na eps_f) s) (mult_assoc Na eps_f s)
                              (le_refl (mult (mult Na eps_f) s))).
            -- apply (le_trans (mult (mult Na eps_f) s)
                              (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                              (mult eps4 s)).
              ++ exact (le_trans (mult (mult Na eps_f) s)
                                 (mult (mult Na (mult (inv_pos M HM) eps4)) s)
                                 (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                 (le_mult_compat_weak (mult Na eps_f)
                                    (mult Na (mult (inv_pos M HM) eps4)) s
                                    Hspos
                                    (req_le_mult_compat_r Na eps_f
                                       (mult (inv_pos M HM) eps4) HNa0
                                       (min_le_r_plain one
                                          (mult (inv_pos M HM) eps4))))
                                 (le_id_l
                                    (mult (mult Na (mult (inv_pos M HM) eps4)) s)
                                    (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                    (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                    (req_mult_compat
                                       (mult Na (mult (inv_pos M HM) eps4))
                                       (mult (mult (inv_pos M HM) eps4) Na) s s
                                       (mult_comm Na (mult (inv_pos M HM) eps4))
                                       (req_refl s))
                                    (le_refl (mult (mult (mult (inv_pos M HM) eps4)
                                                       Na) s)))).
              ++ assert (Hcoef : le (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                            (mult eps4 s)).
                 { apply (le_trans (mult (mult (mult (inv_pos M HM) eps4) Na) s)
                                   (mult (mult (mult (inv_pos M HM) eps4) M) s)
                                   (mult eps4 s)).
                   - exact (le_mult_compat_weak
                               (mult (mult (inv_pos M HM) eps4) Na)
                               (mult (mult (inv_pos M HM) eps4) M) s Hspos
                               (req_le_mult_compat_r
                                  (mult (inv_pos M HM) eps4) Na M
                                  (le_id_l zero (mult zero eps4)
                                     (mult (inv_pos M HM) eps4)
                                     (req_sym (mult zero eps4) zero
                                        (req_trans (mult zero eps4)
                                                   (mult eps4 zero) zero
                                                   (mult_comm zero eps4)
                                                   (mult_zero eps4)))
                                     (le_mult_compat_weak zero
                                        (inv_pos M HM) eps4
                                        (lt_le_iff zero eps4 (inl Heps4))
                                        (lt_le_iff zero (inv_pos M HM)
                                                   (inl (inv_pos_pos M HM)))))
                                  (req_le_plus_nonneg_r Na one
                                     (lt_le_iff zero one (inl one_pos))))).
                   - exact (le_mult_compat_weak
                               (mult (mult (inv_pos M HM) eps4) M)
                               eps4 s Hspos (req_rdf_inv_scale_le M eps4 HM)). }
                 exact Hcoef. }
    (* 完成：伴随恒等式换形 + 通用分解 + 三角 + eps/4 核算 *)
    apply (le_id_l (abs (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (inn adj h))))
                   (abs (plus (req_minus (g (f (spl x h)))
                                          (plus (g (f x)) (inn (dg (f x)) Dg)))
                              (req_minus (inn (dg (f x)) Dg)
                                        (inn (dg (f x)) (df x h)))))
                   (mult eps s)).
    + exact (req_abs_compat
               (req_minus (g (f (spl x h))) (plus (g (f x)) (inn adj h)))
               (plus (req_minus (g (f (spl x h)))
                                (plus (g (f x)) (inn (dg (f x)) Dg)))
                     (req_minus (inn (dg (f x)) Dg)
                                (inn (dg (f x)) (df x h))))
               (req_trans
                  (req_minus (g (f (spl x h))) (plus (g (f x)) (inn adj h)))
                  (req_minus (g (f (spl x h)))
                             (plus (g (f x)) (inn (dg (f x)) (df x h))))
                  (plus (req_minus (g (f (spl x h)))
                                   (plus (g (f x)) (inn (dg (f x)) Dg)))
                        (req_minus (inn (dg (f x)) Dg)
                                   (inn (dg (f x)) (df x h))))
                  (req_rdf_minus_compat_r (g (f (spl x h)))
                     (plus (g (f x)) (inn adj h))
                     (plus (g (f x)) (inn (dg (f x)) (df x h)))
                     (req_plus_compat (g (f x)) (g (f x))
                        (inn adj h) (inn (dg (f x)) (df x h))
                        (req_refl (g (f x)))
                        (req_trans (inn adj h) (inn h adj)
                                   (inn (dg (f x)) (df x h))
                                   (rh_inner_sym SS HS adj h)
                                   (req_trans (inn h adj)
                                              (inn (df x h) (dg (f x)))
                                              (inn (dg (f x)) (df x h))
                                              (req_sym (inn (df x h) (dg (f x)))
                                                       (inn h adj)
                                                       (Hadj h))
                                              (rh_inner_sym SS HS
                                                 (df x h) (dg (f x)))))))
                  (req_rdf_mv_vec_decomp (g (f (spl x h))) (g (f x))
                     (inn (dg (f x)) (df x h)) (inn (dg (f x)) Dg)))).
    + apply (le_trans (abs (plus (req_minus (g (f (spl x h)))
                                                (plus (g (f x))
                                                      (inn (dg (f x)) Dg)))
                                         (req_minus (inn (dg (f x)) Dg)
                                                    (inn (dg (f x)) (df x h)))))
                      (plus (abs (req_minus (g (f (spl x h)))
                                            (plus (g (f x)) (inn (dg (f x)) Dg))))
                            (abs (req_minus (inn (dg (f x)) Dg)
                                            (inn (dg (f x)) (df x h)))))
                      (mult eps s)).
      * exact (req_rdf_abs_triangle (req_minus (g (f (spl x h)))
                                               (plus (g (f x))
                                                     (inn (dg (f x)) Dg)))
                                    (req_minus (inn (dg (f x)) Dg)
                                               (inn (dg (f x)) (df x h)))).
      * apply (le_trans (plus (abs (req_minus (g (f (spl x h)))
                                              (plus (g (f x))
                                                    (inn (dg (f x)) Dg))))
                              (abs (req_minus (inn (dg (f x)) Dg)
                                              (inn (dg (f x)) (df x h)))))
                        (plus (mult eps4 s) (mult eps4 s)) (mult eps s)).
        -- exact (le_plus_compat
                    (abs (req_minus (g (f (spl x h)))
                                    (plus (g (f x)) (inn (dg (f x)) Dg))))
                    (mult eps4 s)
                    (abs (req_minus (inn (dg (f x)) Dg)
                                    (inn (dg (f x)) (df x h))))
                    (mult eps4 s) HT1 HT2).
        -- exact (req_rdf_quarter_pair_le_final eps s Heps Hspos).
Qed.

End ReqRDFMV.

(* ===================================================================== *)

(*   3 孤立 Qed 与追加占位标记截除，早期版本快照另存独立档案）    *)
(* ===================================================================== *)
End ReqRDFScalar.


