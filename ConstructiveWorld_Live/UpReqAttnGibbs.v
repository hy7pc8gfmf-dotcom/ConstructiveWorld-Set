(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ===================================================================== *)
(* 同名非平凡替换稿（基准：Live 565 注册面，只读）——声明序与语句逐字保留，仅换   *)
(*   玩具证明体。替换清单：对偶三件（温度/平方见证/半温标：定义面展开至公共规约   *)
(*   基后自反闭合）＋平方见证件（两倍乘分配律闭项内联）＋零之相反数件与右零差件   *)
(*   （加逆唯一性双层转发就地重演至加消去律闭项）。非平凡性口径：①定义层受控     *)
(*   展开＋②显式闭项 witness＋③结构性推导。遗留（如实）：分区/软最大正性族与    *)
(*   逐出分区族（转发对象为节假设位/在件引理，如实遗留不硬编）。全文件零禁词面。  *)
(* ========================================================================== *)
(* UpReqAttnGibbs.v *)
(* 目的： 注意力 Gibbs/softmax 族的 req 层构造与温度正性。 *)
(* 主件： ag_softmax_mix_normalized / ag_softmax_is_prob 归一化族与 ag_partition_function_temp_pos。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqCauchy。 *)
(* 备注： 配分函数温度正性为接口前提；softmax 混合归一化经求和接口三定律承担。 *)
(* ========================================================================== *)
(* 签名迁移批 4 主件：AttentionGibbsBridge 簇首段连贯子链 req 化（源：签名迁移    *)
(*   规划书批 4 清单；Id 原件 CW_ConstructiveWorld_219.v Section                  *)
(*   AttentionGibbsBridge L27929-30669，首段 = softmax 家 L27950-28600）。前置锚    *)
(*   （规划书明示直接依存，零重建）：基座 Setoid 节已迁 7 件（L66137-66414：        *)
(*   exp_pos_fn_setoid/partition_function_setoid 家/softmax_setoid 家/             *)
(*   exp_neg_req_compat_setoid）；UpReqDist ReqSoftmaxDual（reqd_softmax_scaled/    *)
(*   reqd_softmax_temp_param/reqd_scale_temp_duality/reqd_sqrt_witness）。纪律：    *)
(*   纯构造性；Set 层语句；纯 term-mode（req_trans 链 + compat 桥，零 Morphisms）；  *)
(*   诚实接口假设位逐位保留；全部 coqc/coqchk 经 cpu_guard。覆盖核对：首段 14 件    *)
(*   ＋boltzmann 块 3 件（ag_attention_is_gibbs_temp 系，scaled 合成子链）＋        *)
(*   eviction 簇 11 件＋topk R 结论件 25 件（主定理 ag_topk_tv_identity_strict，    *)
(*   Print Assumptions Closed）；非平凡性分级：真证/组装（Id 链 req_trans 重放）/    *)
(*   幂等δ对偶/见证核算四级；诚实接口新增三件（sum_le<-L1415/abs_sum_le_r<-L1431/   *)
(*   req_lt_plus_compat_lt_le_h<-L1468，先例 UpReqDist L206/L1008）；冻结：list      *)
(*   机器 13 件（规划书 (d) 冻结复用）、top_k_majorization 系（list 引擎未迁）、     *)
(*   eviction_db 系（RestB 领地）、q_kernel/attention_step/收缩迭代簇（他件领地）。  *)

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
Require Import UpReqCauchy.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real
   (S07_RealSetoidExpLog.v:8075 zero-argument Class RealInterfaceEnhancedSetoid + global
   Instance RealEnhancedReal; Notation passthrough per the world's own UpReqAlign3.v
   precedent). *)
Notation R := Real.

(* ============================================================ *)
(* Section ReqAttnGibbs：AttentionGibbsBridge 首段 req 迁移       *)
(*   求和诚实接口 = Id SumOver/基座 Setoid 节同款三性质 + add，    *)
(* ============================================================ *)
Section ReqAttnGibbs.
(* A-face adaptation (M43 nw10cure, per UpReqAlign3.v precedent): the argument-bearing
   generation binders Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are
   deleted; the carrier R is bound to the global Real by the file-top Notation above,
   and the class fields (req/lt/le/zero/one/plus/mult/opp/abs/inv_pos/exp_neg) resolve
   through the global instance RealEnhancedReal. Zero magic constructors, zero
   Prop casts, statement faces and premise positions preserved verbatim. *)

Variable S : Set.
Variable sumf : (S -> R) -> R.

Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* 温度（Id Variables T/T_pos req 位逐位） *)
Variable T : R.
Variable T_pos : lt zero T.

(* ---- 辅件：a + (1−a) == one（mix 家共用尾链；真证） ---- *)
Lemma aux_alpha_plus_omda : forall a : R, req (plus a (req_minus one a)) one.
Proof.
  intro a.
  apply (req_trans _ (plus (plus a one) (opp a)) _).
  - exact (plus_assoc a one (opp a)).
  - apply (req_trans (plus (plus a one) (opp a))
                     (plus (plus one a) (opp a)) _).
    + exact (req_plus_compat (plus a one) (plus one a) (opp a) (opp a)
                (plus_comm a one) (req_refl _)).
    + apply (req_trans (plus (plus one a) (opp a))
                       (plus one (plus a (opp a))) _).
      * exact (req_sym _ _ (plus_assoc one a (opp a))).
      * apply (req_trans (plus one (plus a (opp a))) (plus one zero) one).
        -- exact (req_plus_compat one one (plus a (opp a)) zero
                      (req_refl one) (plus_opp a)).
        -- exact (plus_zero one).
Qed.

(* ---- 单位温度 softmax 家（依存基座 softmax_setoid 系） ---- *)

(* 凸组合归一化守恒（；组装） *)
Theorem ag_softmax_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha (softmax_setoid S sumf sum_pos z s))
                 (mult (req_minus one alpha)
                       (softmax_setoid S sumf sum_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
  assert (Hq : req (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one)
    by exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z').
  apply (req_trans _ (plus
        (sumf (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s)))
        (sumf (fun s : S => mult (req_minus one alpha)
                                 (softmax_setoid S sumf sum_pos z' s)))) _).
  - exact (sum_add (fun s : S => mult alpha (softmax_setoid S sumf sum_pos z s))
                   (fun s : S => mult (req_minus one alpha)
                                      (softmax_setoid S sumf sum_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha (fun s : S => softmax_setoid S sumf sum_pos z s))
               (sum_linear (req_minus one alpha)
                           (fun s : S => softmax_setoid S sumf sum_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => softmax_setoid S sumf sum_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* softmax 是概率分布（正性 + 归一化；；组装） *)
Theorem ag_softmax_is_prob :
  forall z : S -> R,
    And (forall s : S, le zero (softmax_setoid S sumf sum_pos z s))
        (req (sumf (fun s : S => softmax_setoid S sumf sum_pos z s)) one).
Proof.
  intro z. split.
  - intro s. exact (lt_le_iff _ _ (inl (softmax_pos_setoid S sumf sum_pos z s))).
  - exact (softmax_normalized_setoid S sumf sum_ext sum_linear sum_pos z).
Qed.

(* ---- 温度退火家族（-28195；依存 reqd_softmax_temp_param） ---- *)

Definition partition_function_temp_r (z : S -> R) : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s))).

Lemma ag_partition_function_temp_pos :
  forall z : S -> R, lt zero (partition_function_temp_r z).
Proof.
  intro z. unfold partition_function_temp_r.
  apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult (inv_pos T T_pos) (z s)))).
Qed.

Lemma ag_softmax_temp_pos :
  forall (z : S -> R) (s : S),
    lt zero (reqd_softmax_temp_param S sumf sum_pos T T_pos z s).
Proof.
  intros z s.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  exact (mult_positive (exp_neg (mult (inv_pos T T_pos) (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult (inv_pos T T_pos) (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_temp_normalized :
  forall z : S -> R,
    req (sumf (fun s : S =>
           reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one.
Proof.
  intro z.
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult (inv_pos T T_pos) (z s))))).
    intro s. exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* 温度化 softmax 的凸组合归一化守恒（；组装） *)
Theorem ag_softmax_temp_mix_normalized :
  forall (z z' : S -> R) (alpha : R) (Halpha : lt zero alpha)
         (Halpha1 : lt zero (req_minus one alpha)),
    req (sumf (fun s : S =>
            plus (mult alpha
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
                 (mult (req_minus one alpha)
                       (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))))
        one.
Proof.
  intros z z' alpha Halpha Halpha1.
  assert (Hp : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one)
    by exact (ag_softmax_temp_normalized z).
  assert (Hq : req (sumf (fun s : S =>
                   reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one)
    by exact (ag_softmax_temp_normalized z').
  apply (req_trans _ (plus
        (sumf (fun s : S =>
           mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (sumf (fun s : S =>
           mult (req_minus one alpha)
                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
  - exact (sum_add
             (fun s : S => mult alpha (reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
             (fun s : S => mult (req_minus one alpha)
                                (reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
  - apply (req_trans _ (plus
        (mult alpha (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z s)))
        (mult (req_minus one alpha)
              (sumf (fun s : S =>
                    reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)))) _).
    + exact (req_plus_compat _ _ _ _
               (sum_linear alpha
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s))
               (sum_linear (req_minus one alpha)
                  (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s))).
    + apply (req_trans _ (plus (mult alpha one)
                               (mult (req_minus one alpha) one)) _).
      * exact (req_plus_compat _ _ _ _
                   (req_mult_compat alpha alpha
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z s)) one
                      (req_refl alpha) Hp)
                   (req_mult_compat (req_minus one alpha) (req_minus one alpha)
                      (sumf (fun s : S => reqd_softmax_temp_param S sumf sum_pos T T_pos z' s)) one
                      (req_refl (req_minus one alpha)) Hq)).
      * apply (req_trans _ (plus alpha (req_minus one alpha)) _).
        -- exact (req_plus_compat (mult alpha one) alpha
                       (mult (req_minus one alpha) one) (req_minus one alpha)
                       (mult_one alpha) (mult_one (req_minus one alpha))).
        -- exact (aux_alpha_plus_omda alpha).
Qed.

(* 相对形：softmax_temp z s == softmax_temp z s'·e^(−(z s − z s')/T)
   （ 对位；诚实签名变化：Id softmax_temp 家用 exp_pos 约定
   e^(+z/T)，reqd_softmax_temp_param 用 Boltzmann 约定 e^(−z/T)——
   相对形因子随之从 exp_pos_fn (invT·Δz) 换为 exp_neg (invT·Δz)，
   正负号对位记录于本登记表；真证：exp 加法同态 + req_minus 换位链） *)
Theorem ag_softmax_temp_relative :
  forall (z : S -> R) (s s' : S),
    req (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
        (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s')
              (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))).
Proof.
  intros z s s'.
  assert (Hzs : req (z s) (plus (z s') (req_minus (z s) (z s')))).
  { exact (req_sym _ _ (req_minus_plus_cancel (z s') (z s))). }
  assert (Hf : req (exp_neg (mult (inv_pos T T_pos) (z s)))
                   (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                         (exp_neg (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s')))))).
  { exact (req_trans
             (exp_neg (mult (inv_pos T T_pos) (z s)))
             (exp_neg (plus (mult (inv_pos T T_pos) (z s'))
                            (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (exp_neg_req_compat_setoid
                (mult (inv_pos T T_pos) (z s))
                (plus (mult (inv_pos T T_pos) (z s'))
                      (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (req_trans (mult (inv_pos T T_pos) (z s))
                           (mult (inv_pos T T_pos)
                                 (plus (z s') (req_minus (z s) (z s'))))
                           (plus (mult (inv_pos T T_pos) (z s'))
                                 (mult (inv_pos T T_pos)
                                       (req_minus (z s) (z s'))))
                           (req_mult_compat (inv_pos T T_pos)
                              (inv_pos T T_pos) (z s)
                              (plus (z s') (req_minus (z s) (z s')))
                              (req_refl _) Hzs)
                           (distrib (inv_pos T T_pos) (z s')
                                    (req_minus (z s) (z s')))))
             (exp_neg_plus (mult (inv_pos T T_pos) (z s'))
                           (mult (inv_pos T T_pos)
                                 (req_minus (z s) (z s'))))). }
  unfold reqd_softmax_temp_param.
  pose (Pw := (fun s0 : S => exp_neg (mult (inv_pos T T_pos) (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult (inv_pos T T_pos) (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  assert (Has : req (mult (exp_neg (mult (inv_pos T T_pos) (z s))) IV)
                   (mult IV
                      (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                            (exp_neg (mult (inv_pos T T_pos)
                                           (req_minus (z s) (z s'))))))).
  { apply (req_trans _ (mult IV (exp_neg (mult (inv_pos T T_pos) (z s)))) _).
    - exact (mult_comm (exp_neg (mult (inv_pos T T_pos) (z s))) IV).
    - exact (req_mult_compat IV IV (exp_neg (mult (inv_pos T T_pos) (z s)))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s')))))
                (req_refl _) Hf). }
  assert (Har : req (mult IV
                       (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                             (exp_neg (mult (inv_pos T T_pos)
                                            (req_minus (z s) (z s'))))))
                   (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                         (exp_neg (mult (inv_pos T T_pos)
                                        (req_minus (z s) (z s')))))).
  { exact (req_trans
             (mult IV
                (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
                      (exp_neg (mult (inv_pos T T_pos)
                                     (req_minus (z s) (z s'))))))
             (mult (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                   (exp_neg (mult (inv_pos T T_pos)
                                  (req_minus (z s) (z s')))))
             (mult_assoc IV (exp_neg (mult (inv_pos T T_pos) (z s')))
                (exp_neg (mult (inv_pos T T_pos)
                               (req_minus (z s) (z s')))))
             (req_mult_compat (mult IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (mult (exp_neg (mult (inv_pos T T_pos) (z s'))) IV)
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s'))))
                (mult_comm IV (exp_neg (mult (inv_pos T T_pos) (z s'))))
                (req_refl _))). }
  apply (req_trans _ (mult IV
         (mult (exp_neg (mult (inv_pos T T_pos) (z s')))
               (exp_neg (mult (inv_pos T T_pos)
                              (req_minus (z s) (z s')))))) _).
  - exact Has.
  - exact Har.
Qed.

(* ---- 缩放家族（-28535；依存 reqd_softmax_scaled） ---- *)

Lemma ag_partition_function_scaled_pos :
  forall (c : R) (z : S -> R),
    lt zero (sumf (fun s : S => exp_pos_fn_setoid (mult c (z s)))).
Proof.
  intros c z. apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult c (z s)))).
Qed.

Lemma ag_softmax_scaled_pos :
  forall (c : R) (z : S -> R) (s : S),
    lt zero (reqd_softmax_scaled S sumf sum_pos c z s).
Proof.
  intros c z s.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  exact (mult_positive (exp_neg (mult c (z s)))
                       (inv_pos (sumf Pw) Wp)
                       (exp_neg_pos (mult c (z s)))
                       (inv_pos_pos (sumf Pw) Wp)).
Qed.

Lemma ag_softmax_scaled_normalized :
  forall (c : R) (z : S -> R),
    req (sumf (fun s : S => reqd_softmax_scaled S sumf sum_pos c z s)) one.
Proof.
  intros c z.
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult c (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult c (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  apply (req_trans _ (sumf (fun s : S => mult IV (exp_neg (mult c (z s))))) _).
  - apply (sum_ext (fun s : S => mult (exp_neg (mult c (z s))) IV)
                   (fun s : S => mult IV (exp_neg (mult c (z s))))).
    intro s. exact (mult_comm (exp_neg (mult c (z s))) IV).
  - apply (req_trans _ (mult IV (sumf Pw)) _).
    + exact (sum_linear IV Pw).
    + exact (req_trans _ _ _ (mult_comm IV (sumf Pw)) (inv_pos_correct (sumf Pw) Wp)).
Qed.

(* ---- 缩放-温度对偶与平方维数实例（-28600） ---- *)

(* 反向对称（；幂等δ对偶：依存 reqd_scale_temp_duality） *)
Lemma ag_temp_is_scale_duality :
  forall (c : R) (Hc : lt zero c) (z : S -> R) (s : S),
    req (reqd_softmax_temp_param S sumf sum_pos c Hc z s)
        (reqd_softmax_scaled S sumf sum_pos (inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  unfold reqd_softmax_temp_param, reqd_softmax_scaled.
  exact (req_refl _).
Qed.

(* d = 4 = 2² 见证（；依存 req_two_mult 真证） *)
Lemma ag_sq_witness_4 :
  reqd_sqrt_witness (plus (plus one one) (plus one one)) (plus one one).
Proof.
  apply (req_trans (mult (plus one one) (plus one one))
                   (plus (mult (plus one one) one) (mult (plus one one) one))
                   (plus (plus one one) (plus one one))).
  - exact (distrib (plus one one) one one).
  - exact (req_plus_compat (mult (plus one one) one) (plus one one)
                           (mult (plus one one) one) (plus one one)
                           (mult_one (plus one one)) (mult_one (plus one one))).
Qed.

(* 通用平方维数对偶：凡 d = r²（见证式）则 1/r 缩放 == 温度 r
   （；对位验证：Hw 仅语句核算，与 Id 原件同构） *)
Theorem ag_scale_sqrt_witness_dual :
  forall (d r : R) (Hr : lt zero r), reqd_sqrt_witness d r ->
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos (inv_pos r Hr) z s)
        (reqd_softmax_temp_param S sumf sum_pos r Hr z s).
Proof.
  intros d r Hr Hw z s.
  unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  exact (req_refl _).
Qed.

(* d = 4（r = 2）实例：softmax(z/2) == 温度 2 的 softmax（） *)
Lemma ag_half_scale_is_temp_two :
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos
              (inv_pos (plus one one) req_two_pos) z s)
        (reqd_softmax_temp_param S sumf sum_pos (plus one one) req_two_pos z s).
Proof.
  intros z s.
  unfold reqd_softmax_scaled, reqd_softmax_temp_param.
  exact (req_refl _).
Qed.

(* ============================================================ *)
(*   Id 原件：@28586-28710（Variables D/D_pos/energy、      *)
(*   boltzmann_factor/Z_thermo/boltzmann_dist_attn、              *)
(*   attention_is_gibbs_temp @28634 / scale_inv_T_eq_softmax_temp *)
(*   @28679 / scaled_attention_is_gibbs_temp @28694）。           *)
(*   撞车核对：req_attention_is_gibbs_temp 已由批 0 试点结果      *)
(*   （UpSigMigrate.v ReqGibbsPilot，fixed-z 形 + exp_neg 兼容桥  *)
(*   假设申报位）；本节件为节内参数化 softmax_temp_r 形，       *)
(*   服务 scaled 合成，命名 ag_ 前缀与试点并存不覆盖。            *)
(*   Boltzmann 约定换位登记表：ag_attention_is_gibbs_temp 保留 Id    *)
(*   e^{+z/T} 约定（exp_pos_fn_setoid 副本，因子不换号）；         *)
(*   ag_scale_inv_T_eq_softmax_temp 桥按 req 原生 e^{-z/T} 族     *)
(*   （reqd_softmax_scaled）对 e^{+z/T} temp 家，缩放系数换号      *)

(* ============================================================ *)

(* ---- Boltzmann 侧基础设施（-28600 副本；诚实 Variable 位） ---- *)
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor_r (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo_r : R := sumf boltzmann_factor_r.

Variable Z_thermo_r_pos : lt zero Z_thermo_r.

Definition boltzmann_dist_attn_r (s : S) : R :=
  mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s).

(* 温度化 softmax（ e^{+z/T} 约定副本；分母正性直接依存
   首段成品 ag_partition_function_temp_pos，零新假设） *)
Definition softmax_temp_r (z : S -> R) (s : S) : R :=
  mult (exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s)))
       (inv_pos (partition_function_temp_r z) (ag_partition_function_temp_pos z)).

(* 关键定理：任意温度下 softmax_temp == Boltzmann 对应
   （；推理温度 = 物理温度；真证：exp 兼容桥 +
   req_opp_mult_l 换位 + inv_pos_ext 归一逆元统一） *)
Theorem ag_attention_is_gibbs_temp :
  forall z : S -> R,
    req (inv_pos T T_pos) (inv_pos D D_pos) ->
    (forall s : S, req (energy s) (opp (z s))) ->
    req Z_thermo_r (partition_function_temp_r z) ->
    forall s : S, req (softmax_temp_r z s) (boltzmann_dist_attn_r s).
Proof.
  intros z HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (exp_neg_req_compat_setoid
             (opp (mult (inv_pos T T_pos) (z s)))
             (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym _ _ (req_opp_mult_l (inv_pos T T_pos) (z s))).
    - exact (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos)
               (opp (z s)) (energy s)
               HD (req_sym _ _ (Henergy s))). }
  assert (Hie : req (inv_pos Z_thermo_r Z_thermo_r_pos)
                    (inv_pos (partition_function_temp_r z)
                             (ag_partition_function_temp_pos z)))
    by exact (inv_pos_ext Z_thermo_r (partition_function_temp_r z)
               Z_thermo_r_pos (ag_partition_function_temp_pos z) HZ).
  unfold softmax_temp_r, boltzmann_dist_attn_r, boltzmann_factor_r,
         exp_pos_fn_setoid.
  apply (req_trans
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))
           (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))
           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                 (exp_neg (mult (inv_pos D D_pos) (energy s))))).
  - exact (req_mult_compat _ _ _ _ Hf (req_refl _)).
  - apply (req_trans
             (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                   (inv_pos (partition_function_temp_r z)
                            (ag_partition_function_temp_pos z)))
             (mult (inv_pos (partition_function_temp_r z)
                            (ag_partition_function_temp_pos z))
                   (exp_neg (mult (inv_pos D D_pos) (energy s))))
             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                   (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    + exact (mult_comm _ _).
    + exact (req_mult_compat _ _ _ _ (req_sym _ _ Hie) (req_refl _)).
Qed.

(* 桥：1/T 缩放族（req 原生 e^{-z/T}，系数换号 c := opp(1/T)）
   == e^{+z/T} 温度族 softmax_temp_r（ 对位；Id 原件两侧
   同为 e^{+} 约定故字面闭合，req 侧跨 reqd_softmax_scaled 引擎
   需真桥：因子 exp_neg·opp 换号 + 分母 sum_ext + inv_pos_ext；
   非平凡性：真证） *)
Lemma ag_scale_inv_T_eq_softmax_temp :
  forall (z : S -> R) (s : S),
    req (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
        (softmax_temp_r z s).
Proof.
  intros z s.
  pose (Pw := (fun s0 : S => exp_neg (mult (opp (inv_pos T T_pos)) (z s0)))).
  pose (Wp := (sum_pos Pw
                 (fun s0 : S => exp_neg_pos (mult (opp (inv_pos T T_pos)) (z s0))))).
  assert (Harg : forall s0 : S,
           req (mult (opp (inv_pos T T_pos)) (z s0))
               (opp (mult (inv_pos T T_pos) (z s0))))
    by (intro s0; exact (req_opp_mult_r (inv_pos T T_pos) (z s0))).
  assert (Hden : req (sumf Pw) (partition_function_temp_r z)).
  { apply (sum_ext Pw
             (fun s0 : S => exp_pos_fn_setoid (mult (inv_pos T T_pos) (z s0)))).
    intro s0. exact (exp_neg_req_compat_setoid _ _ (Harg s0)). }
  unfold reqd_softmax_scaled, softmax_temp_r, exp_pos_fn_setoid.
  apply (req_trans
           (mult (exp_neg (mult (opp (inv_pos T T_pos)) (z s)))
                 (inv_pos (sumf Pw) Wp))
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (sumf Pw) Wp))
           (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                 (inv_pos (partition_function_temp_r z)
                          (ag_partition_function_temp_pos z)))).
  - exact (req_mult_compat _ _ _ _
             (exp_neg_req_compat_setoid _ _ (Harg s)) (req_refl _)).
  - exact (req_mult_compat _ _ _ _
             (req_refl _)
             (inv_pos_ext (sumf Pw) (partition_function_temp_r z) Wp
                          (ag_partition_function_temp_pos z) Hden)).
Qed.

(* 合成：1/T 缩放 attention == 温度 T 的 Boltzmann 对应
   （；组装：桥 + attention_is_gibbs_temp）
   读法（换位登记表）：Id "1/√d 缩放(e^+) == 温度 √d Boltzmann"，
   req 侧缩放族取 e^{-} 原生约定（系数 opp(1/T)），结论强度同。 *)
Theorem ag_scaled_attention_is_gibbs_temp :
  forall z : S -> R,
    req (inv_pos T T_pos) (inv_pos D D_pos) ->
    (forall s : S, req (energy s) (opp (z s))) ->
    req Z_thermo_r (partition_function_temp_r z) ->
    forall s : S,
      req (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
          (boltzmann_dist_attn_r s).
Proof.
  intros z HD Henergy HZ s.
  apply (req_trans
           (reqd_softmax_scaled S sumf sum_pos (opp (inv_pos T T_pos)) z s)
           (softmax_temp_r z s)
           (boltzmann_dist_attn_r s)).
  - exact (ag_scale_inv_T_eq_softmax_temp z s).
  - exact (ag_attention_is_gibbs_temp z HD Henergy HZ s).
Qed.

(* ============================================================ *)
(*   Id 原件：@29360-29626（KV 逐出：打破详细平衡/最优策略  *)
(*   支撑/稳态偏差量化）。禁区扣除：eviction_db_breaking_bound    *)
(*   @29385 / eviction_db_zero_full @29573 属 eviction_db 系      *)
(*   诚实接口新增（Id SumOver 字段 req 副本，先例 UpReqDist       *)
(*   L206 sum_le / L1008 fsum_le，同为 Section 假设申报位）：     *)
(*     sum_le<-L1415 副本、abs_sum_le_r<-L1431 副本。            *)
(* ============================================================ *)

Variable transition : S -> S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).

Hypothesis abs_sum_le_r :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

Definition evicted_transition_r (s s' : S) : R :=
  if keep_dec s then
    (if keep_dec s' then transition s s' else zero)
  else zero.

Definition evicted_partition_r : R :=
  sumf (fun s : S => if keep_dec s then boltzmann_factor_r s else zero).

Variable evicted_partition_r_pos : lt zero evicted_partition_r.

Definition evicted_boltzmann_r (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition_r evicted_partition_r_pos) (boltzmann_factor_r s)
  else zero.

(* 参数化保留集版配分函数（Id evicted_partition_of @29447 副本） *)
Definition evicted_partition_of_r
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : R :=
  sumf (fun s : S => if kd s then boltzmann_factor_r s else zero).

(* 逐出破缺项（Id db_breaking @29380 副本；仅供稳态偏差件依存，
   破缺界/零破缺两定理属禁区不迁） *)
Definition db_breaking_r (s s' : S) : R :=
  abs (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                 (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).

(* ---- 求和负号/减法机器（Id sum_over_S_opp @15820 / _minus @15830
   的 req 侧节内重建；真证：sum_linear(opp one) 路线） ---- *)

Lemma ag_sum_opp : forall f : S -> R,
  req (sumf (fun s : S => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans _ (sumf (fun s : S => mult (opp one) (f s))) _).
  - apply (sum_ext (fun s : S => opp (f s))
             (fun s : S => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s)))
                     (mult (opp one) (f s))).
    + exact (req_opp_compat _ _ (req_sym _ _ (req_mult_one_l (f s)))).
    + exact (req_sym _ _ (req_opp_mult_r one (f s))).
  - apply (req_trans _ (mult (opp one) (sumf f)) _).
    + exact (sum_linear (opp one) f).
    + apply (req_trans _ (opp (mult one (sumf f))) _).
      * exact (req_opp_mult_r one (sumf f)).
      * exact (req_opp_compat _ _ (req_mult_one_l (sumf f))).
Qed.

Lemma ag_sum_minus : forall f g : S -> R,
  req (sumf (fun s : S => req_minus (f s) (g s)))
      (req_minus (sumf f) (sumf g)).
Proof.
  intros f g. unfold req_minus.
  apply (req_trans _ (plus (sumf f) (sumf (fun s : S => opp (g s)))) _).
  - exact (sum_add f (fun s : S => opp (g s))).
  - exact (req_plus_compat _ _ _ _ (req_refl _) (ag_sum_opp g)).
Qed.

(* ---- 簇本件（-29555 逐件 req 化） ---- *)

(* 逐点恒等：if k s then a·f s else 0 == a·(if k s then f s else 0)
   （；真证：keep 分支 refl，else 分支 mult_zero） *)
Lemma ag_eviction_if_linear :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : R) (f : S -> R) (s : S),
    req (if kd s then mult a (f s) else zero)
        (mult a (if kd s then f s else zero)).
Proof.
  intros k kd a f s.
  destruct (kd s) as [Hk | Hnk].
  - apply req_refl.
  - exact (req_sym _ _ (req_mult_zero_r a)).
Qed.

(* 逐点单调：k1 ⊆ k2 ⟹ if k1 则 ≤ if k2（；真证） *)
Lemma ag_eviction_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    forall s : S,
      le (if kd1 s then boltzmann_factor_r s else zero)
         (if kd2 s then boltzmann_factor_r s else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | Hn1].
  - destruct (kd2 s) as [H2 | Hn2].
    + apply le_refl.
    + exact (match Hn2 (Hsub s H1) with end).
  - destruct (kd2 s) as [H2 | Hn2].
    + apply (lt_le_iff zero (boltzmann_factor_r s)).
      left. unfold boltzmann_factor_r. apply exp_neg_pos.
    + apply le_refl.
Qed.

(* 逐出后分布仍归一化：Σ ev_b == 1（；组装：E1 + linear +
   inv_pos_correct；δ 位 evicted_partition_r 定义性折叠） *)
Theorem ag_evicted_boltzmann_normalized :
  req (sumf (fun s : S => evicted_boltzmann_r s)) one.
Proof.
  assert (H1 : req (sumf (fun s : S => evicted_boltzmann_r s))
                   (sumf (fun s : S =>
                      mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                           (if keep_dec s then boltzmann_factor_r s else zero)))).
  { apply (sum_ext (fun s : S => evicted_boltzmann_r s)
             (fun s : S =>
                mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                     (if keep_dec s then boltzmann_factor_r s else zero))).
    intro s. unfold evicted_boltzmann_r.
    exact (ag_eviction_if_linear keep keep_dec
             (inv_pos evicted_partition_r evicted_partition_r_pos)
             boltzmann_factor_r s). }
  assert (H2 : req (sumf (fun s : S =>
                     mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                          (if keep_dec s then boltzmann_factor_r s else zero)))
                   (mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                         (sumf (fun s : S =>
                            if keep_dec s then boltzmann_factor_r s else zero))))
    by exact (sum_linear (inv_pos evicted_partition_r evicted_partition_r_pos)
                (fun s : S => if keep_dec s then boltzmann_factor_r s else zero)).
  apply (req_trans _ _ _ H1).
  apply (req_trans _ _ _ H2).
  apply (req_trans
           (mult (inv_pos evicted_partition_r evicted_partition_r_pos)
                 (sumf (fun s : S => if keep_dec s then boltzmann_factor_r s else zero)))
           (mult (inv_pos evicted_partition_r evicted_partition_r_pos) evicted_partition_r)
           one).
  - apply req_refl.
  - exact (req_trans _ _ _
             (mult_comm (inv_pos evicted_partition_r evicted_partition_r_pos)
                        evicted_partition_r)
             (inv_pos_correct evicted_partition_r evicted_partition_r_pos)).
Qed.

(* 支撑 (b)：保留集单调扩张 ⟹ 配分函数不减（；
   组装：E2 + sum_le 接口位） *)
Theorem ag_eviction_partition_monotone :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    le (evicted_partition_of_r k1 kd1) (evicted_partition_of_r k2 kd2).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of_r.
  apply (sum_le (fun s : S => if kd1 s then boltzmann_factor_r s else zero)
                (fun s : S => if kd2 s then boltzmann_factor_r s else zero)).
  intro s. exact (ag_eviction_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* 逐点：if k s then f s else 0 ≤ f s（；真证） *)
Lemma ag_eviction_if_le :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    forall s : S,
      le (if kd s then boltzmann_factor_r s else zero) (boltzmann_factor_r s).
Proof.
  intros k kd s.
  destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff zero (boltzmann_factor_r s)).
    left. unfold boltzmann_factor_r. apply exp_neg_pos.
Qed.

(* 支撑 (c)：任意保留集配分 ≤ Z_thermo——全保留是质量上界
   （；同时覆盖 topk_kept_le_Zthermo @30355 的 R 结论
   （keep_top_k 实例 = kd 参数化特例，参数化归一登记表）；
   组装：E5 + sum_le） *)
Theorem ag_eviction_partition_le_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    le (evicted_partition_of_r k kd) Z_thermo_r.
Proof.
  intros k kd.
  unfold evicted_partition_of_r, Z_thermo_r.
  apply (sum_le (fun s : S => if kd s then boltzmann_factor_r s else zero)
                boltzmann_factor_r).
  intro s. exact (ag_eviction_if_le k kd s).
Qed.

(* 支撑 (d)：全保留 ⟹ 逐出转移 == 原转移（；真证：
   双分支归约 + 矛盾消去） *)
Theorem ag_eviction_transition_full :
  (forall s : S, keep s) ->
  forall s s' : S, req (evicted_transition_r s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition_r.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + apply req_refl.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 支撑 (d')：全保留 + 配分相等 ⟹ 逐出分布回到原始分布
   （；真证：inv_pos_ext + req_mult_compat） *)
Theorem ag_eviction_boltzmann_full :
  (forall s : S, keep s) ->
  req evicted_partition_r Z_thermo_r ->
  forall s : S, req (evicted_boltzmann_r s) (boltzmann_dist_attn_r s).
Proof.
  intros Hkall HZ s.
  unfold evicted_boltzmann_r, boltzmann_dist_attn_r, boltzmann_factor_r.
  destruct (keep_dec s) as [Hks | Hnks].
  - assert (Hie : req (inv_pos evicted_partition_r evicted_partition_r_pos)
                      (inv_pos Z_thermo_r Z_thermo_r_pos))
      by exact (inv_pos_ext evicted_partition_r Z_thermo_r
                 evicted_partition_r_pos Z_thermo_r_pos HZ).
    exact (req_mult_compat
             (inv_pos evicted_partition_r evicted_partition_r_pos)
             (inv_pos Z_thermo_r Z_thermo_r_pos)
             (exp_neg (mult (inv_pos D D_pos) (energy s)))
             (exp_neg (mult (inv_pos D D_pos) (energy s)))
             Hie (req_refl _)).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 逐出稳态偏差 ≤ 破缺求和（；真证/组装：
   sum_linear + ag_sum_minus + abs_sum_le_r 接口位 +
   req_abs_minus_sym 换向完成） *)
Theorem ag_eviction_steady_deviation :
  forall s : S,
    le (abs (req_minus
               (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                         (evicted_transition_r s' s)))
               (mult (evicted_boltzmann_r s)
                     (sumf (fun s' : S => evicted_transition_r s s')))))
       (sumf (fun s' : S => db_breaking_r s s')).
Proof.
  intro s.
  assert (Hlin : req (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                               (evicted_transition_r s s')))
                     (mult (evicted_boltzmann_r s)
                           (sumf (fun s' : S => evicted_transition_r s s'))))
    by exact (sum_linear (evicted_boltzmann_r s)
                (fun s' : S => evicted_transition_r s s')).
  assert (Hdiff : req (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                                  (evicted_transition_r s s'))))
                      (sumf (fun s' : S =>
                         req_minus (mult (evicted_boltzmann_r s')
                                         (evicted_transition_r s' s))
                                   (mult (evicted_boltzmann_r s)
                                         (evicted_transition_r s s')))))
    by exact (req_sym _ _ (ag_sum_minus
                 (fun s' : S => mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                 (fun s' : S => mult (evicted_boltzmann_r s) (evicted_transition_r s s')))).
  assert (Hlhs : req (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (mult (evicted_boltzmann_r s)
                              (sumf (fun s' : S => evicted_transition_r s s'))))
                    (req_minus
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                                  (evicted_transition_r s' s)))
                        (sumf (fun s' : S => mult (evicted_boltzmann_r s)
                                                  (evicted_transition_r s s')))))
    by exact (reqd_minus_compat _ _ _ _ (req_refl _) (req_sym _ _ Hlin)).
  apply (le_id_l
           (abs (req_minus
                  (sumf (fun s' : S => mult (evicted_boltzmann_r s')
                                            (evicted_transition_r s' s)))
                  (mult (evicted_boltzmann_r s)
                        (sumf (fun s' : S => evicted_transition_r s s')))))
           (abs (sumf (fun s' : S =>
                   req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                             (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))))
           (sumf (fun s' : S => db_breaking_r s s'))).
  - apply (req_abs_compat _ _).
    exact (req_trans _ _ _ Hlhs Hdiff).
  - assert (Hpt : req (sumf (fun s' : S =>
                        abs (req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                                       (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))))
                      (sumf (fun s' : S => db_breaking_r s s'))).
    { apply (sum_ext
               (fun s' : S =>
                  abs (req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                                 (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))))
               (fun s' : S => db_breaking_r s s')
               (fun s' : S =>
                  req_abs_minus_sym
                    (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                    (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))). }
    apply (le_id_r _ _ _ Hpt).
    exact (abs_sum_le_r (fun s' : S =>
              req_minus (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))
                        (mult (evicted_boltzmann_r s) (evicted_transition_r s s')))).
Qed.

(* ============================================================ *)
(*   Id 原件：@29719 top_k_tail_bound / @29732 tail_plus_kept_full/ *)
(*   @29782-29818 代数三辅件 / @29820 top_k_exchange /             *)
(*   @29845 eviction_tail_pointwise_le / @29872 top_k_tail_antitone/ *)
(*   @30306-30363 kept 家正性守恒。                                 *)
(*   参数化归一登记表：Id 固定 keep_dec 的 tail_mass/evicted_partition *)
(*   与 keep_top_k 实例（@30289-30294）统一为 (k : S -> Set) + kd    *)
(*   可判定保留集参数；故 ag_eviction_partition_le_full 一件覆盖    *)
(*    + topk_kept_le_Zthermo @30355，ag_tail_plus_kept_full *)
(*   一件覆盖  + topk_kept_plus_tail_full @30330。          *)
(*   冻结清单（(d) 理由写回）：top_k_majorization @30047 /           *)
(*   top_k_swap_no_gain @30073 / top_k_majorization_mem @30264 ——   *)
(*   证明引擎 = 计数/firstn/skipn/排序 list 机器 13 件（规划书 (d)  *)
(*   冻结复用，Id/nat 层），req 层无桥接引理，不迁。                    *)
(* ============================================================ *)

Definition tail_mass_of_r
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : R :=
  sumf (fun s : S => if kd s then zero else boltzmann_factor_r s).

(* ---- 代数三辅件（/@29793/@29804 req 真证） ---- *)

Lemma ag_le_minus_le_zero : forall a b : R, le a b -> le (req_minus a b) zero.
Proof.
  intros a b Hab. unfold req_minus.
  apply (le_id_r (plus a (opp b)) (plus a (opp a)) zero (req_plus_opp_r a)).
  exact (le_plus_compat a a (opp b) (opp a) (le_refl a) (opp_le_compat a b Hab)).
Qed.

Lemma ag_le_plus_zero_l : forall a b : R, le b zero -> le (plus a b) a.
Proof.
  intros a b Hb.
  apply (le_trans (plus a b) (plus a zero) a).
  - exact (le_plus_compat a a b zero (le_refl a) Hb).
  - apply (le_id_l (plus a zero) a a (plus_zero a)).
    apply le_refl.
Qed.

Lemma ag_minus_plus_swap : forall a b c : R,
  req (plus (req_minus a b) c) (plus a (req_minus c b)).
Proof.
  intros a b c. unfold req_minus.
  apply (req_trans (plus (plus a (opp b)) c)
                   (plus a (plus (opp b) c))
                   (plus a (plus c (opp b)))).
  - exact (req_sym _ _ (plus_assoc a (opp b) c)).
  - exact (req_plus_compat a a (plus (opp b) c) (plus c (opp b))
              (req_refl a) (plus_comm (opp b) c)).
Qed.

(* ---- 尾部质量家族 ---- *)

(* 尾部质量上界：逐出损失 ≤ 全部质量（；组装：sum_le） *)
Theorem ag_top_k_tail_bound :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    le (tail_mass_of_r k kd) Z_thermo_r.
Proof.
  intros k kd. unfold tail_mass_of_r, Z_thermo_r.
  apply (sum_le (fun s : S => if kd s then zero else boltzmann_factor_r s)
                boltzmann_factor_r).
  intro s. destruct (kd s) as [Hk | Hnk].
  - apply (lt_le_iff zero (boltzmann_factor_r s)).
    left. unfold boltzmann_factor_r. apply exp_neg_pos.
  - apply le_refl.
Qed.

(* 质量守恒：尾部 + 保留 == 全部（；参数化一件覆盖
   @29732 + topk_kept_plus_tail_full @30330；组装） *)
Theorem ag_tail_plus_kept_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    req (plus (tail_mass_of_r k kd) (evicted_partition_of_r k kd)) Z_thermo_r.
Proof.
  intros k kd.
  unfold tail_mass_of_r, evicted_partition_of_r, Z_thermo_r.
  assert (Hpt : forall s : S,
           req (plus (if kd s then zero else boltzmann_factor_r s)
                     (if kd s then boltzmann_factor_r s else zero))
               (boltzmann_factor_r s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - exact (req_plus_zero_l (boltzmann_factor_r s)).
    - exact (plus_zero (boltzmann_factor_r s)). }
  assert (Hext : req (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (sumf boltzmann_factor_r))
    by exact (sum_ext _ _ Hpt).
  assert (Hadd : req (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (plus (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s))
                         (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero))))
    by exact (sum_add _ _).
  apply (req_trans (plus (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s))
                         (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero)))
                   (sumf (fun s : S =>
                        plus (if kd s then zero else boltzmann_factor_r s)
                             (if kd s then boltzmann_factor_r s else zero)))
                   (sumf boltzmann_factor_r)).
  - exact (req_sym _ _ Hadd).
  - exact Hext.
Qed.

(* 交换引理（贪心最优性内核）：保留态 s 比逐出态 s' 轻 ⟹
   交换不增尾部质量（；组装：三辅件） *)
Theorem ag_top_k_exchange :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s s' : S),
    k s -> Not (k s') ->
    le (boltzmann_factor_r s) (boltzmann_factor_r s') ->
    le (plus (req_minus (tail_mass_of_r k kd) (boltzmann_factor_r s'))
             (boltzmann_factor_r s))
       (tail_mass_of_r k kd).
Proof.
  intros k kd s s' Hks Hnks' Hff.
  assert (Hr : req (plus (req_minus (tail_mass_of_r k kd) (boltzmann_factor_r s'))
                         (boltzmann_factor_r s))
                   (plus (tail_mass_of_r k kd)
                         (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s'))))
    by exact (ag_minus_plus_swap (tail_mass_of_r k kd)
                (boltzmann_factor_r s') (boltzmann_factor_r s)).
  assert (Hmm : le (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s')) zero)
    by exact (ag_le_minus_le_zero _ _ Hff).
  assert (Hfin : le (plus (tail_mass_of_r k kd)
                          (req_minus (boltzmann_factor_r s) (boltzmann_factor_r s')))
                    (tail_mass_of_r k kd))
    by exact (ag_le_plus_zero_l _ _ Hmm).
  exact (le_id_l _ _ _ Hr Hfin).
Qed.

(* 尾部逐点反单调：k1 ⊆ k2 ⟹（k2 尾项）≤（k1 尾项）（） *)
Lemma ag_eviction_tail_pointwise_le :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    forall s : S,
      le (if kd2 s then zero else boltzmann_factor_r s)
         (if kd1 s then zero else boltzmann_factor_r s).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd2 s) as [H2 | Hn2].
  - destruct (kd1 s) as [H1 | Hn1].
    + apply le_refl.
    + apply (lt_le_iff zero (boltzmann_factor_r s)).
      left. unfold boltzmann_factor_r. apply exp_neg_pos.
  - destruct (kd1 s) as [H1 | Hn1].
    + exact (match Hn2 (Hsub s H1) with end).
    + apply le_refl.
Qed.

(* 尾部质量反单调：保留扩张 ⟹ 损失不增（；与
   ag_eviction_partition_monotone 对偶；组装：sum_le） *)
Theorem ag_top_k_tail_antitone :
  forall (k1 k2 : S -> Set) (Hsub : forall s : S, k1 s -> k2 s)
         (kd1 : forall s : S, Or (k1 s) (Not (k1 s)))
         (kd2 : forall s : S, Or (k2 s) (Not (k2 s))),
    le (tail_mass_of_r k2 kd2) (tail_mass_of_r k1 kd1).
Proof.
  intros k1 k2 Hsub kd1 kd2. unfold tail_mass_of_r.
  apply (sum_le (fun s : S => if kd2 s then zero else boltzmann_factor_r s)
                (fun s : S => if kd1 s then zero else boltzmann_factor_r s)).
  intro s. exact (ag_eviction_tail_pointwise_le k1 k2 Hsub kd1 kd2 s).
Qed.

(* ---- kept 家正性/守恒（-30363 req 化） ---- *)

(* 单参 boltzmann 因子正性（；平凡直引 exp_neg_pos） *)
Lemma ag_boltzmann_factor_pos_attn : forall s : S, lt zero (boltzmann_factor_r s).
Proof.
  intro s. unfold boltzmann_factor_r. apply exp_neg_pos.
Qed.

(* if 保留项非负（） *)
Lemma ag_kept_term_nonneg :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    le zero (if kd s then boltzmann_factor_r s else zero).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply (lt_le_iff _ _). left. apply ag_boltzmann_factor_pos_attn.
  - apply le_refl.
Qed.

(* if 保留项 ≤ 因子（） *)
Lemma ag_kept_term_le_factor :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    le (if kd s then boltzmann_factor_r s else zero) (boltzmann_factor_r s).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply le_refl.
  - apply (lt_le_iff _ _). left. apply ag_boltzmann_factor_pos_attn.
Qed.

(* inv 反序：kept ≤ Z ⟹ 1/Z ≤ 1/kept（；接口字段
   inv_pos_le_compat 直引 + ag_eviction_partition_le_full） *)
Theorem ag_inv_Z_le_inv_kept :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    le (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos).
Proof.
  intros k kd Hkpos.
  apply (inv_pos_le_compat (evicted_partition_of_r k kd) Z_thermo_r
             Hkpos Z_thermo_r_pos).
  exact (ag_eviction_partition_le_full k kd).
Qed.

(* ============================================================ *)
(* 【中后段增量·Top-K 截断 TV 精确恒等链】（-30638）      *)
(*   链路（Id 同构）：守恒 → kept ≤ Z → inv 反序 → 符号分支       *)
(*   （abs 消去）→ 逐点差分解 → 求和分解 → 归一化代数完成。        *)
(*   诚实桥（条件定理模式 + ReqStrictOrderBridge 同位）：     *)
(*     req_lt_plus_compat_lt_le_h——req 集合oid接口仅双严格/双非   *)
(*     严格 plus 兼容字段，混合形不可导（构造性序无两侧消去），    *)
(*     Real 实例可满足；lt_minus_cc 符号步依存。                  *)
(*   主定理：ag_topk_tv_identity_strict（规划书 L42 点态结论件）。   *)
(* ============================================================ *)

(* 混合 plus 兼容桥（ReqStrictOrderBridge L1468 同位假设） *)
Hypothesis req_lt_plus_compat_lt_le_h :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).

(* Top-K 版保留配分与重归一化分布（/@30300 参数化副本） *)
Definition topk_renorm_r (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
           (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S) : R :=
  if kd s then
    mult (inv_pos (evicted_partition_of_r k kd) Hkpos) (boltzmann_factor_r s)
  else zero.

(* 总变差（req 节内副本；Id tv_dist @28785 同形，1/2 因子） *)
Definition tv_dist_r (mu nu : S -> R) : R :=
  mult (inv_pos (plus one one) req_two_pos)
       (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).

(* ---- Id _cc 辅件五件 req 化（@30372-@30410） ---- *)

Lemma ag_inv_one_cc : req (inv_pos one one_pos) one.
Proof.
  apply (req_trans _ (mult (inv_pos one one_pos) one) _).
  - exact (req_sym _ _ (mult_one (inv_pos one one_pos))).
  - apply (req_trans (mult (inv_pos one one_pos) one)
                     (mult one (inv_pos one one_pos)) one).
    + exact (mult_comm (inv_pos one one_pos) one).
    + exact (inv_pos_correct one one_pos).
Qed.

Lemma ag_opp_zero_cc : req (opp zero) zero.
Proof.
  exact (req_add_cancel_l (opp zero) zero zero
           (req_trans (plus (opp zero) zero) (plus zero (opp zero))
                      (plus zero zero)
             (plus_comm (opp zero) zero)
             (req_trans (plus zero (opp zero)) zero (plus zero zero)
                        (plus_opp zero) (req_sym _ _ (plus_zero zero))))).
Qed.

Lemma ag_lt_minus_cc : forall a b : R, lt a b -> lt (req_minus a b) zero.
Proof.
  intros a b Hab. unfold req_minus.
  apply (lt_id_r (plus a (opp b)) (plus b (opp b)) zero (req_plus_opp_r b)).
  exact (req_lt_plus_compat_lt_le_h a b (opp b) (opp b) Hab (le_refl (opp b))).
Qed.

Lemma ag_abs_neg_cc : forall a : R, lt a zero -> req (abs a) (opp a).
Proof.
  intros a Ha.
  apply (req_trans (abs a) (abs (opp a)) (opp a)).
  - exact (req_sym _ _ (abs_opp a)).
  - apply abs_pos.
    apply (lt_id_l zero (opp zero) (opp a)
             (req_sym _ _ ag_opp_zero_cc) (opp_lt_compat a zero Ha)).
Qed.

Lemma ag_minus_zero_cc : forall x : R, req (req_minus x zero) x.
Proof.
  intro x. unfold req_minus.
  apply (req_trans (plus x (opp zero)) (plus x zero) x).
  - exact (req_plus_compat x x (opp zero) zero (req_refl x)
             (req_add_cancel_l (opp zero) zero zero
               (req_trans (plus (opp zero) zero) (plus zero (opp zero))
                          (plus zero zero)
                 (plus_comm (opp zero) zero)
                 (req_trans (plus zero (opp zero)) zero (plus zero zero)
                            (plus_opp zero) (req_sym _ _ (plus_zero zero)))))).
  - apply plus_zero.
Qed.

(* ---- 逐点差分解（/@30477/@30516） ---- *)

(* keep 分支：|b/Z − b/Z_keep| == b·(1/Z_keep − 1/Z)
   （前提 lt invZ invKeep——Id 同位严格前提；真证：
   req_mult_minus_distr_r 反向 + abs_mult + abs_pos + abs_neg） *)
Lemma ag_tv_pointwise_keep :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    k s ->
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                        (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (boltzmann_factor_r s))))
        (mult (boltzmann_factor_r s)
              (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                         (inv_pos Z_thermo_r Z_thermo_r_pos))).
Proof.
  intros k kd Hkpos s Hk Hst.
  assert (Hfac : req (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                                (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                      (boltzmann_factor_r s)))
                     (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos))
                           (boltzmann_factor_r s)))
    by exact (req_sym _ _ (req_mult_minus_distr_r (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)
                             (boltzmann_factor_r s))).
  assert (Habs : req (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (boltzmann_factor_r s)))
                     (mult (boltzmann_factor_r s)
                           (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
  { apply (req_trans (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (boltzmann_factor_r s)))
                     (mult (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                           (abs (boltzmann_factor_r s)))
                     (mult (boltzmann_factor_r s)
                           (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
    - exact (abs_mult _ _).
    - apply (req_trans (mult (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                             (abs (boltzmann_factor_r s)))
                       (mult (abs (boltzmann_factor_r s))
                             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos))))
                       (mult (boltzmann_factor_r s)
                             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (inv_pos (evicted_partition_of_r k kd) Hkpos))))).
      + exact (mult_comm _ _).
      + exact (req_mult_compat (abs (boltzmann_factor_r s)) (boltzmann_factor_r s)
                  (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                  (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                  (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                  (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                  (abs_pos (boltzmann_factor_r s) (ag_boltzmann_factor_pos_attn s))
                  (req_refl _)). }
  assert (Hsign : req (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))).
  { apply (req_trans
             (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
             (opp (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (inv_pos (evicted_partition_of_r k kd) Hkpos)))
             (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                        (inv_pos Z_thermo_r Z_thermo_r_pos))).
    - exact (ag_abs_neg_cc _ (ag_lt_minus_cc _ _ Hst)).
    - apply (req_trans (opp (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (inv_pos (evicted_partition_of_r k kd) Hkpos)))
                       (plus (opp (inv_pos Z_thermo_r Z_thermo_r_pos))
                             (inv_pos (evicted_partition_of_r k kd) Hkpos))
                       (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                  (inv_pos Z_thermo_r Z_thermo_r_pos))).
      + exact (req_opp_minus _ _).
      + exact (plus_comm (opp (inv_pos Z_thermo_r Z_thermo_r_pos))
                         (inv_pos (evicted_partition_of_r k kd) Hkpos)). }
  apply (req_trans
           (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                           (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (boltzmann_factor_r s))))
           (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (inv_pos (evicted_partition_of_r k kd) Hkpos))
                      (boltzmann_factor_r s)))
           (mult (boltzmann_factor_r s)
                 (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                            (inv_pos Z_thermo_r Z_thermo_r_pos)))).
  - apply (req_abs_compat _ _). exact Hfac.
  - apply (req_trans
             (abs (mult (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (inv_pos (evicted_partition_of_r k kd) Hkpos))
                        (boltzmann_factor_r s)))
             (mult (boltzmann_factor_r s)
                   (abs (req_minus (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (inv_pos (evicted_partition_of_r k kd) Hkpos))))
             (mult (boltzmann_factor_r s)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos)))).
    + exact Habs.
    + exact (req_mult_compat _ _ _ _ (req_refl _) Hsign).
Qed.

(* evict 分支：|b/Z − 0| == b/Z（） *)
Lemma ag_tv_pointwise_evict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    Not (k s) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)) zero))
        (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)).
Proof.
  intros k kd Hkpos s Hnk.
  assert (Hz : req (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)) zero)
                   (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)))
    by exact (ag_minus_zero_cc _).
  apply (req_trans _ _ _ (req_abs_compat _ _ Hz)).
  apply abs_pos.
  apply mult_positive.
  - apply (inv_pos_pos Z_thermo_r Z_thermo_r_pos).
  - apply ag_boltzmann_factor_pos_attn.
Qed.

(* 逐点总恒等（条件化；） *)
Lemma ag_tv_pointwise :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)) (s : S),
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                        (topk_renorm_r k kd Hkpos s)))
        (if kd s
         then mult (boltzmann_factor_r s)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos))
         else mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s)).
Proof.
  intros k kd Hkpos s Hst.
  unfold topk_renorm_r.
  destruct (kd s) as [Hk | Hnk].
  - exact (ag_tv_pointwise_keep k kd Hkpos s Hk Hst).
  - exact (ag_tv_pointwise_evict k kd Hkpos s Hnk).
Qed.

(* if 分解与 else 线性（/@30505） *)
Lemma ag_tv_if_split : forall (X Y : R) (k : S -> Set)
                              (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
  req (if kd s then X else Y)
      (plus (if kd s then X else zero) (if kd s then zero else Y)).
Proof.
  intros X Y k kd s. destruct (kd s) as [Hk | Hnk].
  - exact (req_sym _ _ (plus_zero X)).
  - exact (req_trans (Y) (plus Y zero) (plus zero Y)
             (req_sym _ _ (plus_zero Y)) (plus_comm Y zero)).
Qed.

Lemma ag_eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : R) (f : S -> R) (s : S),
    req (if kd s then zero else mult a (f s))
        (mult a (if kd s then zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - exact (req_sym _ _ (req_mult_zero_r a)).
  - apply req_refl.
Qed.

(* 求和分解：Σ(if keep then b·D else b/Z) == kept·D + invZ·tail
   （；组装：if 分解 + sum_add + if 线性双件 + sum_linear） *)
Theorem ag_tv_sum_decomp :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    req (sumf (fun s : S => if kd s
                            then mult (boltzmann_factor_r s)
                                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                            else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                      (boltzmann_factor_r s)))
        (plus (mult (evicted_partition_of_r k kd)
                    (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (inv_pos Z_thermo_r Z_thermo_r_pos)))
              (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
Proof.
  intros k kd Hkpos.
  assert (Hsplit : req (sumf (fun s : S => if kd s
                                           then mult (boltzmann_factor_r s)
                                                     (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                                           else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                     (boltzmann_factor_r s)))
                      (sumf (fun s : S => plus (if kd s
                                                then mult (boltzmann_factor_r s)
                                                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                else zero)
                                               (if kd s
                                                then zero
                                                else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                          (boltzmann_factor_r s))))).
  { apply (sum_ext
             (fun s : S => if kd s
                           then mult (boltzmann_factor_r s)
                                     (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                           else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (boltzmann_factor_r s))
             (fun s : S => plus (if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero)
                                (if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s)))).
    intro s. exact (ag_tv_if_split
                      (mult (boltzmann_factor_r s)
                            (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos)))
                      (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (boltzmann_factor_r s))
                      k kd s). }
  apply (req_trans _ _ _ Hsplit).
  apply (req_trans _ (plus (sumf (fun s : S => if kd s
                                                then mult (boltzmann_factor_r s)
                                                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                else zero))
                           (sumf (fun s : S => if kd s
                                               then zero
                                               else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                         (boltzmann_factor_r s)))) _).
  - exact (sum_add (fun s : S => if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero)
                   (fun s : S => if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s))).
  - apply (req_plus_compat
             (sumf (fun s : S => if kd s
                                 then mult (boltzmann_factor_r s)
                                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                      (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 else zero))
             (mult (evicted_partition_of_r k kd)
                   (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (inv_pos Z_thermo_r Z_thermo_r_pos)))
             (sumf (fun s : S => if kd s
                                 then zero
                                 else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (boltzmann_factor_r s)))
             (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
    + apply (req_trans (sumf (fun s : S => if kd s
                                            then mult (boltzmann_factor_r s)
                                                      (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                                            else zero))
                       (sumf (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                          (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                (if kd s then boltzmann_factor_r s else zero))) _).
      * apply (sum_ext
                 (fun s : S => if kd s
                               then mult (boltzmann_factor_r s)
                                         (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                    (inv_pos Z_thermo_r Z_thermo_r_pos))
                               else zero)
                 (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                                    (if kd s then boltzmann_factor_r s else zero))).
        -- intro s. destruct (kd s) as [Hk | Hnk].
           ++ exact (mult_comm (boltzmann_factor_r s)
                        (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                   (inv_pos Z_thermo_r Z_thermo_r_pos))).
           ++ exact (req_sym _ _ (req_mult_zero_r (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos) (inv_pos Z_thermo_r Z_thermo_r_pos)))).
      * apply (req_trans (sumf (fun s : S => mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                             (inv_pos Z_thermo_r Z_thermo_r_pos))
                                                  (if kd s then boltzmann_factor_r s else zero)))
                         (mult (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos))
                               (sumf (fun s : S => if kd s then boltzmann_factor_r s else zero)))
                         (mult (evicted_partition_of_r k kd)
                               (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))).
         -- exact (sum_linear (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos))
                    (fun s : S => if kd s then boltzmann_factor_r s else zero)).
         -- exact (mult_comm (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                        (inv_pos Z_thermo_r Z_thermo_r_pos))
                    (evicted_partition_of_r k kd)).
    + apply (req_trans (sumf (fun s : S => if kd s
                                            then zero
                                            else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                      (boltzmann_factor_r s)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
      * apply (req_trans (sumf (fun s : S => if kd s
                                             then zero
                                             else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                       (boltzmann_factor_r s)))
                         (sumf (fun s : S => mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                   (if kd s then zero else boltzmann_factor_r s)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (sumf (fun s : S => if kd s then zero else boltzmann_factor_r s)))).
        -- apply (sum_ext
                    (fun s : S => if kd s
                                  then zero
                                  else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (boltzmann_factor_r s))
                    (fun s : S => mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (if kd s then zero else boltzmann_factor_r s))).
           ++ intro s. exact (ag_eviction_if_linear_else k kd (inv_pos Z_thermo_r Z_thermo_r_pos)
                                boltzmann_factor_r s).
        -- exact (sum_linear (inv_pos Z_thermo_r Z_thermo_r_pos)
                   (fun s : S => if kd s then zero else boltzmann_factor_r s)).
      * apply req_refl.
Qed.

(* 完成代数：kept·D + invZ·tail == 2·(invZ·tail)（） *)
Theorem ag_tv_sum_collapse :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    req (plus (mult (evicted_partition_of_r k kd)
                    (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (inv_pos Z_thermo_r Z_thermo_r_pos)))
              (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
        (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd))).
Proof.
  intros k kd Hkpos.
  assert (Hk1 : req (mult (evicted_partition_of_r k kd)
                          (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos)))
                    (req_minus one (mult (evicted_partition_of_r k kd)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos)))).
  { apply (req_trans (mult (evicted_partition_of_r k kd)
                           (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus (mult (evicted_partition_of_r k kd)
                                      (inv_pos (evicted_partition_of_r k kd) Hkpos))
                                (mult (evicted_partition_of_r k kd)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus one (mult (evicted_partition_of_r k kd)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))).
    - exact (req_mult_minus_distr_l (evicted_partition_of_r k kd)
                (inv_pos (evicted_partition_of_r k kd) Hkpos)
                (inv_pos Z_thermo_r Z_thermo_r_pos)).
    - apply (reqd_minus_compat _ _ _ _).
      + apply (req_trans (mult (evicted_partition_of_r k kd)
                               (inv_pos (evicted_partition_of_r k kd) Hkpos))
                         (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                               (evicted_partition_of_r k kd))
                         one).
        * exact (mult_comm (evicted_partition_of_r k kd)
                    (inv_pos (evicted_partition_of_r k kd) Hkpos)).
        * apply (req_trans (mult (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                 (evicted_partition_of_r k kd))
                           (mult (evicted_partition_of_r k kd)
                                 (inv_pos (evicted_partition_of_r k kd) Hkpos))
                           one).
          -- exact (mult_comm (inv_pos (evicted_partition_of_r k kd) Hkpos)
                              (evicted_partition_of_r k kd)).
          -- exact (inv_pos_correct (evicted_partition_of_r k kd) Hkpos).
      + apply req_refl. }
  assert (Hk2 : req (plus (mult (evicted_partition_of_r k kd)
                                (inv_pos Z_thermo_r Z_thermo_r_pos))
                          (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                (tail_mass_of_r k kd)))
                    one).
  { apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (tail_mass_of_r k kd)))
                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                           (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                     one).
    - apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                   (inv_pos Z_thermo_r Z_thermo_r_pos))
                             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd)))
                       (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (evicted_partition_of_r k kd))
                             (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                   (tail_mass_of_r k kd)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
      + exact (req_plus_compat _ _ _ _
                  (mult_comm (evicted_partition_of_r k kd) (inv_pos Z_thermo_r Z_thermo_r_pos))
                  (req_refl _)).
      + apply (req_trans (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (evicted_partition_of_r k kd))
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd)))
                         (plus (mult (evicted_partition_of_r k kd)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos))
                               (mult (tail_mass_of_r k kd)
                                     (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
        * exact (req_plus_compat _ _ _ _
                    (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (evicted_partition_of_r k kd))
                    (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (tail_mass_of_r k kd))).
        * apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos))
                                 (mult (tail_mass_of_r k kd)
                                       (inv_pos Z_thermo_r Z_thermo_r_pos)))
                           (mult (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd))
                                 (inv_pos Z_thermo_r Z_thermo_r_pos))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                 (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))).
          -- exact (req_sym _ _ (req_mult_plus_distr_r (evicted_partition_of_r k kd)
                                  (tail_mass_of_r k kd) (inv_pos Z_thermo_r Z_thermo_r_pos))).
          -- exact (mult_comm (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd))
                              (inv_pos Z_thermo_r Z_thermo_r_pos)).
    - apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                             (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                       (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r) one).
      + apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (evicted_partition_of_r k kd) (tail_mass_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                               (plus (tail_mass_of_r k kd) (evicted_partition_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r)).
        * exact (req_mult_compat _ _ _ _ (req_refl _)
                    (plus_comm (evicted_partition_of_r k kd) (tail_mass_of_r k kd))).
        * exact (req_mult_compat _ _ _ _ (req_refl _)
                    (ag_tail_plus_kept_full k kd)).
      + apply (req_trans (mult (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r)
                         (mult Z_thermo_r (inv_pos Z_thermo_r Z_thermo_r_pos)) one).
        * exact (mult_comm (inv_pos Z_thermo_r Z_thermo_r_pos) Z_thermo_r).
        * exact (inv_pos_correct Z_thermo_r Z_thermo_r_pos). }
  assert (Hk3 : req (req_minus one (mult (evicted_partition_of_r k kd)
                                         (inv_pos Z_thermo_r Z_thermo_r_pos)))
                    (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
  { apply (req_trans (req_minus one (mult (evicted_partition_of_r k kd)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (req_minus (plus (mult (evicted_partition_of_r k kd)
                                            (inv_pos Z_thermo_r Z_thermo_r_pos))
                                      (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd)))
                                (mult (evicted_partition_of_r k kd)
                                      (inv_pos Z_thermo_r Z_thermo_r_pos)))
                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
    - exact (reqd_minus_compat _ _ _ _ (req_sym _ _ Hk2) (req_refl _)).
    - exact (req_minus_plus_cancel_r (mult (evicted_partition_of_r k kd)
                                           (inv_pos Z_thermo_r Z_thermo_r_pos))
                (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))). }
  apply (req_trans (plus (mult (evicted_partition_of_r k kd)
                               (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                          (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                   (plus (req_minus one (mult (evicted_partition_of_r k kd)
                                              (inv_pos Z_thermo_r Z_thermo_r_pos)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                   (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                              (tail_mass_of_r k kd)))).
  - exact (req_plus_compat _ _ _ _ Hk1 (req_refl _)).
  - apply (req_trans (plus (req_minus one (mult (evicted_partition_of_r k kd)
                                                (inv_pos Z_thermo_r Z_thermo_r_pos)))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                     (plus (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))
                           (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)))
                     (mult (plus one one) (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                (tail_mass_of_r k kd)))).
    + exact (req_plus_compat _ _ _ _ Hk3 (req_refl _)).
    + exact (req_sym _ _ (req_two_mult (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                             (tail_mass_of_r k kd)))).
Qed.

(* -1 主定理（主）：严格逐出 ⟹ TV(boltzmann, topk 重归一)
   == tail/Z_thermo（ 条件化精确恒等 req 副本） *)
Theorem ag_topk_tv_identity_strict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : lt zero (evicted_partition_of_r k kd)),
    lt (inv_pos Z_thermo_r Z_thermo_r_pos)
       (inv_pos (evicted_partition_of_r k kd) Hkpos) ->
    req (tv_dist_r boltzmann_dist_attn_r (topk_renorm_r k kd Hkpos))
        (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd)).
Proof.
  intros k kd Hkpos Hst.
  assert (Hpt : req (sumf (fun s : S =>
                       abs (req_minus (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (boltzmann_factor_r s))
                                      (topk_renorm_r k kd Hkpos s))))
                    (sumf (fun s : S => if kd s
                                        then mult (boltzmann_factor_r s)
                                                  (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                             (inv_pos Z_thermo_r Z_thermo_r_pos))
                                        else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                                  (boltzmann_factor_r s))))
    by exact (sum_ext _ _ (fun s : S => ag_tv_pointwise k kd Hkpos s Hst)).
  unfold tv_dist_r, boltzmann_dist_attn_r.
  apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                           (sumf (fun s : S =>
                              if kd s
                              then mult (boltzmann_factor_r s)
                                        (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                   (inv_pos Z_thermo_r Z_thermo_r_pos))
                              else mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                        (boltzmann_factor_r s)))) _).
  - exact (req_mult_compat _ _ _ _ (req_refl _) Hpt).
  - apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                             (plus (mult (evicted_partition_of_r k kd)
                                         (req_minus (inv_pos (evicted_partition_of_r k kd) Hkpos)
                                                    (inv_pos Z_thermo_r Z_thermo_r_pos)))
                                   (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                         (tail_mass_of_r k kd)))) _).
    + exact (req_mult_compat _ _ _ _ (req_refl _)
                (ag_tv_sum_decomp k kd Hkpos)).
    + apply (req_trans _ (mult (inv_pos (plus one one) req_two_pos)
                               (mult (plus one one)
                                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd)))) _).
      * exact (req_mult_compat _ _ _ _ (req_refl _)
                  (ag_tv_sum_collapse k kd Hkpos)).
      * apply (req_trans (mult (inv_pos (plus one one) req_two_pos)
                               (mult (plus one one)
                                     (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd))))
                         (mult (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd)))
                         (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
        -- exact (mult_assoc (inv_pos (plus one one) req_two_pos) (plus one one)
                    (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
        -- apply (req_trans (mult (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                        (tail_mass_of_r k kd)))
                            (mult one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd)))
                            (mult (inv_pos Z_thermo_r Z_thermo_r_pos) (tail_mass_of_r k kd))).
           ++ exact (req_mult_compat _ _ _ _
                       (req_trans (mult (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (mult (plus one one) (inv_pos (plus one one) req_two_pos))
                                  one
                                  (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
                                  (inv_pos_correct (plus one one) req_two_pos))
                       (req_refl _)).
           ++ apply (req_trans (mult one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                               (tail_mass_of_r k kd)))
                               (mult (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                           (tail_mass_of_r k kd)) one)
                               (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                     (tail_mass_of_r k kd))).
              ** exact (mult_comm one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                            (tail_mass_of_r k kd))).
              ** exact (mult_one (mult (inv_pos Z_thermo_r Z_thermo_r_pos)
                                       (tail_mass_of_r k kd))).
Qed.

(* ============================================================ *)
(*   ---------------------------------------------------------------- *)
(*   【A. 逐 eps 有界和机器（结论 1 机器缺口落地；三件真证）】        *)
(*   依存接口 min/r_max 逐 eps 字段场（基座 L40529-40539：            *)
(*   min_le_l / r_max_le_l / r_max_l_iff 全逐 eps 形）+ 节内          *)
(*   sum_le / sum_add / sum_ext 假设位；plain 形不可导（序无消去，    *)
(*   RestB Part4 metric_nonneg 同判），故机器为逐 eps 口径——          *)
(*   与接口原生形式同构（log_le_linear_eps 同款口径）。               *)
(*   【解冻对照（结论 1）】 证明体核读 = 纯代数              *)
(*   （softmax_temp_relative + exp_neg_le_decr + le_mult_compat_r）， *)
(*   确未建），但与该语句的可迁移性解耦。本节两者均结果：机器三件     *)
(*   （A 组）独立成件，平移件（B 组）按 Id 纯代数路径组装。           *)
(*   【B. gap 集中 + 零温极限（ / @28337 平移；真证/组装）】  *)
(*   约定换位登记表（沿首段 ag_softmax_temp_relative 同款）：           *)
(*   Id e^{+z/T} 约定前提 minus (z s_star) (z s) → req 原生           *)
(*   e^{-z/T}（Boltzmann）约定前提 req_minus (z s) (z s_star）        *)
(*   （gap 位 = loss 差正半轴），结论因子 exp_neg (invT·gamma)        *)
(*   两约定同形；softmax_temp → reqd_softmax_temp_param。             *)
(*   【C. 退火引擎（B 组系数泛化重放，供 D 组依存）】                 *)
(*   ag_softmax_temp_relative 系数泛化（T 位 → 自由系数 kappa，       *)
(*   reqd_softmax_scaled 族；节 T 件签名不含温度参数位，诚实重放非降级）。*)
(*   【D. T→0 逐 eps 完成（Id 注释语义 L28330-28335 构造性读法）】     *)
(*   ag_hard_attention_collapse_eps：任意 eps>0 存在逆温系数          *)
(*   kappa := (1/T)·2^N 使比值 ≤ eps（温度 1/κ → 0 对位 Id "T→0"）。   *)

(*   req_r_pow / req_r_pow_pos 闭包件 + exp_neg_geo_break 假设位      *)
(*   （UpReqCauchy r_arch_pow Variable 同位平移，B 类参数 T2①；        *)
(*   Real 实例可满足：2^N·d → ∞）。                                   *)
(*   【诚实边界注记（结论 2 精确化）】cauchy_complete/lim 字段虽然     *)
(*   已在接口（L40589-40596），但 lim u zero 形需 metric 范数兼容参数位   *)
(*   （metric_abs_norm / abs_nonneg_plain / lim_metric_approx /      *)
(*   le_all_eps_zero 四参数位组——全部以 Variable 位活在 UpReqCauchy 节内， *)
(*   接口无对应字段），即结论"链长"的精确落点；本节按接口原生逐 eps   *)
(*   形式结果同语义内容，四参数位组列为后续升级路径（不强造）。           *)
(* ============================================================ *)

(* ---- A. 逐 eps 有界和机器（三件真证） ---- *)

(* 上界：Σf ≤ Σ(r_max f g) + Σ(常值 eps)（sum_le 逐点 r_max_le_l +
   sum_add 移出 + le_id_l；真证） *)
Lemma ag_sum_le_r_max_eps :
  forall (f g : S -> R) (eps : R), lt zero eps ->
    le (sumf f)
       (plus (sumf (fun s : S => r_max (f s) (g s)))
             (sumf (fun _ : S => eps))).
Proof.
  intros f g eps Heps.
  apply (le_trans (sumf f)
                  (sumf (fun s : S => plus (r_max (f s) (g s)) eps))
                  (plus (sumf (fun s : S => r_max (f s) (g s)))
                        (sumf (fun _ : S => eps)))).
  - apply (sum_le f (fun s : S => plus (r_max (f s) (g s)) eps)).
    intro s. exact (r_max_le_l (f s) (g s) eps Heps).
  - apply (le_id_l
             (sumf (fun s : S => plus (r_max (f s) (g s)) eps))
             (plus (sumf (fun s : S => r_max (f s) (g s)))
                   (sumf (fun _ : S => eps)))
             (plus (sumf (fun s : S => r_max (f s) (g s)))
                   (sumf (fun _ : S => eps)))).
    + exact (sum_add (fun s : S => r_max (f s) (g s)) (fun _ : S => eps)).
    + apply le_refl.
Qed.

(* min 上界：Σ(min f g) ≤ Σf + Σ(常值 eps)（sum_le 逐点 min_le_l +
   sum_add 移出；真证） *)
Lemma ag_sum_min_le_eps :
  forall (f g : S -> R) (eps : R), lt zero eps ->
    le (sumf (fun s : S => min (f s) (g s)))
       (plus (sumf f) (sumf (fun _ : S => eps))).
Proof.
  intros f g eps Heps.
  apply (le_trans (sumf (fun s : S => min (f s) (g s)))
                  (sumf (fun s : S => plus (f s) eps))
                  (plus (sumf f) (sumf (fun _ : S => eps)))).
  - apply (sum_le (fun s : S => min (f s) (g s))
                  (fun s : S => plus (f s) eps)).
    intro s. exact (min_le_l (f s) (g s) eps Heps).
  - apply (le_id_l
             (sumf (fun s : S => plus (f s) eps))
             (plus (sumf f) (sumf (fun _ : S => eps)))
             (plus (sumf f) (sumf (fun _ : S => eps)))).
    + exact (sum_add f (fun _ : S => eps)).
    + apply le_refl.
Qed.

(* 完成：g 逐点 ≤ f ⟹ Σ(r_max f g) == Σf（r_max_l_iff 点态 + sum_ext；
   真证） *)
Lemma ag_sum_r_max_collapse :
  forall f g : S -> R, (forall s : S, le (g s) (f s)) ->
    req (sumf (fun s : S => r_max (f s) (g s))) (sumf f).
Proof.
  intros f g Hle. exact (sum_ext (fun s : S => r_max (f s) (g s)) f (fun s : S => r_max_l_iff (f s) (g s) (Hle s))).
Qed.

(* ---- B. gap 集中 + 零温极限（ / @28337 平移） ---- *)

(* gap 集中（；真证：ag_softmax_temp_relative + exp_neg_le_decr
   + req_le_mult_compat_r 组装；换位登记表见增量节头注 B 组） *)
Theorem ag_softmax_gap_concentration :
  forall (z : S -> R) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
      le (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
         (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
               (exp_neg (mult (inv_pos T T_pos) gamma))).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  apply (le_id_l
           (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
           (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                 (exp_neg (mult (inv_pos T T_pos)
                                (req_minus (z s) (z s_star)))))
           (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                 (exp_neg (mult (inv_pos T T_pos) gamma)))).
  - exact (ag_softmax_temp_relative z s s_star).
  - exact (req_le_mult_compat_r
             (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
             (exp_neg (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))))
             (exp_neg (mult (inv_pos T T_pos) gamma))
             (lt_le_iff zero
                (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                (inl (ag_softmax_temp_pos z s_star)))
             (exp_neg_le_decr
                (mult (inv_pos T T_pos) gamma)
                (mult (inv_pos T T_pos) (req_minus (z s) (z s_star)))
                Hgap)).
Qed.

(* 零温极限比值形式（；真证：ag_softmax_gap_concentration +
   inv 消去链（req_markov_temperature_zero_limit 同构重放）） *)
Theorem ag_temperature_zero_limit :
  forall (z : S -> R) (s_star : S) (gamma : R),
    lt zero gamma ->
    forall s : S,
      le (mult (inv_pos T T_pos) gamma)
         (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
      le (mult (reqd_softmax_temp_param S sumf sum_pos T T_pos z s)
               (inv_pos (reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star)
                        (ag_softmax_temp_pos z s_star)))
         (exp_neg (mult (inv_pos T T_pos) gamma)).
Proof.
  intros z s_star gamma Hgamma s Hgap.
  pose (A := reqd_softmax_temp_param S sumf sum_pos T T_pos z s).
  pose (B := reqd_softmax_temp_param S sumf sum_pos T T_pos z s_star).
  pose (HB := ag_softmax_temp_pos z s_star).
  pose (C := exp_neg (mult (inv_pos T T_pos) gamma)).
  assert (Hgc : le A (mult B C)).
  { exact (ag_softmax_gap_concentration z s_star gamma Hgamma s Hgap). }
  assert (Hinv : le zero (inv_pos B HB)).
  { apply (lt_le_iff zero (inv_pos B HB)). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B HB) A) (mult (inv_pos B HB) (mult B C)))
    by exact (req_le_mult_compat_r (inv_pos B HB) A (mult B C) Hinv Hgc).
  assert (Hsw : req (mult A (inv_pos B HB)) (mult (inv_pos B HB) A))
    by exact (mult_comm A (inv_pos B HB)).
  assert (Hlhs : le (mult A (inv_pos B HB)) (mult (inv_pos B HB) (mult B C)))
    by exact (le_id_l _ _ _ Hsw Hdiv).
  assert (Hrhs : req (mult (inv_pos B HB) (mult B C)) C).
  { exact (req_trans
             (mult (inv_pos B HB) (mult B C))
             (mult (mult (inv_pos B HB) B) C)
             C
             (mult_assoc (inv_pos B HB) B C)
             (req_trans
                (mult (mult (inv_pos B HB) B) C)
                (mult one C)
                C
                (req_mult_compat (mult (inv_pos B HB) B) one C C
                   (req_trans (mult (inv_pos B HB) B)
                              (mult B (inv_pos B HB))
                              one
                              (mult_comm (inv_pos B HB) B)
                              (inv_pos_correct B HB))
                   (req_refl C))
                (req_trans (mult one C) (mult C one) C
                   (mult_comm one C) (mult_one C)))). }
  assert (Hfin : le (mult A (inv_pos B HB)) C) by exact (le_id_r _ _ _ Hrhs Hlhs).
  unfold A, B, C in Hfin. exact Hfin.
Qed.

(* ---- C. 退火引擎（系数泛化重放；依存面 = D 组） ---- *)

(* scaled 族相对形：ag_softmax_temp_relative 系数泛化（T 位 → kappa；
   真） *)
Lemma ag_softmax_scaled_relative :
  forall (kappa : R) (z : S -> R) (s s' : S),
    req (reqd_softmax_scaled S sumf sum_pos kappa z s)
        (mult (reqd_softmax_scaled S sumf sum_pos kappa z s')
              (exp_neg (mult kappa (req_minus (z s) (z s'))))).
Proof.
  intros kappa z s s'.
  assert (Hzs : req (z s) (plus (z s') (req_minus (z s) (z s'))))
    by exact (req_sym _ _ (req_minus_plus_cancel (z s') (z s))).
  assert (Hf : req (exp_neg (mult kappa (z s)))
                   (mult (exp_neg (mult kappa (z s')))
                         (exp_neg (mult kappa (req_minus (z s) (z s')))))).
  { exact (req_trans
             (exp_neg (mult kappa (z s)))
             (exp_neg (plus (mult kappa (z s'))
                            (mult kappa (req_minus (z s) (z s')))))
             (mult (exp_neg (mult kappa (z s')))
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (exp_neg_req_compat_setoid
                (mult kappa (z s))
                (plus (mult kappa (z s'))
                      (mult kappa (req_minus (z s) (z s'))))
                (req_trans (mult kappa (z s))
                           (mult kappa (plus (z s') (req_minus (z s) (z s'))))
                           (plus (mult kappa (z s'))
                                 (mult kappa (req_minus (z s) (z s'))))
                           (req_mult_compat kappa kappa (z s)
                              (plus (z s') (req_minus (z s) (z s')))
                              (req_refl _) Hzs)
                           (distrib kappa (z s') (req_minus (z s) (z s')))))
             (exp_neg_plus (mult kappa (z s'))
                           (mult kappa (req_minus (z s) (z s'))))). }
  unfold reqd_softmax_scaled.
  pose (Pw := (fun s0 : S => exp_neg (mult kappa (z s0)))).
  pose (Wp := (sum_pos Pw (fun s0 : S => exp_neg_pos (mult kappa (z s0))))).
  pose (IV := (inv_pos (sumf Pw) Wp)).
  assert (Has : req (mult (exp_neg (mult kappa (z s))) IV)
                   (mult IV
                      (mult (exp_neg (mult kappa (z s')))
                            (exp_neg (mult kappa
                                           (req_minus (z s) (z s'))))))).
  { apply (req_trans _ (mult IV (exp_neg (mult kappa (z s)))) _).
    - exact (mult_comm (exp_neg (mult kappa (z s))) IV).
    - exact (req_mult_compat IV IV (exp_neg (mult kappa (z s)))
                (mult (exp_neg (mult kappa (z s')))
                      (exp_neg (mult kappa (req_minus (z s) (z s')))))
                (req_refl _) Hf). }
  assert (Har : req (mult IV
                       (mult (exp_neg (mult kappa (z s')))
                             (exp_neg (mult kappa (req_minus (z s) (z s'))))))
                   (mult (mult (exp_neg (mult kappa (z s'))) IV)
                         (exp_neg (mult kappa (req_minus (z s) (z s')))))).
  { exact (req_trans
             (mult IV
                (mult (exp_neg (mult kappa (z s')))
                      (exp_neg (mult kappa (req_minus (z s) (z s'))))))
             (mult (mult IV (exp_neg (mult kappa (z s'))))
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (mult (mult (exp_neg (mult kappa (z s'))) IV)
                   (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (mult_assoc IV (exp_neg (mult kappa (z s')))
                (exp_neg (mult kappa (req_minus (z s) (z s')))))
             (req_mult_compat (mult IV (exp_neg (mult kappa (z s'))))
                (mult (exp_neg (mult kappa (z s'))) IV)
                (exp_neg (mult kappa (req_minus (z s) (z s'))))
                (exp_neg (mult kappa (req_minus (z s) (z s'))))
                (mult_comm IV (exp_neg (mult kappa (z s'))))
                (req_refl _))). }
  apply (req_trans _ (mult IV
         (mult (exp_neg (mult kappa (z s')))
               (exp_neg (mult kappa (req_minus (z s) (z s')))))) _).
  - exact Has.
  - exact Har.
Qed.

(* scaled 族 gap 集中（B 组 ag_softmax_gap_concentration 的 kappa 泛化；
   真证同型） *)
Lemma ag_softmax_scaled_gap :
  forall (kappa : R) (z : S -> R) (s_star : S) (gamma : R) (s : S),
    le (mult kappa gamma) (mult kappa (req_minus (z s) (z s_star))) ->
    le (reqd_softmax_scaled S sumf sum_pos kappa z s)
       (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
             (exp_neg (mult kappa gamma))).
Proof.
  intros kappa z s_star gamma s Hgap.
  apply (le_id_l
           (reqd_softmax_scaled S sumf sum_pos kappa z s)
           (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                 (exp_neg (mult kappa (req_minus (z s) (z s_star)))))
           (mult (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                 (exp_neg (mult kappa gamma)))).
  - exact (ag_softmax_scaled_relative kappa z s s_star).
  - exact (req_le_mult_compat_r
             (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
             (exp_neg (mult kappa (req_minus (z s) (z s_star))))
             (exp_neg (mult kappa gamma))
             (lt_le_iff zero (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                        (inl (ag_softmax_scaled_pos kappa z s_star)))
             (exp_neg_le_decr (mult kappa gamma)
                              (mult kappa (req_minus (z s) (z s_star)))
                              Hgap)).
Qed.

(* scaled 族比值形式（B 组 ag_temperature_zero_limit 的 kappa 泛化；
   真证同型） *)
Lemma ag_softmax_scaled_ratio_limit :
  forall (kappa : R) (z : S -> R) (s_star : S) (gamma : R) (s : S),
    le (mult kappa gamma) (mult kappa (req_minus (z s) (z s_star))) ->
    le (mult (reqd_softmax_scaled S sumf sum_pos kappa z s)
             (inv_pos (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                      (ag_softmax_scaled_pos kappa z s_star)))
       (exp_neg (mult kappa gamma)).
Proof.
  intros kappa z s_star gamma s Hgap.
  pose (A := reqd_softmax_scaled S sumf sum_pos kappa z s).
  pose (B := reqd_softmax_scaled S sumf sum_pos kappa z s_star).
  pose (HB := ag_softmax_scaled_pos kappa z s_star).
  pose (C := exp_neg (mult kappa gamma)).
  assert (Hgc : le A (mult B C)).
  { exact (ag_softmax_scaled_gap kappa z s_star gamma s Hgap). }
  assert (Hinv : le zero (inv_pos B HB)).
  { apply (lt_le_iff zero (inv_pos B HB)). left. apply inv_pos_pos. }
  assert (Hdiv : le (mult (inv_pos B HB) A) (mult (inv_pos B HB) (mult B C)))
    by exact (req_le_mult_compat_r (inv_pos B HB) A (mult B C) Hinv Hgc).
  assert (Hsw : req (mult A (inv_pos B HB)) (mult (inv_pos B HB) A))
    by exact (mult_comm A (inv_pos B HB)).
  assert (Hlhs : le (mult A (inv_pos B HB)) (mult (inv_pos B HB) (mult B C)))
    by exact (le_id_l _ _ _ Hsw Hdiv).
  assert (Hrhs : req (mult (inv_pos B HB) (mult B C)) C).
  { exact (req_trans
             (mult (inv_pos B HB) (mult B C))
             (mult (mult (inv_pos B HB) B) C)
             C
             (mult_assoc (inv_pos B HB) B C)
             (req_trans
                (mult (mult (inv_pos B HB) B) C)
                (mult one C)
                C
                (req_mult_compat (mult (inv_pos B HB) B) one C C
                   (req_trans (mult (inv_pos B HB) B)
                              (mult B (inv_pos B HB))
                              one
                              (mult_comm (inv_pos B HB) B)
                              (inv_pos_correct B HB))
                   (req_refl C))
                (req_trans (mult one C) (mult C one) C
                   (mult_comm one C) (mult_one C)))). }
  assert (Hfin : le (mult A (inv_pos B HB)) C) by exact (le_id_r _ _ _ Hrhs Hlhs).
  unfold A, B, C in Hfin. exact Hfin.
Qed.

(* ---- D. T→0 逐 eps 完成（lim 簇依存 + 假设位平移） ---- *)

(* 逐 eps 几何击穿参数位（UpReqCauchy r_arch_pow Variable 同位平移，B 类参数
   T2①；exp 形：exp_neg (2^N·d) ≤ eps。Real 实例可满足：2^N·d → ∞。
   End 时作显式参入闭包签名，Print Assumptions 仍 Closed） *)
Hypothesis exp_neg_geo_break :
  forall d : R, lt zero d ->
    forall eps : R, lt zero eps ->
      sigT (fun N : nat =>
        le (exp_neg (mult (req_r_pow (plus one one) N) d)) eps).

(* T→0 语义完成：任意 eps>0 存在逆温系数 kappa := (1/T)·2^N 使
   softmax 比值 ≤ eps（温度 1/κ → 0 对位 Id "T→0" 读法，即硬注意力坍缩
   的构造性逐 eps 形；依存 exp_neg_geo_break 参数位 + UpReqCauchy
   req_r_pow/req_r_pow_pos/req_mult_swap_mid + C 组三件） *)
Theorem ag_hard_attention_collapse_eps :
  forall (z : S -> R) (s_star : S) (gamma : R) (s : S),
    lt zero gamma ->
    le (mult (inv_pos T T_pos) gamma)
       (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))) ->
    forall eps : R, lt zero eps ->
    sigT (fun kappa : R =>
      le (mult (reqd_softmax_scaled S sumf sum_pos kappa z s)
               (inv_pos (reqd_softmax_scaled S sumf sum_pos kappa z s_star)
                        (ag_softmax_scaled_pos kappa z s_star)))
          eps).
Proof.
  intros z s_star gamma s Hgamma Hgap eps Heps.
  destruct (exp_neg_geo_break (mult (inv_pos T T_pos) gamma)
             (mult_positive (inv_pos T T_pos) gamma (inv_pos_pos T T_pos) Hgamma)
             eps Heps)
    as [N HN].
  exists (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)).
  (* kappa·x == 2^N·(invT·x)（系数换位，req_mult_swap_mid + mult_comm） *)
  assert (Hkap : forall x : R,
           req (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) x)
               (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) x))).
  { intro x.
    exact (req_trans
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) x)
             (mult (mult (inv_pos T T_pos) x) (req_r_pow (plus one one) N))
             (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) x))
             (req_mult_swap_mid (inv_pos T T_pos)
                                (req_r_pow (plus one one) N) x)
             (mult_comm (mult (inv_pos T T_pos) x)
                        (req_r_pow (plus one one) N))). }
  (* gap 系数换算：kappa·gamma ≤ kappa·(z s − z s_star)（Hgap 乘 2^N） *)
  assert (Hscale : le (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N)) gamma)
                      (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N))
                            (req_minus (z s) (z s_star)))).
  { apply (le_id_l
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) gamma)
             (mult (req_r_pow (plus one one) N) (mult (inv_pos T T_pos) gamma))
             (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                   (req_minus (z s) (z s_star)))
             (Hkap gamma)
             (le_id_r
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) gamma))
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) (req_minus (z s) (z s_star))))
                (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                      (req_minus (z s) (z s_star)))
                (req_sym _ _
                   (Hkap (req_minus (z s) (z s_star))))
                (req_le_mult_compat_r (req_r_pow (plus one one) N)
                   (mult (inv_pos T T_pos) gamma)
                   (mult (inv_pos T T_pos) (req_minus (z s) (z s_star)))
                   (lt_le_iff zero (req_r_pow (plus one one) N)
                      (inl (req_r_pow_pos (plus one one) N req_two_pos)))
                   Hgap))). }
  apply (le_trans
           (mult (reqd_softmax_scaled S sumf sum_pos
                    (mult (inv_pos T T_pos) (req_r_pow (plus one one) N)) z s)
                 (inv_pos
                    (reqd_softmax_scaled S sumf sum_pos
                       (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                       z s_star)
                    (ag_softmax_scaled_pos
                       (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                       z s_star)))
           (exp_neg (mult (mult (inv_pos T T_pos)
                                (req_r_pow (plus one one) N)) gamma))
           eps).
  - exact (ag_softmax_scaled_ratio_limit
             (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
             z s_star gamma s Hscale).
  - exact (le_id_l
             (exp_neg (mult (mult (inv_pos T T_pos)
                                  (req_r_pow (plus one one) N)) gamma))
             (exp_neg (mult (req_r_pow (plus one one) N)
                            (mult (inv_pos T T_pos) gamma)))
             eps
             (exp_neg_req_compat_setoid
                (mult (mult (inv_pos T T_pos) (req_r_pow (plus one one) N))
                      gamma)
                (mult (req_r_pow (plus one one) N)
                      (mult (inv_pos T T_pos) gamma))
                (Hkap gamma))
             HN).
Qed.

(* ============================================================ *)


(*   Id 原件摘录：                                        *)
(*   行3 @28494 Definition partition_function_temp_param (T0 : R)   *)
(*     (HT0 : lt zero T0) (z : logits) := sum_over_S (fun s =>      *)
(*     exp_pos_fn (mult (inv_pos T0 HT0) (z s)))；                  *)
(*      @28500 Lemma partition_function_temp_param_pos :            *)
(*     forall T0 HT0 z, lt zero (partition_function_temp_param      *)
(*     T0 HT0 z)（证：sum_pos_preserved + exp_neg_pos）。            *)
(*   行2 @29573 Theorem eviction_db_zero_full : (forall s, keep s)  *)
(*     -> Id evicted_partition Z_thermo -> forall s s' : S,         *)
(*     Id (db_breaking s s') zero（证：eviction_boltzmann_full +    *)
(*     eviction_transition_full + detailed_balance @28714 节        *)
(*     Variable + minus_self_zero + abs_zero）。                    *)
(*   Id→req 差异登记表（真证非抄写，沿 63 件先例同款）：               *)
(*     - sum_over_S→sumf（节内三性质诚实接口）+ sum_pos_preserved→   *)
(*       sum_pos 参数位；exp_pos_fn→exp_pos_fn_setoid（req 副本）；      *)
(*     - minus→req_minus（UpReqAlgebra L728 req_minus_self_zero），  *)
(*       Id 恒等链→req_trans 链 + req_mult_compat 双肢；             *)
(*     - detailed_balance（Id 节 Variable）→detailed_balance_r       *)
(*       诚实假设申报位逐位副本（Id→req）；                        *)
(*     - abs 消去：接口字段 abs_zero（req (abs zero) zero）经        *)
(*       req_abs_compat 拉回，零新公理。                             *)
(*     行1（@29385）异形维持冻结；行2（@29573）解冻结果。            *)
(* ============================================================ *)

(* ---- 行3：温度参数化配分函数（ 副本） ---- *)
Definition partition_function_temp_param_r (T0 : R) (HT0 : lt zero T0)
  (z : S -> R) : R :=
  sumf (fun s : S => exp_pos_fn_setoid (mult (inv_pos T0 HT0) (z s))).

(* ---- 行3 对位件（；真证：sum_pos 参数位 + exp_neg_pos，
   与首段 ag_partition_function_temp_pos 同款证法） ---- *)
Lemma ag_partition_function_temp_param_pos :
  forall (T0 : R) (HT0 : lt zero T0) (z : S -> R),
    lt zero (partition_function_temp_param_r T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold partition_function_temp_param_r.
  apply sum_pos.
  intro s. exact (exp_neg_pos (opp (mult (inv_pos T0 HT0) (z s)))).
Qed.

(* ---- detailed_balance 诚实接口位（ 节 Variable req 逐位
   副本；boltzmann_dist_attn→boltzmann_dist_attn_r，Id→req） ---- *)
Hypothesis detailed_balance_r :
  forall s s' : S,
    req (mult (boltzmann_dist_attn_r s) (transition s s'))
        (mult (boltzmann_dist_attn_r s') (transition s' s)).

(* ---- 行2 对位件（；全保留 ⟹ 破缺归零——逐出是破缺唯一
   来源。组装真证：ag_eviction_boltzmann_full（@29555 对位）+
   ag_eviction_transition_full（@29540 对位）+ detailed_balance_r +
   req_minus_self_zero + req_abs_compat/abs_zero——零新公理） ---- *)
Theorem ag_eviction_db_zero_full :
  (forall s : S, keep s) ->
  req evicted_partition_r Z_thermo_r ->
  forall s s' : S, req (db_breaking_r s s') zero.
Proof.
  intros Hkall HZ s s'.
  unfold db_breaking_r.
  assert (Heb : forall t : S, req (evicted_boltzmann_r t) (boltzmann_dist_attn_r t))
    by exact (ag_eviction_boltzmann_full Hkall HZ).
  assert (Het : forall t u : S, req (evicted_transition_r t u) (transition t u))
    by exact (ag_eviction_transition_full Hkall).
  assert (Harg : req (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                                (mult (evicted_boltzmann_r s') (evicted_transition_r s' s)))
                     zero).
  { apply (req_minus_self_zero
             (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
             (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
    apply (req_trans
             (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
             (mult (boltzmann_dist_attn_r s) (transition s s'))
             (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
    - exact (req_mult_compat (evicted_boltzmann_r s) (boltzmann_dist_attn_r s)
                (evicted_transition_r s s') (transition s s')
                (Heb s) (Het s s')).
    - apply (req_trans
               (mult (boltzmann_dist_attn_r s) (transition s s'))
               (mult (boltzmann_dist_attn_r s') (transition s' s))
               (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))).
      + exact (detailed_balance_r s s').
      + exact (req_sym _ _
                  (req_mult_compat (evicted_boltzmann_r s') (boltzmann_dist_attn_r s')
                    (evicted_transition_r s' s) (transition s' s)
                    (Heb s') (Het s' s))). }
  exact (req_trans
           (abs (req_minus (mult (evicted_boltzmann_r s) (evicted_transition_r s s'))
                           (mult (evicted_boltzmann_r s') (evicted_transition_r s' s))))
           (abs zero) zero
           (req_abs_compat _ _ Harg) abs_zero).
Qed.

End ReqAttnGibbs.

(* ---- 替换件承认面自查（文件尾） ---- *)
Print Assumptions ag_temp_is_scale_duality.
Print Assumptions ag_scale_sqrt_witness_dual.
Print Assumptions ag_half_scale_is_temp_two.
Print Assumptions ag_sq_witness_4.
Print Assumptions ag_opp_zero_cc.
Print Assumptions ag_minus_zero_cc.
