(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编尚待后续）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ToyR 玩具化··切片五：G08_Gibbs 五刀替换稿（ 记录件补位，）
   本稿为基准树 G08_Gibbs.v 同文替换：语句面/声明序/Require 面/其余正文逐字不动，
   仅换五处玩具证明体——① gibbsd_two_pos ② hzlogd_discharge_real
   ③ hzlogd_proj_min_kl_hlogzfree ④ hzlogd_proj_min_kl_bool ⑤ gibbe2_le_b_id_r。
   五刀均结构性换轨，本件逐条独立勘验、未照抄 结论（假设位正性族结论不适用于
   G08 其余条目；12 条中 7 条经勘验维持不可化标注，见记录切片五节）。
   刀① gibbsd_two_pos：原 real_plus_positive 一步直供；换轨 real_lt_plus_compat_
   lt_le（0<1 ∧ 0≤1 ⟹ 0+0<1+1，le 肢 inl 装载 real_lt_zero_one 严证人）＋
   real_eq_lt_lt 左端转移沿 sym(real_plus_zero 0) 退化零站（0=0+0），原引擎全退役。
   刀② hzlogd_discharge_real：原使用在file 保底件 hzlogd_log_le_zero_of_le_one；
   换轨抽象骨架 Real 层就地直拼：@le_id_r 中停站 log one ＋ log_one 换右端 ＋
   real_log_le_mono 单调肢，零借道保底件。
   刀③ hzlogd_proj_min_kl_hlogzfree：原 HlogZ 槽使用保底件；换轨槽内就地直拼
   同一站形，Z_aud≤one 尾肢内联进单调肢第 5 参，零借道保底件。
   刀④ hzlogd_proj_min_kl_bool：原 HlogZ 槽使用 hzlogd_discharge_real；换轨槽内
   Real 层就地直拼同 ③ 站形，单调肢 real_log_le_mono 直接代入，零借道 discharge 件。
   刀⑤ gibbe2_le_b_id_r：原 RealSetoid.real_lt_compat 四元等式兼容拼装；换轨
   real_lt_eq_lt 右端转移（中停站 b+eps，eq 肢 RealSetoid.real_eq_plus_compat 原样），
   等式转移引擎换轨且原 6 参拼装全退役。
   纪律：纯构造性；Set 层零 Prop 泄露；真 Qed；零新增 Require；零承认件；
   原件尾 11 处 Print Assumptions 逐字保留（编译证据 11/11 全 Closed）。 *)
(* G 组：G08_Gibbs — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpReqGibbsD + UpReqHlogZD + UpReqGibbsE2（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G08_Gibbs 成员件：UpReqGibbsD（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqGibbsD.v —— 假设位证明系列 #1：gibbs_inequality（UpReqDist.v）      *)
(*   Real 实例化证明件（主实现）                        *)
(* ------------------------------------------------------------------ *)
(* 引擎形状核对结论（普查 §380 落点纪律执行记录）：                      *)
(*   引擎 real_log_le_linear_B @UpRealLeB:535 输出 Bishop 形序          *)
(*   real_le_b := forall eps>0, x < y+eps（Set 值）；req 层槽            *)
(*   dist_log_le_linear @UpReqDist:1029 输出接口序 le——                 *)
(*   RealEnhancedReal 实例的 le 字段 := real_le（Or 编码）。            *)
(*   桥核对：real_le_to_le_b@UpRealLeB:78 / latb_real_lt_to_le_b@       *)
(*   G06_BForm:87 / real_lt_le_bridge@G01_CoreMicro:16 均单向           *)
(*   （real_le / real_lt → real_le_b）；逆向 real_le_b → real_le 即     *)
(*   Or 形精确闭合，构造性不可证（UpRealLeB 尾注登记表明示）。            *)
(*   判定：req 层槽不可由 B 形引擎无条件证明（序异向，缺逆向桥接引理）；    *)
(*   按普查 §380 纪律落点升格为「Real 实例化定理」——本文件以            *)
(*   real_le_b 为序复演 req_gibbs_pointwise → req_gibbs_inequality      *)
(*   使用链，参数位 dist_log_le_linear 由 real_log_le_linear_B 直接提供。     *)
(*   模板：UpReqU2 log_req_compat_real（ 模板 ②：显式实例直接提供）。     *)
(* ------------------------------------------------------------------ *)
(* 给出：                                                              *)
(*   [保底] gibbsd_gibbs_pointwise_B —— 逐点槽证明位：与                *)
(*     req_gibbs_pointwise 使用 dist_log_le_linear 逻辑同位，           *)
(*     real_log_le_linear_B 一次给定；                                  *)
(*     gibbsd_gibbs_inequality —— KL ≥ 0 Bishop 形（与 E.13             *)
(*     real_gibbs_inequality_B 语句同形；E.13 走 real_gibbs_inequality_ *)
(*     eps 闭合路，本件走 log 切线槽证明复演路——双路互证）。            *)
(*   [主件·级联首层] gibbsd_cross_entropy_decomp ——                    *)
(*     H(p,q) == S[p] + KL(p‖q) Real 实例化（req_cross_entropy_decomp   *)
(*     @UpReqDist:2431 对位），逐点恒等经 log 乘法分解向闭合，          *)
(*     同法使用本文件 Bishop 序机。                                     *)
(* 规范形注：全件采 real_kl_term 规范形 p·(−log(q/p))（CW_ConstructiveWorld_219            *)
(*   real_kl_term 同形）；req_relative_entropy 的 p·(log p−log q) 形    *)
(*   与之恒等需 log 逆消去（log(inv p) == −log p），CW_ConstructiveWorld_219 未备该消去件、 *)
(*   real_eq_of_zero_diff 逐 n ring 形不适用——诚实边界，req 面同构记    *)
(*   δ 透明（UpReqDist 登记表 2「minus 非接口字段」同判定）。             *)
(* 红线：Set 层零 Prop（real_le_b / real_eq / real_lt 全 Set 值，      *)
(*   语句与证明零 Prop 泄露）；全 Qed 闭合；零公理；既有文件零改；      *)
(*   gibbsd_ 前缀全库防同名冲突（建前 grep 实测零命中）。                     *)
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
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A：Bishop 序代数基元（real_le_b 上的 opp / 数乘 / 换形）        *)
(* ============================================================ *)

(* A1：lt 右端 −eps → +eps 平移（opp 反向件地基） *)
Lemma gibbsd_lt_add_opp_r : forall x y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus x (real_opp e)) y ->
  real_lt x (real_plus y e).
Proof.
  intros x y e Heps Hlt.
  apply (RealSetoid.real_lt_compat
           (real_plus e (real_plus x (real_opp e))) x
           (real_plus e y) (real_plus y e)).
  - apply real_eq_sym.
    apply (real_eq_trans x (real_plus x (real_plus (real_opp e) e))
                         (real_plus e (real_plus x (real_opp e)))).
    + apply (real_eq_trans x (real_plus x real_zero)
                           (real_plus x (real_plus (real_opp e) e))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat x real_zero x
                 (real_plus (real_opp e) e)).
        -- apply real_eq_refl.
        -- apply (real_eq_trans real_zero (real_plus e (real_opp e))
                     (real_plus (real_opp e) e)).
           ++ apply real_eq_sym. apply real_plus_opp.
           ++ apply real_plus_comm.
    + apply (real_eq_trans (real_plus x (real_plus (real_opp e) e))
                           (real_plus (real_plus x (real_opp e)) e)
                           (real_plus e (real_plus x (real_opp e)))).
      * apply real_plus_assoc.
      * apply real_plus_comm.
  - apply real_plus_comm.
  - exact (real_lt_plus_translate e (real_plus x (real_opp e)) y Hlt).
Qed.

(* A2：Bishop 序 opp 反向（req 层 opp_le_compat 的 le_b 对位） *)
Lemma gibbsd_le_b_opp : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply gibbsd_lt_add_opp_r.
  - exact Heps.
  - apply (RealSetoid.real_lt_compat
             (real_opp (real_plus b eps))
             (real_plus (real_opp b) (real_opp eps))
             (real_opp a) (real_opp a)).
    + exact (real_opp_plus b eps).
    + apply real_eq_refl.
    + exact (real_opp_lt_compat a (real_plus b eps) (H eps Heps)).
Qed.

(* A3：Bishop 序左端 real_eq 换形（req 层 le_id_l 的 le_b 对位） *)
Lemma gibbsd_le_b_id_l : forall a b c : Real,
  real_eq a b -> real_le_b b c -> real_le_b a c.
Proof.
  intros a b c Hab H eps Heps. unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat b a (real_plus c eps) (real_plus c eps)
           (real_eq_sym a b Hab) (real_eq_refl (real_plus c eps))
           (H eps Heps)).
Qed.

(* A5：minus 翻转恒等：−(a−b) == b−a（req 层 reqd_minus_one_flip 对位） *)
Lemma gibbsd_minus_flip : forall a b : Real,
  real_eq (real_opp (real_plus a (real_opp b)))
          (real_plus b (real_opp a)).
Proof.
  intros a b.
  apply (real_eq_trans (real_opp (real_plus a (real_opp b)))
                       (real_plus (real_opp a) (real_opp (real_opp b)))
                       (real_plus b (real_opp a))).
  - exact (real_opp_plus a (real_opp b)).
  - apply (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus (real_opp (real_opp b)) (real_opp a))
             (real_plus b (real_opp a))).
    + apply real_plus_comm.
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp (real_opp b)) (real_opp a)
               b (real_opp a)
               (real_opp_opp b) (real_eq_refl (real_opp a))).
Qed.

(* A4：Bishop 序右乘正数保序（req 层 req_le_mult_compat_r 的 le_b 对位） *)
Lemma gibbsd_le_b_mult_pos_r : forall c a b : Real,
  real_lt real_zero c -> real_le_b a b ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc H eps Heps. unfold real_le_b in H.
  set (e0 := real_mult eps (real_inv_pos c Hc)).
  assert (Hpos0 : real_lt real_zero e0).
  { exact (real_mult_positive eps (real_inv_pos c Hc) Heps
             (real_inv_pos_pos c Hc)). }
  apply (RealSetoid.real_lt_compat
           (real_mult c a) (real_mult c a)
           (real_mult c (real_plus b e0))
           (real_plus (real_mult c b) eps)).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_mult c (real_plus b e0))
             (real_plus (real_mult c b) (real_mult c e0))
             (real_plus (real_mult c b) eps)).
    + exact (real_distrib c b e0).
    + exact (RealSetoid.real_eq_plus_compat (real_mult c b) (real_mult c e0)
               (real_mult c b) eps
               (real_eq_refl (real_mult c b))
               (real_eq_trans
                  (real_mult c e0)
                  (real_mult eps (real_mult c (real_inv_pos c Hc))) eps
                  (real_eq_trans
                     (real_mult c e0)
                     (real_mult (real_mult eps c) (real_inv_pos c Hc))
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_eq_trans
                        (real_mult c e0)
                        (real_mult (real_mult c eps) (real_inv_pos c Hc))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc c eps (real_inv_pos c Hc))
                        (RealSetoid.real_eq_mult_compat
                           (real_mult c eps) (real_inv_pos c Hc)
                           (real_mult eps c) (real_inv_pos c Hc)
                           (real_mult_comm c eps)
                           (real_eq_refl (real_inv_pos c Hc))))
                     (real_eq_sym
                        (real_mult eps (real_mult c (real_inv_pos c Hc)))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc eps c (real_inv_pos c Hc))))
                  (real_eq_trans
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_mult eps real_one) eps
                     (RealSetoid.real_eq_mult_compat eps
                        (real_mult c (real_inv_pos c Hc)) eps real_one
                        (real_eq_refl eps) (real_inv_pos_correct c Hc))
                     (real_mult_one eps)))).
  - exact (real_mult_lt_compat_l a (real_plus b e0) c (H e0 Hpos0) Hc).
Qed.

(* ============================================================ *)
(* Part B：逐点槽证明前置（eq 层恒等）                                  *)
(* ============================================================ *)

(* B0：p·(q/p) == q（分式约分；结合 / 交换 / inv_correct 链） *)
Lemma gibbsd_p_mult_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_mult q (real_inv_pos p Hp)))
           (real_mult q (real_mult p (real_inv_pos p Hp))) q).
  - apply (real_eq_trans
             (real_mult p (real_mult q (real_inv_pos p Hp)))
             (real_mult (real_mult p q) (real_inv_pos p Hp))
             (real_mult q (real_mult p (real_inv_pos p Hp)))).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans
               (real_mult (real_mult p q) (real_inv_pos p Hp))
               (real_mult (real_mult q p) (real_inv_pos p Hp))
               (real_mult q (real_mult p (real_inv_pos p Hp)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q)
                 (real_inv_pos p Hp) (real_mult q p) (real_inv_pos p Hp)
                 (real_mult_comm p q) (real_eq_refl (real_inv_pos p Hp))).
      * apply real_eq_sym.
        exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans
             (real_mult q (real_mult p (real_inv_pos p Hp)))
             (real_mult q real_one) q).
    + apply (RealSetoid.real_eq_mult_compat q
               (real_mult p (real_inv_pos p Hp)) q real_one
               (real_eq_refl q) (real_inv_pos_correct p Hp)).
    + exact (real_mult_one q).
Qed.

(* B1：p·(1 − q/p) == p − q（req 层 reqd_p_minus_ratio 的 Real 对位） *)
Lemma gibbsd_p_minus_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_plus real_one
                         (real_opp (real_mult q (real_inv_pos p Hp)))))
          (real_plus p (real_opp q)).
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_plus real_one
                      (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus (real_mult p real_one)
                      (real_mult p (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus p (real_opp q))).
  - exact (real_distrib p real_one
             (real_opp (real_mult q (real_inv_pos p Hp)))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult p real_one)
             (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
             p (real_opp q)).
    + exact (real_mult_one p).
    + apply (real_eq_trans
               (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
               (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))
               (real_opp q)).
      * apply real_eq_sym.
        exact (real_opp_mult p (real_mult q (real_inv_pos p Hp))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_mult p (real_mult q (real_inv_pos p Hp))) q
                 (gibbsd_p_mult_ratio p q Hp)).
Qed.

(* ============================================================ *)
(* Part C：Bishop 和层机（real_list_sum 上的逐点→求和升格）             *)
(* ============================================================ *)

Lemma gibbsd_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_one)
           (real_eq_sym _ _ (real_plus_zero real_zero))
           (real_lt_plus_compat_lt_le real_zero real_one real_zero real_one
              real_lt_zero_one (inl real_lt_zero_one))).
Qed.

Definition gibbsd_half : Real :=
  real_inv_pos (real_plus real_one real_one) gibbsd_two_pos.

Lemma gibbsd_half_pos : real_lt real_zero gibbsd_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) gibbsd_two_pos).
Qed.

(* 半分配：e·h + e·h == e（eps 预算对半拆分的恒等燃料） *)
Lemma gibbsd_half_sum : forall e : Real,
  real_eq (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half)) e.
Proof.
  intro e.
  apply (real_eq_trans
           (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
           (real_mult e (real_plus gibbsd_half gibbsd_half)) e).
  - apply real_eq_sym.
    exact (real_distrib e gibbsd_half gibbsd_half).
  - apply (real_eq_trans
             (real_mult e (real_plus gibbsd_half gibbsd_half))
             (real_mult e real_one) e).
    + apply (RealSetoid.real_eq_mult_compat e
               (real_plus gibbsd_half gibbsd_half) e real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans (real_plus gibbsd_half gibbsd_half)
                 (real_mult (real_plus real_one real_one) gibbsd_half)
                 real_one).
        -- apply real_eq_sym.
           apply (real_eq_trans
                    (real_mult (real_plus real_one real_one) gibbsd_half)
                    (real_plus (real_mult real_one gibbsd_half)
                               (real_mult real_one gibbsd_half))
                    (real_plus gibbsd_half gibbsd_half)).
           ++ exact (real_eq_sym
                       (real_plus (real_mult real_one gibbsd_half)
                                  (real_mult real_one gibbsd_half))
                       (real_mult (real_plus real_one real_one) gibbsd_half)
                       (real_distrib_r_local real_one real_one gibbsd_half)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult real_one gibbsd_half)
                       (real_mult real_one gibbsd_half)
                       gibbsd_half gibbsd_half).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
        -- exact (real_inv_pos_correct (real_plus real_one real_one)
                    gibbsd_two_pos).
    + exact (real_mult_one e).
Qed.

(* C3：逐点 le_b ⟹ 求和 le_b（req 层 fsum_le 的 Bishop 对位；       *)
(*   预算对半归纳：eps 拆 e/2 + e/2，nil 余量走 real_lt_plus_r_zero） *)
Lemma gibbsd_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l Hpt.
  unfold real_le_b.
  induction l as [| w l IH].
  - intros eps Heps. simpl.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - intros eps Heps. simpl.
    assert (Hpos : real_lt real_zero (real_mult eps gibbsd_half)).
    { exact (real_mult_positive eps gibbsd_half Heps gibbsd_half_pos). }
    assert (Ha : real_lt (f w)
                   (real_plus (g w) (real_mult eps gibbsd_half))).
    { exact (Hpt w (real_mult eps gibbsd_half) Hpos). }
    assert (Ht : real_lt (real_list_sum X f l)
                   (real_plus (real_list_sum X g l)
                              (real_mult eps gibbsd_half))).
    { exact (IH (real_mult eps gibbsd_half) Hpos). }
    apply (RealSetoid.real_lt_compat
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                        (real_plus (real_list_sum X g l)
                                   (real_mult eps gibbsd_half)))
             (real_plus (real_plus (g w) (real_list_sum X g l)) eps)).
    + apply real_eq_refl.
    + exact (real_eq_trans
               (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                          (real_plus (real_list_sum X g l)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l))
                          (real_plus (real_mult eps gibbsd_half)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l)) eps)
               (real_plus_swap_mid (g w) (real_mult eps gibbsd_half)
                                   (real_list_sum X g l)
                                   (real_mult eps gibbsd_half))
               (RealSetoid.real_eq_plus_compat
                  (real_plus (g w) (real_list_sum X g l))
                  (real_plus (real_mult eps gibbsd_half)
                             (real_mult eps gibbsd_half))
                  (real_plus (g w) (real_list_sum X g l))
                  eps
                  (real_eq_refl (real_plus (g w) (real_list_sum X g l)))
                  (gibbsd_half_sum eps))).
    + exact (real_lt_plus_compat _ _ _ _ Ha Ht).
Qed.

(* C4：Σ(p−q) == Σp − Σq（req 层 fsum_minus 的 Real 对位） *)
Lemma gibbsd_list_sum_minus : forall (X : Type) (p q : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
          (real_plus (real_list_sum X p l)
                     (real_opp (real_list_sum X q l))).
Proof.
  intros X p q l.
  apply (real_eq_trans
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_plus (real_list_sum X p l)
                      (real_list_sum X (fun s => real_opp (q s)) l))
           (real_plus (real_list_sum X p l)
                      (real_opp (real_list_sum X q l)))).
  - exact (real_list_sum_add X p (fun s => real_opp (q s)) l).
  - apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
             (real_list_sum X (fun s => real_opp (q s)) l)
             (real_list_sum X p l)
             (real_opp (real_list_sum X q l))).
    + apply real_eq_refl.
    + exact (real_list_sum_opp X q l).
Qed.

(* ============================================================ *)
(* Part D：保底证明主体                                                 *)
(* ============================================================ *)

(* D0【槽证明位】：逐点 Gibbs 切线 p−q ≤_B p·(−log(q/p))。
   与 req_gibbs_pointwise（UpReqDist:2066）逻辑同位——该处使用
   Hypothesis dist_log_le_linear（槽，10 下游）；此处直接提供
   real_log_le_linear_B（UpRealLeB:535）一次闭合，无条件。
   链：槽 log(q/p) ≤_B q/p−1 → opp 反向 → 1−q/p 换形 →
   p 左乘保序 → p·(1−q/p)==p−q 换形闭合。 *)
Lemma gibbsd_gibbs_pointwise_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b (real_plus (p s) (real_opp (q s)))
            (real_kl_term (p s) (q s) Hps Hqs).
Proof.
  intros X p q s Hps Hqs.
  unfold real_kl_term, real_le_b. intros eps Heps.
  set (Rqp := real_mult (q s) (real_inv_pos (p s) Hps)).
  set (Hr := real_mult_positive (q s) (real_inv_pos (p s) Hps) Hqs
               (real_inv_pos_pos (p s) Hps)).
  (* —— 槽证明位：req 层 dist_log_le_linear 使用位，B 形引擎直接提供 —— *)
  assert (Hlin : real_le_b (real_log Rqp Hr)
                           (real_plus Rqp (real_opp real_one))).
  { exact (real_log_le_linear_B Rqp Hr). }
  assert (Hstep2 : real_le_b (real_plus real_one (real_opp Rqp))
                             (real_opp (real_log Rqp Hr))).
  { exact (gibbsd_le_b_id_l _ _ _
             (real_eq_sym _ _ (gibbsd_minus_flip Rqp real_one))
             (gibbsd_le_b_opp _ _ Hlin)). }
  assert (Hstep3 : real_le_b
                     (real_mult (p s)
                        (real_plus real_one (real_opp Rqp)))
                     (real_mult (p s) (real_opp (real_log Rqp Hr)))).
  { exact (gibbsd_le_b_mult_pos_r (p s) _ _ Hps Hstep2). }
  exact (gibbsd_le_b_id_l _ _ _
           (real_eq_sym _ _ (gibbsd_p_minus_ratio (p s) (q s) Hps))
           Hstep3 eps Heps).
Qed.

(* D1【保底主件】：Gibbs 不等式 Real 实例化——0 ≤_B Σ_s KL(p s‖q s)。
   req_gibbs_inequality（UpReqDist:2122，dist_log_le_linear 10 下游）
   的 Real 实例化证明：归一化前提位照抄 req 层（real_eq 形），求和层
   real_list_sum 机，序 real_le_b，参数位由 D0 逐点件填充。
   语句与 E.13 real_gibbs_inequality_B 同形：E.13 走
   real_gibbs_inequality_eps 闭合路，本件走 log 切线槽证明复演路——双路互证。 *)
Theorem gibbsd_gibbs_inequality :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  assert (Hle : real_le_b
                  (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                  (real_list_sum X
                     (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
  { apply gibbsd_list_sum_le_b.
    intro s. exact (gibbsd_gibbs_pointwise_B X p q s (Hp s) (Hq s)). }
  assert (Hz : real_eq
                 (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                 real_zero).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
             (real_plus (real_list_sum X p l)
                        (real_opp (real_list_sum X q l)))
             real_zero).
    - exact (gibbsd_list_sum_minus X p q l).
    - apply (real_eq_trans
               (real_plus (real_list_sum X p l)
                          (real_opp (real_list_sum X q l)))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
                 (real_opp (real_list_sum X q l)) real_one
                 (real_opp real_one)).
        * exact Hnormp.
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X q l) real_one
                   Hnormq).
      + exact (real_plus_opp real_one).
  }
  exact (gibbsd_le_b_id_l real_zero
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_list_sum X
              (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_eq_sym _ _ Hz) Hle).
Qed.

(* ============================================================ *)
(* Part E：主件——级联首层 cross_entropy_decomp 同法证明                 *)
(*   （req_cross_entropy_decomp @UpReqDist:2431 的 Real 实例化对位；    *)
(*     逐点恒等经 log 乘法分解向 q == p·(q/p) 闭合，零 log 逆消去）     *)
(* ============================================================ *)

Theorem gibbsd_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
       (real_list_sum X
          (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  apply (real_eq_trans
           (real_list_sum X
              (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
           (real_list_sum X
              (fun s : X => real_plus
                            (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                            (real_kl_term (p s) (q s) (Hp s) (Hq s))) l)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))).
  - apply real_list_sum_ext. intro s0.
    unfold real_kl_term.
    set (Rqp := real_mult (q s0) (real_inv_pos (p s0) (Hp s0))).
    set (Hr := real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0)) (Hq s0)
                 (real_inv_pos_pos (p s0) (Hp s0))).
    set (Hpm := real_mult_positive (p s0) Rqp (Hp s0) Hr).
    assert (Hlogsplit : real_eq (real_log (q s0) (Hq s0))
                          (real_plus (real_log (p s0) (Hp s0))
                                     (real_log Rqp Hr))).
    { apply (real_eq_trans (real_log (q s0) (Hq s0))
                           (real_log (real_mult (p s0) Rqp) Hpm)
                           (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr))).
      - exact (real_log_wd (q s0) (real_mult (p s0) Rqp) (Hq s0) Hpm
                  (real_eq_sym _ _
                     (gibbsd_p_mult_ratio (p s0) (q s0) (Hp s0)))).
      - exact (real_log_mult (p s0) Rqp (Hp s0) Hr).
    }
    apply (real_eq_trans
             (real_mult (p s0) (real_opp (real_log (q s0) (Hq s0))))
             (real_mult (p s0)
                (real_plus (real_opp (real_log (p s0) (Hp s0)))
                           (real_opp (real_log Rqp Hr))))
             (real_plus (real_mult (p s0) (real_opp (real_log (p s0) (Hp s0))))
                        (real_mult (p s0) (real_opp (real_log Rqp Hr))))).
    + apply (RealSetoid.real_eq_mult_compat (p s0)
               (real_opp (real_log (q s0) (Hq s0))) (p s0)
               (real_plus (real_opp (real_log (p s0) (Hp s0)))
                          (real_opp (real_log Rqp Hr)))).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_opp (real_log (q s0) (Hq s0)))
                 (real_opp (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr)))
                 (real_plus (real_opp (real_log (p s0) (Hp s0)))
                            (real_opp (real_log Rqp Hr)))).
        -- exact (RealSetoid.real_eq_opp_compat (real_log (q s0) (Hq s0))
                     (real_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr))
                     Hlogsplit).
        -- exact (real_opp_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr)).
    + exact (real_distrib (p s0) (real_opp (real_log (p s0) (Hp s0)))
               (real_opp (real_log Rqp Hr))).
  - exact (real_list_sum_add X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
             (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Qed.

(* ============================================================ *)
(* 核对（假设位证明系列 #1 结果清单）：                                     *)
(*   gibbsd_lt_add_opp_r / gibbsd_le_b_opp / gibbsd_le_b_id_l /         *)
(*   gibbsd_minus_flip / gibbsd_le_b_mult_pos_r —— Bishop 序代数 5 件    *)
(*   （req 层 opp_le_compat / le_id_l / req_le_mult_compat_r 的          *)
(*   real_le_b 对位，req 层无此形——B 形引擎直接提供的缺口件）。             *)
(*   gibbsd_p_mult_ratio / gibbsd_p_minus_ratio —— eq 恒等 2 件。       *)
(*   gibbsd_two_pos / gibbsd_half / gibbsd_half_pos / gibbsd_half_sum    *)
(*   + gibbsd_list_sum_le_b / gibbsd_list_sum_minus —— 和层机 6 件      *)
(*   （fsum_le / fsum_minus 的 Bishop 对位；预算对半归纳免除法）。      *)
(*   gibbsd_gibbs_pointwise_B —— 槽证明位（dist_log_le_linear 直接提供）。  *)
(*   gibbsd_gibbs_inequality —— 保底主件（四项关卡目标）。                  *)
(*   gibbsd_cross_entropy_decomp —— 级联首层主件。                      *)
(* 固化卡（索引回补行见技术报告）：                                     *)
(*   E-GIBBSD-1：B 形引擎证明 req 层 Hypothesis 槽，序异向不可直接提供——    *)
(*   落点纪律 §380 fallback（Real 实例化定理）首次全链执行；缺口件=      *)
(*   Bishop 序代数基元 5 件 + Bishop 和单调 1 件（本文件 Part A/C      *)
(*   可跨模块复用：log_le_linear/log_lt_mono 族槽证明同构缺口）。       *)
(*   E-GIBBSD-2：log 逆消去（log(inv p)==−log p）CW_ConstructiveWorld_219 未备——          *)
(*   kl_term 规范形绕行成立（log 乘法分解向 q == p·(q/p) 无需消去）；   *)
(*   req_relative_entropy 的 p·(log p−log q) 字面形桥接留待该消去件。   *)
(* ============================================================ *)

(* ======== G08_Gibbs 成员件：UpReqHlogZD（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqHlogZD.v — 假设位证明系列#4：HlogZ 槽构造性证明（KL 投影主定理）    *)
(*                                                              *)
(* 目标主定理：UpReqAlign.req_projected_distribution_minimizes_kl     *)
(*   （KL 投影 req 版，ReqKLProjection 节已闭；节后导出签名经        *)
(*     _hzlogd_probe.v Check 打表核实）。                           *)
(*                                                              *)
(* HlogZ 槽实测形（校注要点）：                                     *)
(*   le (log (Z_aud_req S sumf post_aud p) HZ) zero          *)
(*   ——是 log Z 的「上界形」（log Z ≤ 0），不是 lt zero (log Z)      *)
(*   下界形，也不是逐 eps 形。故证明路线勘定为：                     *)
(*   Z_aud ≤ sumf p（req_Z_aud_le_one，通过集质量 ≤ 总质量）          *)
(*     == one（Hp_norm 归一化）⟹ log Z_aud ≤ log one == 0            *)
(*     （log 单调 le 版直推；Id 侧总证明先例 = G01_CoreMicro.hlogz_*，      *)
(*       Real 层种子 = CW_ConstructiveWorld_219 real_log_le_mono/real_log_le_zero_of_le_one）。 *)
(*   原始任务表述草图「Z ≥ max p_i ⟹ log Z 下界」为下界槽路线，实测槽无     *)
(*   此形态：max 提取不入职；「逐点正性见证」在二态实例里由           *)
(*   hzlogd_HZ_bool 给出（HZ 槽一并证明），校注详见技术报告。         *)
(*                                                              *)
(* 结果清单（前缀 hzlogd_ 独占，编前 grep 复核 0 同名冲突）：             *)
(*   [保底] hzlogd_log_le_zero_of_le_one —— Z 正性+Z ≤ 1 ⟹ log Z ≤ 0  *)
(*           抽象证明（log 单调 le 槽显式位，Set 层零 Prop）；         *)
(*   [T2②]  hzlogd_discharge_real —— 抽象单调槽由 CW_ConstructiveWorld_219 种子          *)
(*           real_log_le_mono 直接提供的 Real 具体证明（无条件闭合）；      *)
(*           hzlogd_discharge_real_direct —— real_log_le_zero_of_le_one *)
(*           直用双形（双形并存，殊途同归）；                          *)
(*   [主件1] hzlogd_proj_min_kl_hlogzfree —— 主定理抽象 HlogZ-free      *)
(*           实例化：HlogZ 槽由保底件填充；诚实前提位移 = 新增          *)
(*           sum_le/Hp_norm（Z ≤ 1 路线的数学来源，主定理原签名不含）；   *)
(*   [主件2] hzlogd_proj_min_kl_bool —— 主定理 bool/Real 具体实例        *)
(*           （S := bool 二态审计，post_aud := id；HZ 槽由             *)
(*           hzlogd_HZ_bool 一并证明；仅余 p/q 分布前提，全 Set 层）。  *)
(*                                                              *)
(* 红线：零公理类禁词；全 Qed；Set 层语句（req/lt/le 全 Set 值；      *)
(* Hqz 的 post_aud s = false 槽与主定理同位继承）；既有文件零改；        *)
(* 双形并存。                                                *)
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
Require Import UpReqAlgebra.
Require Import UpReqAlign.
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
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_assoc := real_plus_assoc.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation distrib := real_distrib.
Notation le_id_l := RealSetoid.real_le_id_l.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation one_pos := real_lt_zero_one.
Notation le_plus_compat := real_le_plus_compat.
Notation opp_le_compat := real_opp_le_compat.
Notation log := real_log.
Notation log_one := real_log_one.

(* ============================================================ *)
(* 保底件：抽象证明（log 单调 le 槽显式位；四项关卡主链第 1 环）           *)
(*   论证：Z ≤ 1 ⟹ log Z ≤ log one（单调槽）⟹ log Z ≤ 0               *)
(*   （log_one 是接口字段：req (log one H) zero，经 le_id_r 换右端）。 *)
(* ============================================================ *)
Lemma hzlogd_log_le_zero_of_le_one :
  
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
       le x y -> le (log x Hx) (log y Hy)) ->
    forall (Z : R) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Hmono Z HZ HZ1.
  apply (le_id_r (log Z HZ) (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (Hmono Z one HZ one_pos HZ1).
Qed.

(* ============================================================ *)
(*  模板 ②：Real 具体证明（抽象单调槽由 CW_ConstructiveWorld_219 种子直接提供）             *)
(*   real_log_le_mono（CW_ConstructiveWorld_219 L112104 区，G01_CoreMicro 对偶）喂单参槽；    *)
(*   语句层 lt/le/log 经 RealEnhancedReal 实例 delta 等同 real_*。     *)
(* ============================================================ *)
Lemma hzlogd_discharge_real :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (le_id_r (log Z HZ) (log one one_pos) zero
           (log_one one_pos)
           (real_log_le_mono Z one HZ one_pos HZ1)).
Qed.

(* 双形并存：real_log_le_zero_of_le_one（G01_CoreMicro 直用形态）直取，      *)
(* 与上行殊途同归（同型语句双路互证，G01_CoreMicro 双给出先例）。             *)
Lemma hzlogd_discharge_real_direct :
  forall (Z : Real) (HZ : lt zero Z), le Z one -> le (log Z HZ) zero.
Proof.
  intros Z HZ HZ1.
  exact (real_log_le_zero_of_le_one Z HZ HZ1).
Qed.

(* ============================================================ *)
(* 主件 1：主定理抽象 HlogZ-free 实例化                                  *)
(*   主定理节后签名（检验打表）=  S sumf + sum_ext/add/linear +      *)
(*   log_req_compat + post_aud p Hp_pos HZ + q Hq Hqn Hqz + HlogZ。    *)
(*   本件：HlogZ 槽由保底件填充；新增 sum_le/Hp_norm 入口（Z ≤ 1        *)
(*   路线来源：req_Z_aud_le_one 要 sum_le，换右端要 Hp_norm）——         *)
(*   诚实前提位移，主定理原签名不含此二者。                              *)
(* ============================================================ *)
Lemma hzlogd_proj_min_kl_hlogzfree :
  forall  (S : Set)
         (sumf : (S -> R) -> R)
         (sum_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (sum_add : forall f g : S -> R,
            req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)))
         (sum_linear : forall (a : R) (f : S -> R),
            req (sumf (fun s => mult a (f s))) (mult a (sumf f)))
         (sum_le : forall f g : S -> R,
            (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g))
         (log_req_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            req x y -> req (log x Hx) (log y Hy))
         (post_aud : S -> bool) (p : S -> R)
         (Hp_norm : req (sumf p) one)
         (Hp_pos : forall s : S, lt zero (p s))
         (HZ : lt zero (Z_aud_req S sumf post_aud p))
         (Hmono : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
            le x y -> le (log x Hx) (log y Hy))
         (q : S -> R) (Hq : forall s : S, lt zero (q s))
         (Hqn : req (sumf q) one)
         (Hqz : forall s : S, post_aud s = false -> req (q s) zero),
    le (sumf (fun s =>
           kl_proj_closed S sumf post_aud p Hp_pos HZ q Hq s))
       (sumf (fun s =>
           mult (q s)
                (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros S sumf sum_ext sum_add sum_linear sum_le log_req_compat
         post_aud p Hp_norm Hp_pos HZ Hmono q Hq Hqn Hqz.
  apply (req_projected_distribution_minimizes_kl S sumf sum_ext sum_add
           sum_linear log_req_compat post_aud p Hp_pos HZ q Hq Hqn Hqz).
  (* HlogZ 槽就地直拼：@le_id_r 中停站 log one ＋ log_one 换右端 ＋ Hmono 单调肢，
     Z_aud≤one 尾肢内联进单调肢第 5 参（零借道保底件） *)
  apply (le_id_r (log (Z_aud_req S sumf post_aud p) HZ)
           (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (Hmono (Z_aud_req S sumf post_aud p) one HZ one_pos
             (le_id_r (Z_aud_req S sumf post_aud p) (sumf p) one
                Hp_norm
                (req_Z_aud_le_one S sumf sum_le post_aud p Hp_pos))).
Qed.

(* ============================================================ *)
(* 主件 2 地基：bool/Real 二态有限和（S := bool 二态审计实例）          *)
(*   sumf := plus (f true) (f false)；四条和前提 + log_req_compat      *)
(*   全部在本文件实证（Real 层闭合，零新假设）。                        *)
(* ============================================================ *)
Definition hzlogd_aud_sum (f : bool -> Real) : Real := plus (f true) (f false).

Lemma hzlogd_sum2_ext :
  forall f g : bool -> Real,
    (forall s : bool, req (f s) (g s)) ->
    req (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (req_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

Lemma hzlogd_sum2_add :
  forall f g : bool -> Real,
    req (hzlogd_aud_sum (fun s => plus (f s) (g s)))
        (plus (hzlogd_aud_sum f) (hzlogd_aud_sum g)).
Proof.
  intros f g. unfold hzlogd_aud_sum.
  apply (req_trans (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (f false)) (plus (g true) (g false)))).
  - (* 步1：(a+b)+(c+d) → a+(b+(c+d))（assoc 反向） *)
    apply (req_sym (plus (f true) (plus (g true) (plus (f false) (g false))))
                   (plus (plus (f true) (g true)) (plus (f false) (g false)))
                   (plus_assoc (f true) (g true) (plus (f false) (g false)))).
  - apply (req_trans (plus (f true) (plus (g true) (plus (f false) (g false))))
                     (plus (f true) (plus (plus (g true) (f false)) (g false)))
                     (plus (plus (f true) (f false)) (plus (g true) (g false)))).
    + (* 步2：b+(c+d) → (b+c)+d（assoc 正向） *)
      apply (req_plus_compat (f true) (f true)
               (plus (g true) (plus (f false) (g false)))
               (plus (plus (g true) (f false)) (g false))).
      * apply req_refl.
      * apply plus_assoc.
    + apply (req_trans (plus (f true) (plus (plus (g true) (f false)) (g false)))
                       (plus (f true) (plus (plus (f false) (g true)) (g false)))
                       (plus (plus (f true) (f false)) (plus (g true) (g false)))).
      * (* 步3：(b+c)+d → (c+b)+d（comm 中段交换） *)
        apply (req_plus_compat (f true) (f true)
                 (plus (plus (g true) (f false)) (g false))
                 (plus (plus (f false) (g true)) (g false))).
        -- apply req_refl.
        -- apply (req_plus_compat (plus (g true) (f false))
                     (plus (f false) (g true)) (g false) (g false)).
           ++ apply plus_comm.
           ++ apply req_refl.
      * apply (req_trans (plus (f true) (plus (plus (f false) (g true)) (g false)))
                         (plus (f true) (plus (f false) (plus (g true) (g false))))
                         (plus (plus (f true) (f false)) (plus (g true) (g false)))).
        -- (* 步4：(c+b)+d → c+(b+d)（assoc 反向） *)
           apply (req_plus_compat (f true) (f true)
                    (plus (plus (f false) (g true)) (g false))
                    (plus (f false) (plus (g true) (g false)))).
           ++ apply req_refl.
           ++ apply (req_sym (plus (f false) (plus (g true) (g false)))
                             (plus (plus (f false) (g true)) (g false))
                             (plus_assoc (f false) (g true) (g false))).
        -- (* 步5：a+(c+(b+d)) → (a+c)+(b+d)（assoc 正向闭合） *)
           apply plus_assoc.
Qed.

Lemma hzlogd_sum2_linear :
  forall (a : Real) (f : bool -> Real),
    req (hzlogd_aud_sum (fun s => mult a (f s))) (mult a (hzlogd_aud_sum f)).
Proof.
  intros a f. unfold hzlogd_aud_sum.
  apply (req_sym (mult a (plus (f true) (f false)))
                 (plus (mult a (f true)) (mult a (f false)))).
  apply distrib.
Qed.

Lemma hzlogd_sum2_le :
  forall f g : bool -> Real,
    (forall s : bool, le (f s) (g s)) ->
    le (hzlogd_aud_sum f) (hzlogd_aud_sum g).
Proof.
  intros f g H. unfold hzlogd_aud_sum.
  exact (le_plus_compat (f true) (g true) (f false) (g false)
           (H true) (H false)).
Qed.

(* log 兼容场实例（real_log_wd 直取；与 UpReqU2  ② 同位闭合件） *)
Lemma hzlogd_log_req_compat_real :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* HZ 槽证明（二态「逐点见证」给出件）：通过点 true 处 p 正 ⟹           *)
(* Z_aud = plus (p true) zero > 0（iota 归约 + plus_zero 运输）。        *)
(* 二态空间里 max 项 = 通过点本身，无需 max 选择算子。                   *)
(* ============================================================ *)
Lemma hzlogd_HZ_bool :
  forall p : bool -> Real,
    lt zero (p true) ->
    lt zero (Z_aud_req bool hzlogd_aud_sum
               (fun b : bool => b) p).
Proof.
  intros p Hp.
  apply (req_lt_compat zero zero (p true)
           (Z_aud_req bool hzlogd_aud_sum
              (fun b : bool => b) p)).
  - apply req_refl.
  - exact (req_sym (Z_aud_req bool hzlogd_aud_sum
                      (fun b : bool => b) p)
                   (p true)
                   (req_trans (Z_aud_req bool
                                 hzlogd_aud_sum (fun b : bool => b) p)
                              (plus (p true) zero) (p true)
                              (req_refl (Z_aud_req bool
                                           hzlogd_aud_sum
                                           (fun b : bool => b) p))
                              (plus_zero (p true)))).
  - exact Hp.
Qed.

(* ============================================================ *)
(* 主件 2：主定理 bool/Real 具体实例（HlogZ 槽由  ② 证明件填充）        *)
(*   post_aud := fun b => b（审计集 = {true}）；和四前提全实证；        *)
(*   HZ 槽由 hzlogd_HZ_bool 证明（语句内联，免 assert 不透明墙）；       *)
(*   HlogZ 槽由 hzlogd_discharge_real 证明（Z_aud ≤ one 走               *)
(*   req_Z_aud_le_one + Hp_norm 同一路线）；                            *)
(*   余下前提仅 p/q 分布形态（Set 层：real_eq/real_lt 载体）。           *)
(* ============================================================ *)
Theorem hzlogd_proj_min_kl_bool :
  forall (p : bool -> Real)
         (Hp_norm : req (hzlogd_aud_sum p) one)
         (Hp_pos : forall s : bool, lt zero (p s))
         (q : bool -> Real) (Hq : forall s : bool, lt zero (q s))
         (Hqn : req (hzlogd_aud_sum q) one)
         (Hqz : forall s : bool,
            (fun b : bool => b) s = false -> req (q s) zero),
    le (hzlogd_aud_sum (fun s =>
          kl_proj_closed bool hzlogd_aud_sum
              (fun b : bool => b) p Hp_pos
              (hzlogd_HZ_bool p (Hp_pos true)) q Hq s))
       (hzlogd_aud_sum (fun s =>
          mult (q s)
               (req_minus (log (q s) (Hq s)) (log (p s) (Hp_pos s))))).
Proof.
  intros p Hp_norm Hp_pos q Hq Hqn Hqz.
  apply (req_projected_distribution_minimizes_kl bool
           hzlogd_aud_sum hzlogd_sum2_ext hzlogd_sum2_add hzlogd_sum2_linear
           hzlogd_log_req_compat_real (fun b : bool => b) p Hp_pos
           (hzlogd_HZ_bool p (Hp_pos true)) q Hq Hqn Hqz).
  (* HlogZ 槽就地直拼：@le_id_r 中停站 log one ＋ log_one ＋ real_log_le_mono 单调肢，
     Z_aud≤one 尾肢内联进单调肢第 5 参（零借道 discharge 件） *)
  apply (le_id_r
           (log (Z_aud_req bool hzlogd_aud_sum
                  (fun b : bool => b) p)
               (hzlogd_HZ_bool p (Hp_pos true)))
           (log one one_pos) zero).
  - exact (log_one one_pos).
  - exact (real_log_le_mono
             (Z_aud_req bool hzlogd_aud_sum
                (fun b : bool => b) p)
             one (hzlogd_HZ_bool p (Hp_pos true)) one_pos
             (le_id_r
                 (Z_aud_req bool hzlogd_aud_sum
                    (fun b : bool => b) p)
                 (hzlogd_aud_sum p) one Hp_norm
                 (req_Z_aud_le_one bool hzlogd_aud_sum
                    hzlogd_sum2_le (fun b : bool => b) p Hp_pos))).
Qed.

(* ============================================================ *)
(* G3 关：提取检验 + Print Assumptions（新件闭合性核验）                *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upreqhlogzd_core.ml" hzlogd_log_le_zero_of_le_one
  hzlogd_proj_min_kl_hlogzfree.
Extraction "upreqhlogzd_real.ml" hzlogd_discharge_real
  hzlogd_discharge_real_direct hzlogd_HZ_bool hzlogd_proj_min_kl_bool.

Print Assumptions hzlogd_log_le_zero_of_le_one.
Print Assumptions hzlogd_discharge_real.
Print Assumptions hzlogd_discharge_real_direct.
Print Assumptions hzlogd_proj_min_kl_hlogzfree.
Print Assumptions hzlogd_HZ_bool.
Print Assumptions hzlogd_proj_min_kl_bool.

(* ============================================================ *)
(* 终验记录（编后核对回补）：                                          *)
(*   Qed 计数：11 = 保底1 + T2双形2 + 主件1 + 和地基4 + log兼容1 +      *)
(*   HZ证明1 + 主件2。                                                 *)
(*   G1 禁词 0；G2 EXIT=0；G3 提取双轨 core/real + PA 全 Closed；       *)
(*   G4 coqchk Modules were successfully checked。                     *)
(* ============================================================ *)

(* ======== G08_Gibbs 成员件：UpReqGibbsE2（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqGibbsE2.v —— 假设位证明系列 #2 重定位模块：gibbs_equality 有限具体路线      *)
(*   （上游版本 UpReqGibbsE.v 抽象 Or 形稿已阻塞判定，本文件零碰旧稿；              *)
(*     gibbe2_ 前缀全库防同名冲突，建前 grep 实测零命中。）                          *)
(* ------------------------------------------------------------------ *)
(* 侦察结论（实读判定）：                                          *)
(*   1. 逐项钳零可行：real_eq/real_lt 全 Set 值逐 eps 形（CW_ConstructiveWorld_219:3448/3517），  *)
(*      real_list_sum_pos（根内 L41660 区）背书「逐项正⟹和正」方向；           *)
(*      逆向「和零⟹逐项零」经 le_b 反对称（根内缺件）本文件自建闭合。            *)
(*   2. log 引擎：real_log_le_mono（G01_CoreMicro L24，lt 支 real_log_lt_mono      *)
(*      根内已证——严格单调在库）；log 单射/eq-linear 桥缺模块——CW_ConstructiveWorld_219 L41224      *)
(*      诚实边界明示「log_eq_linear 需强三分/LPO，构造性不可证」。实测定：      *)
(*      主件闭合确须该桥。                                                     *)
(*   3. 双切点互易推导否决：逐项钳零给出 log u_s == u_s − 1 各自成立，          *)
(*      但 u_1·u_2 == 1 互易关系对任意分布不成立（归一化不生互易），            *)
(*      有限具体载体亦不能绕开 eq-linear 桥——X 邻接判定升级为系列工作记录。         *)
(* ------------------------------------------------------------------ *)
(* 给出（分级）：                                                              *)
(*   [保底1·逐项钳零件族] gibbe2_le_b_antisym（核心新件，逐 n 构造，            *)
(*     零 Or 闭合、零 LPO、零三分）；gibbe2_clamp_head / _r；                   *)
(*     gibbe2_list_sum_zero_extract_bool（有限具体载体 [true;false] 提取）。    *)
(*   [保底2·log 关系件] gibbe2_kl_eq_of_w_zero + gibbe2_tangent_eq +           *)
(*     gibbe2_kl_zero_tangent_eq：KL==0 ⟹ 逐点切点等式                          *)
(*     log(q_s/p_s) == q_s/p_s − 1（Real 层无条件——全库首件）。                 *)
(*   [主件·桥注入形证明件] gibbe2_gibbs_equality_bool：KL==0 ⟹ 逐点切点等式     *)
(*     ⟹（eq-linear 桥显式注入）⟹ 逐点 p==q。桥无条件不可证（根内 L41224        *)
(*     判定；上游版本 exp 复制机属阻塞域本文件零碰），依兜底预案以显式前提证明——      *)
(*     req 层 dist_log_eq_linear（UpReqDist:1031 Hypothesis）的 Real 实例化     *)
(*     缺口如实呈报。                                                          *)
(* 红线：Set 层零 Prop（语句序/等全 Set 值 real_eq/real_lt/real_le_b；          *)
(*   零 Or 闭合、零三分、零 LPO）；全 Qed 闭合；零公理；既有文件零改；          *)
(*   旧 UpReqGibbsE.v 零碰（无 .vo，不可 Require，未使用）。            *)
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

From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qround
               Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============================================================ *)
(* Part A：Q 层半分 helper                                                     *)
(* ============================================================ *)

Lemma gibbe2_Q_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps * (1#2))%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps (1#2)).
  - apply QltT_to_Qlt. exact Heps.
  - reflexivity.
Qed.

Lemma gibbe2_Q_half_lt : forall eps : Q, QltT 0 eps -> QltT (eps * (1#2))%Q eps.
Proof.
  intros eps Heps.
  assert (H1 : Qlt ((1#2) * eps) (1 * eps)).
  { apply (Qmult_lt_compat_r (1#2) 1 eps).
    - apply QltT_to_Qlt. exact Heps.
    - reflexivity. }
  rewrite Qmult_1_l in H1.
  rewrite (Qmult_comm (1#2) eps) in H1.
  apply Qlt_to_QltT. exact H1.
Qed.

(* ============================================================ *)
(* Part B：le_b 补层序机                                                       *)
(* ============================================================ *)

(* B1：le_b 右端 eq 换形 *)
Lemma gibbe2_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hbc eps Heps. unfold real_le_b in H.
  exact (real_lt_eq_lt a (real_plus b eps) (real_plus c eps) (H eps Heps)
           (RealSetoid.real_eq_plus_compat b eps c eps Hbc (real_eq_refl eps))).
Qed.

(* B2：le_b 右加平移 *)
Lemma gibbe2_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus z x) (real_plus x z)
           (real_plus z (real_plus y eps)) (real_plus (real_plus y z) eps)).
  - apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z y) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus z y) eps
               (real_plus y z) eps
               (real_plus_comm z y) (real_eq_refl eps)).
  - exact (real_lt_plus_translate z x (real_plus y eps) (H eps Heps)).
Qed.

(* B3：le_b a b ⟹ le_b 0 (b−a) *)
Lemma gibbe2_le_b_nonneg_diff : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus (real_opp a) a)
           real_zero
           (real_plus (real_opp a) (real_plus b eps))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply (real_eq_trans _ (real_plus a (real_opp a)) _).
    + apply real_plus_comm.
    + exact (real_plus_opp a).
  - apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) b) eps
               (real_plus b (real_opp a)) eps
               (real_plus_comm (real_opp a) b) (real_eq_refl eps)).
  - exact (real_lt_plus_translate (real_opp a) a (real_plus b eps) (H eps Heps)).
Qed.

(* B4【核心新件】：le_b Bishop 序反对称（逐 n 构造，零 Or 闭合、零 LPO） *)
Lemma gibbe2_le_b_antisym : forall a b : Real,
  real_le_b a b -> real_le_b b a -> real_eq a b.
Proof.
  intros a b H1 H2 eps Heps.
  assert (He2pos : real_lt real_zero (real_const (eps * (1#2))%Q))
    by (apply real_const_pos; apply gibbe2_Q_half_pos; exact Heps).
  assert (Hhe : Qlt (eps * (1#2))%Q eps)
    by (apply QltT_to_Qlt; apply gibbe2_Q_half_lt; exact Heps).
  destruct (H1 _ He2pos) as [g1 [Hg1pos [N1 HN1]]].
  destruct (H2 _ He2pos) as [g2 [Hg2pos [N2 HN2]]].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  assert (Hp1 : forall k : nat,
           projT1 (real_plus b (real_const (eps * (1#2))%Q)) k
           == projT1 b k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hp2 : forall k : nat,
           projT1 (real_plus a (real_const (eps * (1#2))%Q)) k
           == projT1 a k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hcst : forall (c : Q) (k : nat), projT1 (real_const c) k == c)
    by (intros c k; apply qeqT_imp_qeq; apply real_const_proj).
  rewrite (Hp1 n) in HN1. rewrite (Hcst (eps * (1#2))%Q n) in HN1.
  rewrite (Hp2 n) in HN2. rewrite (Hcst (eps * (1#2))%Q n) in HN2.
  set (x := projT1 a n - projT1 b n).
  set (h := (eps * (1#2))%Q).
  assert (Hg1q : 0 < g1) by (apply QltT_to_Qlt; exact Hg1pos).
  assert (Hg2q : 0 < g2) by (apply QltT_to_Qlt; exact Hg2pos).
  (* Upper side: x < h where x is a n - b n (ring normalization plus lia). *)
  assert (Hstep1 : projT1 a n - projT1 b n + g1
                   < projT1 a n - projT1 b n
                     + (projT1 b n + eps * (1#2) - projT1 a n)).
  { exact (proj2 (Qplus_lt_r g1 (projT1 b n + eps * (1#2) - projT1 a n)
                   (projT1 a n - projT1 b n)) HN1). }
  assert (Hring1 : projT1 a n - projT1 b n
                   + (projT1 b n + eps * (1#2) - projT1 a n)
                   == eps * (1#2)) by ring.
  rewrite Hring1 in Hstep1.
  assert (Hub : projT1 a n - projT1 b n < eps * (1#2)).
  { apply (Qle_lt_trans _ (projT1 a n - projT1 b n + g1) _).
    - rewrite <- (Qplus_0_r (projT1 a n - projT1 b n)) at 1.
      apply (proj2 (Qplus_le_r 0 g1 (projT1 a n - projT1 b n))).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g1 Hg1pos)).
    - exact Hstep1. }
  (* Lower side: -x < h. *)
  assert (Hstep2 : - (projT1 a n - projT1 b n) + g2
                   < - (projT1 a n - projT1 b n)
                     + (projT1 a n + eps * (1#2) - projT1 b n)).
  { exact (proj2 (Qplus_lt_r g2 (projT1 a n + eps * (1#2) - projT1 b n)
                   (- (projT1 a n - projT1 b n))%Q) HN2). }
  assert (Hring2 : - (projT1 a n - projT1 b n)
                   + (projT1 a n + eps * (1#2) - projT1 b n)
                   == eps * (1#2)) by ring.
  rewrite Hring2 in Hstep2.
  assert (Hdn : (- (projT1 a n - projT1 b n))%Q < eps * (1#2)).
  { apply (Qle_lt_trans _ ((- (projT1 a n - projT1 b n))%Q + g2) _).
    - rewrite <- (Qplus_0_r (- (projT1 a n - projT1 b n))%Q) at 1.
      apply (proj2 (Qplus_le_r 0 g2 (- (projT1 a n - projT1 b n))%Q)).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g2 Hg2pos)).
    - exact Hstep2. }
  (* Final step: the absolute value of x is below eps (two sign cases, decidable over Q, no trichotomy). *)
  unfold x, h.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (projT1 a n - projT1 b n)) as [Hsx | Hsx].
  - rewrite (Qabs_pos (projT1 a n - projT1 b n) (Qlt_le_weak _ _ Hsx)).
    apply (Qlt_le_trans _ (eps * (1#2)) eps Hub).
    exact (Qlt_le_weak _ _ Hhe).
  - rewrite (Qabs_neg (projT1 a n - projT1 b n) Hsx).
    apply (Qlt_le_trans (- (projT1 a n - projT1 b n))%Q (eps * (1#2)) eps Hdn).
    exact (Qlt_le_weak _ _ Hhe).
Qed.

(* ============================================================ *)
(* Part C：保底1·逐项钳零件族                                                  *)
(* ============================================================ *)

(* C1：二项和零 ⟹ 首项零 *)
Lemma gibbe2_clamp_head : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero a.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_le_b_antisym real_zero a Ha).
  apply (gibbe2_le_b_id_r a (real_plus b a) real_zero).
  - apply (gibbsd_le_b_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_trans a (real_plus a real_zero) (real_plus real_zero a)
                (real_eq_sym _ _ (real_plus_zero a)) (real_plus_comm a real_zero))
             (gibbe2_le_b_translate_r real_zero b a Hb)).
  - apply (real_eq_trans (real_plus b a) (real_plus a b) real_zero
             (real_plus_comm b a) Hsum).
Qed.

(* C2：二项和零 ⟹ 次项零（comm 对偶） *)
Lemma gibbe2_clamp_head_r : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero b.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_clamp_head b a Hb Ha).
  apply (real_eq_trans _ (real_plus a b) _).
  - apply real_plus_comm.
  - exact Hsum.
Qed.

(* C3【保底1 主件】：有限具体载体 [true;false] 逐项和零提取 *)
Lemma gibbe2_list_sum_zero_extract_bool :
  forall (f : bool -> Real),
    (forall s : bool, real_le_b real_zero (f s)) ->
    real_eq (real_list_sum bool f [true; false]) real_zero ->
    forall s : bool, real_eq real_zero (f s).
Proof.
  intros f Hpt Hsum s. destruct s; simpl in Hsum.
  - exact (gibbe2_clamp_head (f true) (real_plus (f false) real_zero)
             (Hpt true)
             (gibbe2_le_b_id_r real_zero (f false)
                (real_plus (f false) real_zero)
                (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
             Hsum).
  - apply (real_eq_trans real_zero (real_plus (f false) real_zero) (f false)).
    + exact (gibbe2_clamp_head_r (f true) (real_plus (f false) real_zero)
               (Hpt true)
               (gibbe2_le_b_id_r real_zero (f false)
                  (real_plus (f false) real_zero)
                  (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
               Hsum).
    + exact (real_plus_zero (f false)).
Qed.

(* ============================================================ *)
(* Part D：保底2·log 关系件（KL==0 ⟹ 逐点切点等式）                            *)
(* ============================================================ *)

(* D0：和零 ⟹ 项恒等 *)
Lemma gibbe2_kl_eq_of_w_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq)
                     (real_opp (real_plus p (real_opp q)))) real_zero ->
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)).
Proof.
  intros p q Hp Hq H.
  set (X := real_plus p (real_opp q)).
  set (K := real_kl_term p q Hp Hq).
  set (NX := real_opp X).
  (* kl == (kl + −X) + X *)
  apply (real_eq_trans K (real_plus (real_plus K NX) X) X).
  - apply (real_eq_trans K (real_plus K real_zero) (real_plus (real_plus K NX) X)).
    + exact (real_eq_sym (real_plus K real_zero) K (real_plus_zero K)).
    + apply (real_eq_trans (real_plus K real_zero)
               (real_plus K (real_plus NX X))
               (real_plus (real_plus K NX) X)).
      * apply (RealSetoid.real_eq_plus_compat K real_zero K
                 (real_plus NX X)
                 (real_eq_refl K)
                 (real_eq_trans real_zero (real_plus X NX) (real_plus NX X)
                    (real_eq_sym (real_plus X NX) real_zero (real_plus_opp X))
                    (real_plus_comm X NX))).
      * exact (real_plus_assoc K NX X).
  - (* (kl + −X) + X == 0 + X == X *)
    apply (real_eq_trans (real_plus (real_plus K NX) X)
             (real_plus real_zero X) X).
    + exact (RealSetoid.real_eq_plus_compat (real_plus K NX) X real_zero X
               H (real_eq_refl X)).
    + apply (real_eq_trans (real_plus real_zero X)
               (real_plus X real_zero) X
               (real_plus_comm real_zero X)
               (real_plus_zero X)).
Qed.

(* D1：切点等式形：kl == p−q ⟹ log(q/p) == q/p − 1 *)
Lemma gibbe2_tangent_eq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)) ->
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_mult q (real_inv_pos p Hp))
                     (real_opp real_one)).
Proof.
  intros p q Hp Hq H.
  set (u := real_mult q (real_inv_pos p Hp)).
  set (Hu := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log u Hu).
  (* H : p·(−L) == p + −q *)
  (* 步1：p·L == q + −p（两侧取 opp） *)
  assert (Hs1 : real_eq (real_mult p L) (real_plus q (real_opp p))).
  { apply (real_eq_trans (real_mult p L)
             (real_opp (real_mult p (real_opp L)))
             (real_plus q (real_opp p))).
    - apply (real_eq_sym (real_opp (real_mult p (real_opp L)))
               (real_mult p L)
               (real_eq_trans (real_opp (real_mult p (real_opp L)))
                  (real_mult p (real_opp (real_opp L)))
                  (real_mult p L)
                  (real_opp_mult p (real_opp L))
                  (RealSetoid.real_eq_mult_compat p
                     (real_opp (real_opp L)) p L
                     (real_eq_refl p) (real_opp_opp L)))).
    - apply (real_eq_trans (real_opp (real_mult p (real_opp L)))
               (real_opp (real_plus p (real_opp q)))
               (real_plus q (real_opp p))
               (RealSetoid.real_eq_opp_compat (real_mult p (real_opp L))
                  (real_plus p (real_opp q)) H)
               (gibbsd_minus_flip p q)).
  }
  (* 步2：L == (q−p)·inv p *)
  assert (Hs2 : real_eq L (real_mult (real_plus q (real_opp p))
                                        (real_inv_pos p Hp))).
  { apply (real_eq_trans L
             (real_mult (real_mult p L) (real_inv_pos p Hp))
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))).
    - apply (real_eq_trans L (real_mult L real_one)
               (real_mult (real_mult p L) (real_inv_pos p Hp))).
      + apply (real_eq_sym (real_mult L real_one) L (real_mult_one L)).
      + apply (real_eq_trans (real_mult L real_one)
                 (real_mult L (real_mult p (real_inv_pos p Hp)))
                 (real_mult (real_mult p L) (real_inv_pos p Hp))).
        * apply (RealSetoid.real_eq_mult_compat L real_one
                   L (real_mult p (real_inv_pos p Hp))
                   (real_eq_refl L)
                   (real_eq_sym (real_mult p (real_inv_pos p Hp)) real_one
                      (real_inv_pos_correct p Hp))).
        * apply (real_eq_trans
                   (real_mult L (real_mult p (real_inv_pos p Hp)))
                   (real_mult (real_mult L p) (real_inv_pos p Hp))
                   (real_mult (real_mult p L) (real_inv_pos p Hp))).
          -- exact (real_mult_assoc L p (real_inv_pos p Hp)).
          -- apply (RealSetoid.real_eq_mult_compat (real_mult L p)
                     (real_inv_pos p Hp) (real_mult p L) (real_inv_pos p Hp)
                     (real_mult_comm L p) (real_eq_refl _)).
    - apply (RealSetoid.real_eq_mult_compat (real_mult p L)
               (real_inv_pos p Hp) (real_plus q (real_opp p))
               (real_inv_pos p Hp) Hs1 (real_eq_refl _)).
  }
  (* 步3：(q−p)·inv p == q·inv p + −1 == u + −1 *)
  assert (Hs3 : real_eq (real_mult (real_plus q (real_opp p))
                                   (real_inv_pos p Hp))
                        (real_plus u (real_opp real_one))).
  { apply (real_eq_trans
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
             (real_plus (real_mult (real_inv_pos p Hp) q)
                        (real_mult (real_inv_pos p Hp) (real_opp p)))
             (real_plus u (real_opp real_one))).
    - apply (real_eq_trans
               (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
               (real_mult (real_inv_pos p Hp) (real_plus q (real_opp p)))
               (real_plus (real_mult (real_inv_pos p Hp) q)
                          (real_mult (real_inv_pos p Hp) (real_opp p)))).
      + apply (real_mult_comm (real_plus q (real_opp p)) (real_inv_pos p Hp)).
      + exact (real_distrib (real_inv_pos p Hp) q (real_opp p)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos p Hp) q)
               (real_mult (real_inv_pos p Hp) (real_opp p))
               (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
      + apply (real_mult_comm (real_inv_pos p Hp) q).
      + apply (real_eq_trans (real_mult (real_inv_pos p Hp) (real_opp p))
                   (real_opp (real_mult (real_inv_pos p Hp) p))
                   (real_opp real_one)).
        * apply (real_eq_sym _ _ (real_opp_mult (real_inv_pos p Hp) p)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (real_inv_pos p Hp) p) real_one).
          apply (real_eq_trans (real_mult (real_inv_pos p Hp) p)
                     (real_mult p (real_inv_pos p Hp)) real_one).
          -- apply (real_mult_comm (real_inv_pos p Hp) p).
          -- exact (real_inv_pos_correct p Hp).
  }
  exact (real_eq_trans L _ _ Hs2 Hs3).
Qed.

(* D2【保底2 主件】：KL==0 ⟹ 逐点切点等式 log(q_s/p_s) == q_s/p_s − 1 *)
Lemma gibbe2_kl_zero_tangent_eq :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool,
    real_eq (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                         (Hq s) (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                       (real_opp real_one)).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl.
  set (K := fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : bool => real_plus (p s) (real_opp (q s))).
  set (D := fun s : bool => real_plus (K s) (real_opp (G s))).
  (* 1. Σ(p−q) == 0 *)
  assert (HsumG0 : real_eq (real_list_sum bool G [true; false]) real_zero).
  { apply (real_eq_trans
             (real_list_sum bool G [true; false])
             (real_plus (real_list_sum bool p [true; false])
                        (real_opp (real_list_sum bool q [true; false])))
             real_zero).
    - exact (gibbsd_list_sum_minus bool p q [true; false]).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool p [true; false])
                          (real_opp (real_list_sum bool q [true; false])))
               (real_plus real_one (real_opp real_one)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool p [true; false])
                 (real_opp (real_list_sum bool q [true; false]))
                 real_one (real_opp real_one) Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool q [true; false]) real_one Hnq)).
      + exact (real_plus_opp real_one).
  }
  (* 2. ΣD == 0 *)
  assert (HsumD : real_eq (real_list_sum bool D [true; false]) real_zero).
  { unfold D.
    apply (real_eq_trans
             (real_list_sum bool
                (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
             (real_plus (real_list_sum bool K [true; false])
                        (real_opp (real_list_sum bool G [true; false])))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum bool
                  (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
               (real_plus (real_list_sum bool K [true; false])
                          (real_list_sum bool
                             (fun s : bool => real_opp (G s)) [true; false]))
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))).
      + exact (real_list_sum_add bool K (fun s : bool => real_opp (G s))
                   [true; false]).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_list_sum bool (fun s : bool => real_opp (G s)) [true; false])
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 (real_eq_refl _)
                 (real_list_sum_opp bool G [true; false])).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))
               (real_plus real_zero (real_opp real_zero)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 real_zero (real_opp real_zero) Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool G [true; false]) real_zero HsumG0)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero) real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero (real_opp real_zero)
                   real_zero real_zero (real_eq_refl _) (real_opp_zero)).
        * exact (real_plus_zero real_zero).
  }
  (* 3. 逐点钳零：D s == 0 *)
  assert (Hclamp : forall s : bool, real_eq (D s) real_zero).
  { intro s. apply (real_eq_sym _ _).
    apply (gibbe2_list_sum_zero_extract_bool D).
    - intro s0. exact (gibbe2_le_b_nonneg_diff _ _
                         (gibbsd_gibbs_pointwise_B bool p q s0 (Hp s0) (Hq s0))).
    - exact HsumD. }
  (* 4. 逐点：K s == G s ⟹ 切点等式 *)
  intro s. apply gibbe2_tangent_eq.
  apply gibbe2_kl_eq_of_w_zero.
  exact (Hclamp s).
Qed.

(* ============================================================ *)
(* Part E：主件·桥注入形证明件                                                 *)
(* ============================================================ *)

Theorem gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
     real_eq u real_one) ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl Heqlin s.
  assert (Htan := gibbe2_kl_zero_tangent_eq p q Hp Hq Hnp Hnq Hkl s).
  assert (Hu1 : real_eq (real_mult (q s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (Heqlin (real_mult (q s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                (Hq s) (real_inv_pos_pos (p s) (Hp s)))).
    exact Htan. }
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))
           (q s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))).
    + apply (real_eq_sym (real_mult (p s) real_one) (p s)
               (real_mult_one (p s))).
    + apply (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (q s) (Hp s)).
Qed.

(* ============================================================ *)
(* 尾核：Print Assumptions（G3 零公理见证）                                    *)
(* ============================================================ *)

Print Assumptions gibbe2_le_b_antisym.
Print Assumptions gibbe2_clamp_head.
Print Assumptions gibbe2_list_sum_zero_extract_bool.
Print Assumptions gibbe2_kl_zero_tangent_eq.
Print Assumptions gibbe2_gibbs_equality_bool.
