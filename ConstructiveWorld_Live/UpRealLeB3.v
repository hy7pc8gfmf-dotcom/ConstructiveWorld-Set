(* ==========================================================================)
   UpRealLeB3.v — ≤_B 序的结构律
   使命: leb3_le_b_refl/leb3_le_b_eq_l/leb3_le_b_eq_r（自反与等式运输）、leb3_le_b_plus_nonneg_r、leb3_le_b_opp_rev/leb3_le_b_pos_scale（相反数反转与正缩放）与 leb3_abs_plus_one_pos。
   依赖: S01–S15 系、UpRealLeB、UpRealLeB2；Stdlib QArith
   对标: ε-一致下界序 ≤_B 的基本代数（等式运输与单调运算）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
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
Require Import UpRealLeB2.

(* ============================================================ *)
(* 一、运输四件（自反 / 左右端等式运输 / 非负右加）                      *)
(* ============================================================ *)

(* 件 1：≤_B 自反（单向桥 + real_le_refl 单步） *)
Lemma leb3_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. apply real_le_to_le_b. apply real_le_refl.
Qed.

(* 件 2：左端等式运输：x1≈x2 且 x1 ≤_B y 给 x2 ≤_B y *)
Lemma leb3_le_b_eq_l : forall x1 x2 y : Real,
  real_eq x1 x2 -> real_le_b x1 y -> real_le_b x2 y.
Proof.
  intros x1 x2 y Heq H. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_l x2 x1 (real_plus y eps)).
  - apply real_eq_sym. exact Heq.
  - exact (H eps Heps).
Qed.

(* 件 3：右端等式运输：x ≤_B y1 且 y1≈y2 给 x ≤_B y2
   （逐 eps 加法兼容换形 y1+e == y2+e） *)
Lemma leb3_le_b_eq_r : forall x y1 y2 : Real,
  real_le_b x y1 -> real_eq y1 y2 -> real_le_b x y2.
Proof.
  intros x y1 y2 H Heq. unfold real_le_b in H. unfold real_le_b.
  intros eps Heps.
  apply (RealSetoid.real_lt_id_r x (real_plus y1 eps) (real_plus y2 eps)).
  - apply (RealSetoid.real_eq_plus_compat y1 eps y2 eps).
    + exact Heq.
    + apply real_eq_refl.
  - exact (H eps Heps).
Qed.

(* 件 4：非负右加：x ≤_B y 且 0 ≤ c 给 x ≤_B y+c
   （加法兼容组合器 + x+0==x 左端运输） *)
Lemma leb3_le_b_plus_nonneg_r : forall x y c : Real,
  real_le_b x y -> real_le real_zero c -> real_le_b x (real_plus y c).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_plus x real_zero) x (real_plus y c)).
  - apply real_plus_zero.
  - apply (real_le_b_plus_compat x y real_zero c).
    + exact H.
    + apply real_le_to_le_b. exact Hc.
Qed.

(* ============================================================ *)
(* 二、反序件（≤_B 的负号反变）                                        *)
(* ============================================================ *)

(* 件 5：反序：x ≤_B y 给 −y ≤_B −x。
   给 d>0：H 直取 x<y+d ⟹ −(y+d)<−x（opp 严格反序基元）
   ⟹ 换形 −y+−d<−x（opp 分配）⟹ 双侧右加 d（lt_le 混合加法保序）
   ⟹ 左端 (−y+−d)+d == −y 恒等完成（结合 + −d+d==0 + +0）。
   d 在两侧成对消去，免 eps/2 拆分。 *)
Lemma leb3_le_b_opp_rev : forall x y : Real,
  real_le_b x y -> real_le_b (real_opp y) (real_opp x).
Proof.
  intros x y H. unfold real_le_b in H. unfold real_le_b.
  intros d Hd.
  pose proof (H d Hd) as H1.
  pose proof (real_opp_lt_compat x (real_plus y d) H1) as H2.
  assert (H3 : real_lt (real_plus (real_opp y) (real_opp d)) (real_opp x)).
  { apply (RealSetoid.real_lt_id_l (real_plus (real_opp y) (real_opp d))
                                   (real_opp (real_plus y d)) (real_opp x)).
    - apply real_eq_sym. exact (real_opp_plus y d).
    - exact H2. }
  assert (H4 : real_lt (real_plus (real_plus (real_opp y) (real_opp d)) d)
                       (real_plus (real_opp x) d)).
  { exact (real_lt_plus_compat_lt_le (real_plus (real_opp y) (real_opp d))
                                     (real_opp x) d d H3 (real_le_refl d)). }
  assert (Heq5 : real_eq (real_plus (real_plus (real_opp y) (real_opp d)) d)
                         (real_opp y)).
  { apply (real_eq_trans _
             (real_plus (real_opp y) (real_plus (real_opp d) d)) _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_opp y) real_zero) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp y)
                 (real_plus (real_opp d) d) (real_opp y) real_zero).
        * apply real_eq_refl.
        * apply (real_eq_trans (real_plus (real_opp d) d)
                   (real_plus d (real_opp d)) real_zero).
          -- apply real_plus_comm.
          -- apply real_plus_opp.
      + apply real_plus_zero. }
  apply (RealSetoid.real_lt_id_l (real_opp y)
           (real_plus (real_plus (real_opp y) (real_opp d)) d)
           (real_plus (real_opp x) d)).
  - apply real_eq_sym. exact Heq5.
  - exact H4.
Qed.

(* ============================================================ *)
(* 三、正缩放件（完成器反用）                                           *)
(* ============================================================ *)

(* 件 6：正缩放：x ≤_B y 且 0<c 给 x·c ≤_B y·c。
   完成器反用（D:=c）：给 e>0 只需 Or 形 x·c ≤ y·c+c·e——
   x<y+e 经乘法保序 ⟹ x·c<(y+e)·c，再 (y+e)·c==y·c+c·e 换形。 *)
Lemma leb3_le_b_pos_scale : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult x c) (real_mult y c).
Proof.
  intros x y c H Hc.
  apply (real_le_closure_b (real_mult x c) (real_mult y c) c Hc).
  intros eps Heps. unfold real_le. left.
  apply (RealSetoid.real_lt_id_r (real_mult x c)
           (real_mult (real_plus y eps) c)
           (real_plus (real_mult y c) (real_mult c eps))).
  - apply (real_eq_trans _ (real_mult c (real_plus y eps)) _).
    + apply real_mult_comm.
    + apply (real_eq_trans _
               (real_plus (real_mult c y) (real_mult c eps)) _).
      * apply real_distrib.
      * apply (RealSetoid.real_eq_plus_compat (real_mult c y)
                 (real_mult c eps) (real_mult y c) (real_mult c eps)).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
  - exact (real_mult_lt_compat x (real_plus y eps) c (H eps Heps) Hc).
Qed.

(*
   等式运输两步平移（comm 换形各一） *)
Lemma leb3_le_b_pos_scale_l : forall x y c : Real,
  real_le_b x y -> real_lt real_zero c ->
  real_le_b (real_mult c x) (real_mult c y).
Proof.
  intros x y c H Hc.
  apply (leb3_le_b_eq_l (real_mult x c) (real_mult c x) (real_mult c y)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult x c) (real_mult y c) (real_mult c y)).
    + apply (leb3_le_b_pos_scale x y c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 四、严格对照锚件（冻结 72 筛余唯一 Real 层可对照行）                  *)
(* ============================================================ *)

(* 件 7：0 < |a|+1。依 S09 判例件 real_abs_plus_one_pos（0 < 1+|a|，逐点 born-clean：
   QeqT 门桥投影 qeqT_imp_qeq＋Qabs 非负），经 real_plus_comm 加法交换
   ＋ real_lt_id_r 右端等式运输一步到位（语句面与正源逐字相同）。 *)
Lemma leb3_abs_plus_one_pos : forall a : Real,
  real_lt real_zero (real_plus (real_abs a) real_one).
Proof.
  intro a.
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus real_one (real_abs a))
           (real_plus (real_abs a) real_one)).
  - apply real_plus_comm.
  - exact (real_abs_plus_one_pos a).
Qed.

(* ============================================================ *)
(* 五、假设审计（全件 Closed，证据在编译日志）                           *)
(* ============================================================ *)

Print Assumptions leb3_le_b_refl.
Print Assumptions leb3_le_b_eq_l.
Print Assumptions leb3_le_b_eq_r.
Print Assumptions leb3_le_b_plus_nonneg_r.
Print Assumptions leb3_le_b_opp_rev.
Print Assumptions leb3_le_b_pos_scale.
Print Assumptions leb3_le_b_pos_scale_l.
Print Assumptions leb3_abs_plus_one_pos.
