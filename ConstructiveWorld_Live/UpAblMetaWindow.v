(* ==========================================================================)
   UpAblMetaWindow.v — 两态核的退化窗与双侧混合窗
   使命: mwi_step（两态核一步演化）、mwi_collapse_row_equal（核行全同 ⟹ 一步 TV == 0）、mwi_Kunif 均匀核实例与 mtw_window_two_sided（退化侧与持续侧双侧合取）。
   依赖: S01_BaseRing、CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist、UpReqSampling、UpAblMetaWorld3
   对标: 有限马尔可夫链混合时间窗（退化核与均匀核的总变差距离）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
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
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpAblMetaWorld3.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 退化侧机器：泛型核一步演化 + 基座代数桥                                      *)
(* ============================================================ *)

(* 泛型一步演化器：与供体 mtw_step 同构，核 K 提升为显式参数 *)
Definition mwi_step (K : bool -> bool -> Real) (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (K true s')) (mult (mu false) (K false s')).

(* 左零乘：0·a == 0（基座 mult_zero 仅右零形，comm 桥） *)
Lemma mwi_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans (mult zero a) (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* 自差为零：a − a == 0 *)
Lemma mwi_req_minus_self : forall a : Real, req (req_minus a a) zero.
Proof.
  intro a.
  unfold req_minus.
  exact (plus_opp a).
Defined.

(* 零的绝对值：|0| == 0 *)
Lemma mwi_abs_zero : req (abs zero) zero.
Proof. exact abs_zero. Defined.

(* ============================================================ *)
(* §2 退化面定理：核行全同 ⟹ 一步退化（TV == 0，混合窗退化侧）                      *)
(*   注：行随机前提为世界资格前提；退化本体只需行全同（两行同为首行）。                *)
(* ============================================================ *)

Theorem mwi_collapse_row_equal :
  forall K : bool -> bool -> Real,
    (forall s : bool, req (plus (K s true) (K s false)) one) ->
    (forall s s' : bool, req (K s s') (K true s')) ->
    req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero.
Proof.
  intros K Hrow Heq.
  (* 质量对在核 K 下一步演化逐点等于首行：mu0 侧 = 1·K(t,·) + 0·K(f,·) *)
  assert (Ht : forall s' : bool, req (mwi_step K mtw_mu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_mu0 s')
                     (plus (K true s') zero)
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_mu0 true) (K true s')) (K true s')
               (mult (mtw_mu0 false) (K false s')) zero
               (req_mult_one_l (K true s'))
               (mwi_mult_zero_l (K false s'))).
    - exact (plus_zero (K true s')). }
  (* nu0 侧 = 0·K(t,·) + 1·K(f,·) = K(f,·) = K(t,·)（行全同） *)
  assert (Hf : forall s' : bool, req (mwi_step K mtw_nu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_nu0 s')
                     (plus zero (K false s'))
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_nu0 true) (K true s')) zero
               (mult (mtw_nu0 false) (K false s')) (K false s')
               (mwi_mult_zero_l (K true s'))
               (req_mult_one_l (K false s'))).
    - exact (req_trans (plus zero (K false s')) (K false s') (K true s')
               (req_plus_zero_l (K false s'))
               (Heq false s')). }
  (* 逐点差为零 ⟹ 逐点绝对值为零 *)
  assert (Hz : forall s' : bool,
           req (abs (req_minus (mwi_step K mtw_mu0 s')
                               (mwi_step K mtw_nu0 s'))) zero).
  { intro s'.
    apply (req_trans
             (abs (req_minus (mwi_step K mtw_mu0 s')
                             (mwi_step K mtw_nu0 s')))
             (abs zero) zero).
    - exact (req_abs_compat
               (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
               zero
               (req_trans
                  (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
                  (req_minus (K true s') (K true s'))
                  zero
                  (req_plus_compat
                     (mwi_step K mtw_mu0 s') (K true s')
                     (opp (mwi_step K mtw_nu0 s')) (opp (K true s'))
                     (Ht s')
                     (req_opp_compat (mwi_step K mtw_nu0 s') (K true s')
                               (Hf s')))
                  (mwi_req_minus_self (K true s')))).
    - exact mwi_abs_zero. }
  (* TV = (1/2)·(0+0) = 0 *)
  apply (req_trans (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0))
                   (mult mtw_half zero) zero).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mwi_step K mtw_mu0 s)
                                  (mwi_step K mtw_nu0 s))))
             zero
             (req_refl mtw_half)
             (req_trans
                (mtw_sumf (fun s : bool =>
                      abs (req_minus (mwi_step K mtw_mu0 s)
                                     (mwi_step K mtw_nu0 s))))
                (plus zero zero) zero
                (req_plus_compat
                   (abs (req_minus (mwi_step K mtw_mu0 true)
                                   (mwi_step K mtw_nu0 true))) zero
                   (abs (req_minus (mwi_step K mtw_mu0 false)
                                   (mwi_step K mtw_nu0 false))) zero
                   (Hz true) (Hz false))
                (req_plus_zero_l zero))).
  - exact (mult_zero mtw_half).
Defined.

(* ============================================================ *)
(* §3 退化世界显式实例：均匀核（每行 (1/2,1/2)，行全同）TV(1) == 0                  *)
(* ============================================================ *)

Definition mwi_Kunif (s s' : bool) : Real := mtw_half.

Lemma mwi_Kunif_row : forall s : bool,
  req (plus (mwi_Kunif s true) (mwi_Kunif s false)) one.
Proof. intro s. unfold mwi_Kunif. exact mtw_hh_one. Defined.

Lemma mwi_Kunif_rows_eq : forall s s' : bool,
  req (mwi_Kunif s s') (mwi_Kunif true s').
Proof. intros s s'. unfold mwi_Kunif. exact (req_refl mtw_half). Defined.

Theorem mwi_degenerate_collapse_uniform :
  req (mtw_tv (mwi_step mwi_Kunif mtw_mu0) (mwi_step mwi_Kunif mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal mwi_Kunif mwi_Kunif_row mwi_Kunif_rows_eq).
Defined.

(* ============================================================ *)
(* §4 主件：双侧混合窗定理（S01 基座 Set 层合取承载）                               *)
(*   左肢=退化侧（退化世界窗退化）；右肢=存在侧（非退化世界窗真实存在：               *)
(*   精确幂律 + 预算下界两支合取）。                                              *)
(* ============================================================ *)

Theorem mtw_window_two_sided :
  And
    (* 退化侧：核行全同的行随机核 ⟹ 一步退化 TV == 0 *)
    (forall K : bool -> bool -> Real,
       (forall s : bool, req (plus (K s true) (K s false)) one) ->
       (forall s s' : bool, req (K s s') (K true s')) ->
       req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero)
    (* 存在侧：非退化世界（World3）精确幂律 + 混合窗预算下界 *)
    (And
       (forall n : nat,
          req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
              (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
       (forall (n : nat) (B : Real),
          lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
          lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
Proof.
  split.
  - exact mwi_collapse_row_equal.
  - split.
    + exact mtw_tv_exact_iter.
    + exact mtw_no_mixing_below.
Defined.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零新假设）                                              *)
(* ============================================================ *)

Print Assumptions mwi_step.
Print Assumptions mwi_mult_zero_l.
Print Assumptions mwi_req_minus_self.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_collapse_row_equal.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mtw_window_two_sided.
