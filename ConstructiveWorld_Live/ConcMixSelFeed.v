(* ==========================================================================
   ConcMixSelFeed.v — conc/mix/select 接口的 req 层供给总件（-Set 世系对齐代）
   使命: cms_ 系十一件：lt_plus_compat 选形（cms_lt_plus_compat_lt_le_sel/time）、
   求和外延/线性/加法/序四件（cms_sum_ext/linear/add/le）、折叠一致性
   （cms_fold_req_list_sum/sum_eq_list）、bs_swap 换序与 bs_abs/bs_lpc；
   全件 Qed/Defined 闭合，零承认词面。
   依赖清单: S01_BaseRing..S15_TailFEPUp、UpReqAlgebra、UpReqSumD、UpReqSampling、
   Stdlib List；接口面为 S07_RealSetoidExpLog 的 argument-less Class
   RealInterfaceEnhancedSetoid（模块 RealInterfaceEnhancedMod），字段经全局 Real
   实例 RealEnhancedReal 消解。求和机换代注记：旧代 csm_sumf 宿主三件
   （UpReqConcSoftmax/UpReqConcMixSel/UpReqConcB1）现盘无存，语句面按同形同参序
   换为 UpReqSumD 的 sumd_sumf（S/enum/f，透明展开即 sumd_list_sum 折叠）；
   rsq_bs_list_sum 取自 UpReqSampling，签名不变，语句名逐一承旧。
   对标: 求和与混合接口的 req 层系统一实例（接口转接层）。
   构造性注记: 语句面以 Set 层承载（req/le/lt/plus 等皆 Set 值接口字段，零 Prop
   泄露）；零提取强转、零经典逻辑。
   编译配方: Rocq 9.1 直调 rocq c -native-compiler no -Q . ""（vo 影子树同世界
   重编），cpu_guard 包裹限载，ulimit -s 65532。
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
Require Import UpReqSumD.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 世界钉柯西 Real 实数面（lt_plus 混合保序体为 S07 Real 层成品；           *)
(* 接口字段经 RealEnhancedReal 全局实例消解）                              *)

(* ============ 槽①/②：lt_plus_compat_lt_le ×2（Real 层成品直接代入） ========= *)

Theorem cms_lt_plus_compat_lt_le_sel :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

Theorem cms_lt_plus_compat_lt_le_time :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ============ 槽③-⑥：sum 四槽（sumd_sumf 折叠键，任意 S/en 泛型） ======== *)

Theorem cms_sum_ext : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) -> req (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

Theorem cms_sum_linear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => mult a (f s)))
        (mult a (sumd_sumf S0 en f)).
Proof.
  intros S0 en a f.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - simpl.
    exact (req_sym
             (mult a (plus (f x) (sumd_list_sum S0 f t)))
             (plus (mult a (f x))
                     (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
             (req_trans
                (mult a (plus (f x) (sumd_list_sum S0 f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S0 f t)))
                (plus (mult a (f x))
                        (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
                (distrib a (f x) (sumd_list_sum S0 f t))
                (req_plus_compat (mult a (f x)) (mult a (f x))
                   (mult a (sumd_list_sum S0 f t))
                   (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                   (req_refl (mult a (f x)))
                   (req_sym
                      (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                      (mult a (sumd_list_sum S0 f t)) IH)))).
Defined.

Theorem cms_sum_add :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => plus (f s) (g s)))
        (plus (sumd_sumf S0 en f) (sumd_sumf S0 en g)).
Proof.
  intros S0 en f g.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - simpl.
    exact (req_trans
             (plus (plus (f x) (g x))
                     (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                     (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))
             (plus (plus (f x) (sumd_list_sum S0 f t))
                     (plus (g x) (sumd_list_sum S0 g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t)
                (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_sym
                (plus (plus (f x) (sumd_list_sum S0 f t))
                        (plus (g x) (sumd_list_sum S0 g t)))
                (plus (plus (f x) (g x))
                        (plus (sumd_list_sum S0 f t)
                                (sumd_list_sum S0 g t)))
                (req_plus_exchange (f x) (g x)
                   (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))).
Defined.

Theorem cms_sum_le :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, le (f s) (g s)) -> le (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (le_refl zero).
  - simpl.
    exact (le_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

(* ============ 槽⑧：sum_eq_list（折叠衔接 shim + 定义性展开） ============ *)

(* 两折叠机器同构 shim：sumd_list_sum 与 rsq_bs_list_sum 逐构造子同形       *)
(* （nil 支同归 zero、cons 支同为 plus 头元尾折），列表归纳一跳，           *)
(* req_plus_compat 衔接（SumEqList shim 的 req 折叠面重铸）。               *)
Lemma cms_fold_req_list_sum :
  forall (S0 : Set) (g : S0 -> Real) (l : list S0),
    req (sumd_list_sum S0 g l) (rsq_bs_list_sum S0 g l).
Proof.
  intros S0 g l.
  induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (g x) (g x)
             (sumd_list_sum S0 g t) (rsq_bs_list_sum S0 g t)
             (req_refl (g x)) IH).
Defined.

Theorem cms_sum_eq_list : forall (S0 : Set) (en : list S0) (g : S0 -> Real),
  req (sumd_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof.
  intros S0 en g.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl.
    exact (req_plus_compat (g x) (g x) (sumd_list_sum S0 g t)
             (rsq_bs_list_sum S0 g t) (req_refl (g x)) IH).
Defined.

(* ============ 槽⑦：bs_swap（双列表泛型换序归纳） ============ *)

Theorem cms_bs_swap :
  forall (S0 : Set) (en : list S0) (f : S0 -> S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => sumd_sumf S0 en (fun s' : S0 => f s s')))
        (sumd_sumf S0 en (fun s' : S0 => sumd_sumf S0 en (fun s : S0 => f s s'))).
Proof.
  intros S0 en f.
  unfold sumd_sumf.
  assert (Hsw : forall l1 l2 : list S0,
    req (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) l1)
        (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') l1) l2)).
  { intros l1 l2.
    induction l1 as [| x t IH].
    - induction l2 as [| y t2 IH2].
      + exact (req_refl zero).
      + exact (req_trans zero
            (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
            (plus zero
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
            IH2
            (req_sym
               (plus zero
                  (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
               (req_trans
                  (plus zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
                  (plus
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
                     zero)
                  (sumd_list_sum S0
                     (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
                  (plus_comm zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
                  (plus_zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))))).
    - exact (req_trans
            (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) t))
            (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2))
            (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') (x :: t)) l2)
            (req_plus_compat (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) t)
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2)
               (req_refl (sumd_list_sum S0 (fun s' : S0 => f x s') l2)) IH)
            (req_sym
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') (x :: t)) l2)
               (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
                  (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2))
               (cms_sum_add S0 l2 (fun s' : S0 => f x s')
                  (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t)))). }
  exact (Hsw en en).
Defined.

(* ============ 邻接伴件⑨/⑩：bs_abs / bs_lpc ============================ *)

Theorem cms_bs_abs : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

Theorem cms_bs_lpc :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions cms_lt_plus_compat_lt_le_sel.
Print Assumptions cms_lt_plus_compat_lt_le_time.
Print Assumptions cms_sum_ext.
Print Assumptions cms_sum_linear.
Print Assumptions cms_sum_add.
Print Assumptions cms_sum_le.
Print Assumptions cms_fold_req_list_sum.
Print Assumptions cms_sum_eq_list.
Print Assumptions cms_bs_swap.
Print Assumptions cms_bs_abs.
Print Assumptions cms_bs_lpc.
