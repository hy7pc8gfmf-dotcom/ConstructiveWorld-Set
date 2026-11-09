(* ConstructiveWorld-Set -- UpReq attention-iteration reference ablation pieces, completed on Set carriers. *)

(** * UpAblD1S2_e752_UpReqAttnIter: Set-carrier completion of the two UpReqAttnIter iteration slots (double-sum exchange, absolute value bound).

    Mission.  This file formalizes two reference results of the
      attention-iteration family on Set carriers: the exchange law for a
      double finite sum over one enumerated carrier type
      [uabd1s2_iter_sum_swap_i], and the coincidence of an element with
      its absolute value once zero precedes it [uabd1s2_iter_abs_ge_zero_i].

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqSumD], [fa53_compat_abs], and
      [TempSoftmaxInstantiation] of this development.

    References.  This development, UpAblD1S2_e752_UpReqAttnIter.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q <single-root world> ""
      UpAblD1S2_e752_UpReqAttnIter.v] compiles cleanly (exit 0) on the
      Rocq 9.3.0 tree; the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import List.
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
Require Import fa53_compat_abs.
Require TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

(* ================= Section S. Double finite sum of UpReqAttnIter, supplied
   by the concrete sumd instance =================

   The upstream slot is stated in the context {R : Set} {RIS :
   RealInterfaceEnhancedSetoid R} as the variable sum_swap_i, verbatim:
   forall f : S -> S -> R,
     req (sumf (fun s => sumf (fun s' => f s s')))
         (sumf (fun s' => sumf (fun s => f s s'))).
   Tree-face re-anchor (per PA_TempSoftmaxInstantiation: the class
   RealInterfaceEnhancedSetoid is zero-argument in this tree, its fields
   at the global Real/real_eq carrier, S02:511/:513): the abstract
   carrier R is completed at the global Real carrier, the abstract sumf
   is read as sumd_sumf S0 enum0, the concrete fold over the enumerated
   list, and the setoid req at the canonical instance reads as real_eq
   (the discharged face of sumd_sum_swap itself).  Exchanging the two
   bound variables does not change the accumulated value, since both
   iterated folds traverse the same finite list, and the concrete
   instance is supplied verbatim by sumd_sum_swap of UpReqSumD. *)
Section UabD1S2IterSumFeed.
Variable S0 : Set.
Variable enum0 : list S0.

Theorem uabd1s2_iter_sum_swap_i : forall f : S0 -> S0 -> Real,
  real_eq (sumd_sumf S0 enum0 (fun s : S0 => sumd_sumf S0 enum0 (fun s' : S0 => f s s')))
          (sumd_sumf S0 enum0 (fun s' : S0 => sumd_sumf S0 enum0 (fun s : S0 => f s s'))).
Proof.
  intro f.
  exact (sumd_sum_swap S0 enum0 f).
Qed.

End UabD1S2IterSumFeed.

(* ================= Section A. Absolute value bound of UpReqAttnIter, supplied
   through the setoid bridge instance =================

   The upstream slot reads verbatim: forall a : R, le zero a ->
   req (abs a) a.  Tree-face re-anchor (per PA_TempSoftmaxInstantiation:
   the class RealInterfaceEnhancedSetoid is zero-argument in this tree
   and its bridge instance tsi_rie_setoid takes no carrier argument, so
   the per-carrier setoid bridge has no tree counterpart): the carrier
   reads as the interface carrier @S01_BaseRing.R RI0, le/zero/abs as
   the RealInterface fields of RI0, and the setoid req at the interface
   as the interface equality Id; once zero precedes a, the element a
   coincides with its absolute value, and the statement is supplied
   directly by fa53_abs_ge_zero_id_dec (its discharged face, with the
   implicit {RI}{DO} slots made explicit). *)

Theorem uabd1s2_iter_abs_ge_zero_i :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a : @S01_BaseRing.R RI0),
    @S01_BaseRing.le RI0 (@S01_BaseRing.zero RI0) a ->
    Id (@S01_BaseRing.abs RI0 a) a.
Proof.
  intros RI0 DO0 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

(* ================= Closing. The assumption audit is printed for each
   statement ================= *)
Print Assumptions uabd1s2_iter_sum_swap_i.
Print Assumptions uabd1s2_iter_abs_ge_zero_i.
