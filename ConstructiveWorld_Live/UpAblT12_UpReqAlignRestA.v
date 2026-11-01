(* ====================================================================== *)
(* Five-field pointer | Mission. Formalization of the property stated by  *)
(*   the declaration face of this piece's theorem.                        *)
(* Dependencies. The library pieces listed on the in-piece Require        *)
(*   declaration faces (all read-only dependencies, zero original-tree    *)
(*   edits): CW_ConstructiveWorld_219, UpReqSumD.                         *)
(* References. UpReqAlignRestA.v, ReqRestACore section sumf interface     *)
(*   face (L70 ralt_sum_ext, one slot); instantiation-resolution source   *)
(*   sumd_sum_ext@UpReqSumD:112; the non-trivial proof content lives in   *)
(*   sumd_list_sum_ext@UpReqSumD (in-library instantiation resolution --  *)
(*   this piece connects directly, no padding; grade N1).                 *)
(* Constructivity. Zero admission-style statements (mechanically          *)
(*   checked); statement face fully Set-layered; axiom face zero         *)
(*   additions; the piece closes with Print Assumptions.                  *)
(* Build. rocq c -native-compiler no -q -Q . "".                          *)
(* ====================================================================== *)
(* Ablation piece: statement face aligned to the world's unparameterized  *)
(*   interface class per S10_KVQuantTrig.v L12417 precedent -- the        *)
(*   Main-tree parameterized binder face forall (R : Set) {RIS :          *)
(*   RealInterfaceEnhancedSetoid R} was an alien transplant into this     *)
(*   -Set-lineage world (RealInterfaceEnhancedSetoid is a zero-parameter  *)
(*   Class whose fields resolve through the global Real instance); fixed  *)
(*   by dropping the binders, Notation R := Real, and the global-face     *)
(*   predicate real_eq -- zero shims, statement face stays Set-layered.   *)
(* ====================================================================== *)

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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

Notation R := Real.

(* ============ ReqRestACore (UpReqAlignRestA.v L66-71 interface face) ==== *)
(* Original section face Context {R}{RIS} + S + sumf; aligned out-of-     *)
(* section form per the S10_KVQuantTrig.v L12417 precedent: R := Real via *)
(* Notation (UpReqSumD.v:58 / UpReqDist.v:52 precedent), the zero-        *)
(* parameter class resolved through its global instance, and sumf         *)
(* replaced by the sumd_sumf S enum instance.                             *)

(* A1 <- L70 ralt_sum_ext (section face: forall f g : S -> R,
   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g);
   aligned face: req -> real_eq global-instance projection) *)
Theorem uabT12_ralt_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* Purpose: discharge the ablation theorem for the req-sum interface-face *)
(* assumption slot of the ReqRestACore section -- on the concrete         *)
(* finite-sum instance sumf := sumd_sumf S enum the assumption slot holds *)
(* unconditionally: the premise thins to pure data parameters (the        *)
(* enumeration list) and the assumption slot is eliminated.               *)
(* Remark: statement face aligned to the world's unparameterized          *)
(* interface class per S10_KVQuantTrig.v L12417 precedent (the Main-tree  *)
(* parameterized signature was an alien transplant into this -Set-        *)
(* lineage world); only the sumf -> sumd_sumf S enum instance slot is     *)
(* swapped.                                                               *)

(* ============ Print Assumptions close-out (per-piece Closed verdict) ==== *)
Print Assumptions uabT12_ralt_sum_ext.
