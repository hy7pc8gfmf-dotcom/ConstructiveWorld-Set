(* ==========================================================================
   UpAblT6_UpSigMigrate2.v - the sumf interface slots of the free-energy
   core section, discharged at the enumerated finite-sum instance.
   Mission. 使命: at the concrete finite-sum operator sumd_sumf the three
     sumf interface assumptions hold unconditionally - the premise thins to
     a pure data slot (the enumeration list), each assumption discharged:
     uabT6_sigmig2_sum_ext, uabT6_sigmig2_sum_add, uabT6_sigmig2_sum_linear.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqSumD of the
     -Set lineage world; the interface is the argument-less Class
     RealInterfaceEnhancedSetoid (module RealInterfaceEnhancedMod).
   References. 对标: the sumf interface slots (sum_ext / sum_add /
     sum_linear) of the free-energy core section. Statement names carried
     over verbatim from the source piece; adaptation = pure binder removal
     + notation rebinding on this world's own precedent (the source
     forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} binders were an
     alien argumented face raising "Illegal application (Non-functional
     construction)"): R := Real by notation (UpReqSumD.v), predicate face
     real_eq through the global instance (UpReqSumD.v L113-114), the proof
     bodies discharge by direct consumption of the in-register supply
     lemmas sumd_sum_ext / sumd_sum_add / sumd_sum_linear (UpReqSumD).
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; the proof content lives in the supply
     lemmas (list-induction chains), this piece connects them at the
     instance; the tail Print Assumptions probes report the closure face;
     no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> "" -Q . ""
     UpAblT6_UpSigMigrate2.v (cpu_guard thermal wrapper, ulimit -s 65532).
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v precedent). *)
Notation R := Real.

(* ============ the sumf interface slots of the free-energy core section ============ *)
(* Prem discharged to the fully-applied form: the enumeration list is the
   only remaining data slot; sumf := sumd_sumf S enum. *)

(* A1 sum_ext. The predicate face is real_eq, the same face as the supply
   lemmas (the two constant names are delta-equal through the instance; the
   extraction face keeps one constant name, so the statement face carries
   real_eq directly). *)
Theorem uabT6_sigmig2_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  exact (sumd_sum_ext).
Qed.

(* A2 sum_add *)
Theorem uabT6_sigmig2_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  exact (sumd_sum_add).
Qed.

(* A3 sum_linear *)
Theorem uabT6_sigmig2_sum_linear :
  forall (S : Set) (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  exact (sumd_sum_linear).
Qed.

(* ============ assumption audit ============ *)
Print Assumptions uabT6_sigmig2_sum_ext.
Print Assumptions uabT6_sigmig2_sum_add.
Print Assumptions uabT6_sigmig2_sum_linear.
