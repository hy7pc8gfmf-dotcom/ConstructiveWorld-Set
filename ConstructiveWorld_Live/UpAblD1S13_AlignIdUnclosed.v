(* ==========================================================================
   UpAblD1S13_AlignIdUnclosed.v - data-supply module for the AiuBackwardKL
   section (piece two): the fourteen remaining slot positions of the
   AiuBackwardKL section, given by one single-point instance.
   Mission. 使命: instance supply for the AiuBackwardKL residual slots --
   R, RIS (the interface itself), S, sumf, sum_ext, sum_add, sum_linear,
   reward, beta, beta_pos, pi_ref, pi_ref_pos, eta, and ZAL_pos (the Z
   certificate, the req2_Z_align single-point instance) -- assembled as the
   supply record uabd1s13_aiu_pack14 with its supply theorem; sum_pos and
   the two log slots go to the sibling pieces and are excluded here.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqAlign2 of the
   -Set lineage world; interface = the argument-less Class
   RealInterfaceEnhancedSetoid (module RealInterfaceEnhancedMod).
   References. 对标: statement names carried over verbatim; adaptation =
     binder-shell removal + notation rebinding on this world's own precedent
     (the source argumented Class applications raised "Illegal application
     (Non-functional construction)"): the binder pairs (R : Set)
     (RIS : RealInterfaceEnhancedSetoid R) are removed, R := Real by
     notation (UpReqSumD.v L58), law fields resolve as bare names through
     the global instance RealEnhancedReal (UpReqSumD.v L68-72), the
     predicate faces are real_eq/real_lt (UpReqSumD.v L113-114); the type
     slots (S) are monomorphised to the supplied unit instance (type slots
     are erased at extraction and would raise Obj.magic at slot values).
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; supply-grade unconditional witnesses
     throughout; tail Print Assumptions report the closure face.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> "" -Q . ""
     UpAblD1S13_AlignIdUnclosed.v (cpu_guard thermal wrapper,
     ulimit -s 65532).
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
Require Import UpReqAlign2.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v L58 precedent). *)
Notation R := Real.

Definition uabd1s13_ren : RealInterfaceEnhancedSetoid :=
  RealEnhancedReal.

(* ============ ZAL_pos supply certificate (ZAL = the req2_Z_align
   single-point instance; three law fields matched directly) ============ *)

Lemma uabd1s13_aiu_zal_pos :
  real_lt zero (req2_Z_align unit
            (fun f : unit -> Real => f tt)
            (fun _ : unit => zero)
            one
            one_pos
            (fun _ : unit => one)).
Proof.
  exact (mult_positive
           one
           (exp_neg
              (opp
                 (mult
                    (inv_pos one one_pos)
                    zero)))
           one_pos
           (exp_neg_pos
              (opp
                 (mult
                    (inv_pos one one_pos)
                    zero)))).
Qed.

(* ============ supply record: source lines L74-118 verbatim in ============ *)
(* Slot order = supply order; sum_pos (L87) and the two log slots (L89-93)
   are supplied by the sibling pieces and not part of this record (see the
   exclusion note at the head). *)
(* The type slots (S) of the source record are monomorphised to the supplied
   unit instance: type slots are erased at extraction and would raise
   Obj.magic casts at every slot value; the record's slot values below are
   carried by that single instance. *)

Inductive uabd1s13_aiu_pack14 : Type :=
| uabd1s13_aiu_pack14_intro :
    forall (sumf : (unit -> R) -> R),
        forall (sum_ext : forall f g : unit -> R,
                   (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)),
          forall (sum_add : forall f g : unit -> R,
                     real_eq (sumf (fun s : unit => plus (f s) (g s)))
                         (plus (sumf f) (sumf g))),
            forall (sum_linear : forall (a : R) (f : unit -> R),
                       real_eq (sumf (fun s : unit => mult a (f s)))
                           (mult a (sumf f))),
              forall (reward : unit -> R) (beta : R) (beta_pos : real_lt zero beta),
                forall (pi_ref : unit -> R)
                       (pi_ref_pos : forall s : unit, real_lt zero (pi_ref s)),
                  forall (eta : R),
                    forall (ZAL_pos :
                              real_lt zero (req2_Z_align unit sumf reward beta
                                         beta_pos pi_ref)),
                      uabd1s13_aiu_pack14.

(* ============ instance supply: one single-point instance fills all
   fourteen slots ============ *)

Theorem uabd1s13_aiu_pack14_supplied :
  uabd1s13_aiu_pack14.
Proof.
  exact (uabd1s13_aiu_pack14_intro
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) =>
              req_refl (plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              req_refl (mult a (f tt)))
           (fun _ : unit => zero)
           one
           one_pos
           (fun _ : unit => one)
           (fun _ : unit => one_pos)
           one
           uabd1s13_aiu_zal_pos).
Qed.

(* ============ assumption-face closure declaration ============ *)

Print Assumptions uabd1s13_aiu_zal_pos.
Print Assumptions uabd1s13_aiu_pack14_supplied.
