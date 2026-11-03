(* ==========================================================================
   UpAblD1S13_UpReqAlignClose.v - the UpReqAlignClose section-remainder
   slots, discharged as a one-point instance package.
   Mission. 使命: one named instance declaration, one positivity
     certificate for the alignment partition function at the one-point
     instance, one record-type package uabd1s13_uac_pack16 restating the
     sixteen remainder slots in declaration order (the KL plain-le slot
     enters as an explicit premise, exactly as the source section
     declares it - an honest-interface slot, not claimed as a supply),
     and one discharge theorem taking that premise.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqAlign of the
     -Set lineage world; argument-less Class RealInterfaceEnhancedSetoid;
     notation rebind Notation R := Real; predicate faces converged to
     real_eq / real_le / real_lt; bare field consumption through the
     global instance.
   References. 对标: the alignment requirement family (single-point
     instance at the world's discharged signatures). Statement names
     carried over verbatim; adaptation = binder-pair removal + notation
     rebinding + predicate-face convergence + space-slot monomorphise to
     unit (the D1S17 record-form precedent, keeping the extracted payload
     real data).
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; the tail Print Assumptions probes
     report the closure face; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> ""
     UpAblD1S13_UpReqAlignClose.v (cpu_guard thermal wrapper,
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
Require Import UpReqAlign.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* ============ named instance declaration ============ *)

Definition uabd1s13_ren : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ Z_align_pos supply certificate (field matching) ============ *)

Lemma uabd1s13_uac_zap_pos :
  real_lt zero (@Z_align_req unit
            (fun f : unit -> R => f tt)
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

(* ============ package record: the sixteen remainder slots, in the source
   declaration order; sum_pos and the two log slots are carried by their
   own pieces and are not restated here. The space slot is monomorphised
   to unit (the instance the discharge supplies). ============ *)

Inductive uabd1s13_uac_pack16 : Type :=
| uabd1s13_uac_pack16_intro :
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
                forall (eta : R) (eta_pos : real_lt zero eta)
                       (eta_le_one : real_le eta one),
                  forall (Z_align_pos :
                            real_lt zero (@Z_align_req unit sumf reward beta
                                               beta_pos pi_ref)),
                    forall (uac_gibbs_le_zero :
                              forall (p q : unit -> R)
                                     (Hp : @pos_dist unit p)
                                     (Hq : @pos_dist unit q),
                                real_le zero (@relative_entropy_req unit sumf
                                           p q Hp Hq)),
                        uabd1s13_uac_pack16.

(* ============ discharge: fifteen slots fed at the one-point instance,
   the KL slot taken as the explicit premise ============ *)

Theorem uabd1s13_uac_pack16_supplied :
  forall (GIBBS : forall (p q : unit -> R)
                    (Hp : @pos_dist unit p)
                    (Hq : @pos_dist unit q),
              real_le zero (@relative_entropy_req unit
                        (fun f : unit -> R => f tt) p q Hp Hq)),
    uabd1s13_uac_pack16.
Proof.
  intro GIBBS.
  exact (uabd1s13_uac_pack16_intro
           (fun f : unit -> R => f tt)
           (fun (f g : unit -> R)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> R) =>
              req_refl (plus (f tt) (g tt)))
           (fun (a : R) (f : unit -> R) =>
              req_refl (mult a (f tt)))
           (fun _ : unit => zero)
           one
           one_pos
           (fun _ : unit => one)
           (fun _ : unit => one_pos)
           one
           one_pos
           (le_refl one)
           uabd1s13_uac_zap_pos
           GIBBS).
Qed.

(* ============ closure face ============ *)

Print Assumptions uabd1s13_uac_zap_pos.
Print Assumptions uabd1s13_uac_pack16_supplied.
