(* ConstructiveWorld-Set — log-face alignment cluster: temperature-entropy group. *)

(** * UpAblT2a_UpReqTempEntropy: interface-slot alignment theorems for the
      log/exp temperature-entropy face at the concrete Real instance
      [RealEnhancedReal] of [RealInterfaceEnhancedSetoid].

    Mission.  Eighteen interface slots of the log/exp temperature-entropy
      face hold unconditionally at the Real instance: logarithm
      compatibility under pointwise agreement (8 stations), the inverse
      identity log(1/x) = −log x (4 stations), the exponential identity
      log(e^{−u}) = −u (6 stations); every assumption slot reduces to a
      data slot (a positivity witness); predicate positions carried by
      the Set-valued relations [req]/[lt]; names in source order.

    Dependencies.  [S01_BaseRing] through [S15_TailFEPUp], [G05_LogSmall];
      interface = the argument-less Class [RealInterfaceEnhancedSetoid]
      (module [RealInterfaceEnhancedMod]), instance [RealEnhancedReal].

    References.  Slot faces carried verbatim (with [R := Real]) from the
      interface segments of the modules imported below; content consumed
      from the [G05_LogSmall] Real-layer closures ([logd_log_compat_real],
      [logd_log_inv_one_inv_real], [logd_log_exp_neg_real]).

    Constructivity.  All statements Set-carried ([req]/[lt] are
      [Real -> Real -> Set]); every station closes by [Defined] (a
      computable per-eps witness function); zero admitted items, no new
      axioms; tail [Print Assumptions] report closure.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT2a_UpReqTempEntropy.v]
      compiles cleanly (exit 0); artifact bytes [436f7121 000160bc]. *)

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
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* The interface class in this tree is unparameterized; its carrier is the
   global Real.  The interface vocabulary below is bound to the global
   concrete constants (the [G05_LogSmall] carrier convention), so every
   statement face elaborates onto the Set-valued carriers of the supply
   closures and extraction converges without casts. *)
Notation req := real_eq.
Notation zero := real_zero.
Notation opp := real_opp.
Notation lt := real_lt.
Notation inv_pos := real_inv_pos.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation log := real_log.

(* ---- log compatibility (core alignment slot) ---- *)
Theorem uabT2a_align_log_req_compat_core :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- log compatibility (KL-projection alignment slot) ---- *)
Theorem uabT2a_align_log_req_compat_klproj :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- log compatibility (second alignment segment slot) ---- *)
Theorem uabT2a_a2_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- inverse identity (distribution-layer slot): log(1/x) = −log x ---- *)
Theorem uabT2a_dist_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- exponential identity (distribution-layer slot): log(e^{−u}) = −u ---- *)
Theorem uabT2a_dist_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- inverse identity (FEP-layer slot) ---- *)
Theorem uabT2a_fep_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- exponential identity (FEP-layer slot) ---- *)
Theorem uabT2a_fep_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- log compatibility (FEP-layer slot) ---- *)
Theorem uabT2a_fep_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- inverse identity (log-zero segment slot) ---- *)
Theorem uabT2a_lz_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- exponential identity (log-zero segment slot) ---- *)
Theorem uabT2a_lz_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- log compatibility (log-zero segment slot) ---- *)
Theorem uabT2a_lz_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- log compatibility (single-line miscellaneous slot) ---- *)
Theorem uabT2a_m5_req_log_compat_slot :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y), req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- inverse identity (temperature-entropy slot) ---- *)
Theorem uabT2a_te_dist_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- exponential identity (temperature-entropy slot) ---- *)
Theorem uabT2a_te_dist_log_exp_neg :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- exponential identity (signature-migration request slot) ---- *)
Theorem uabT2a_sigm2_req_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Defined.

(* ---- log compatibility (signature-migration request slot) ---- *)
Theorem uabT2a_sigm2_req_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Defined.

(* ---- exponential identity (signature-migration base slot) ---- *)
Theorem uabT2a_sigm2_b_log_exp_neg :
  forall x : Real, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (logd_log_exp_neg_real x).
Defined.

(* ---- log compatibility (signature-migration base slot) ---- *)
Theorem uabT2a_sigm2_b_log_compat :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    req a b -> req (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (logd_log_compat_real a b Ha Hb Hab).
Defined.

(* ---- closure audit: per-station [Print Assumptions] ---- *)
Print Assumptions uabT2a_align_log_req_compat_core.
Print Assumptions uabT2a_align_log_req_compat_klproj.
Print Assumptions uabT2a_a2_log_req_compat.
Print Assumptions uabT2a_dist_log_inv_one_inv.
Print Assumptions uabT2a_dist_log_exp_neg.
Print Assumptions uabT2a_fep_log_inv_one_inv.
Print Assumptions uabT2a_fep_log_exp_neg.
Print Assumptions uabT2a_fep_log_req_compat.
Print Assumptions uabT2a_lz_log_inv_one_inv.
Print Assumptions uabT2a_lz_log_exp_neg.
Print Assumptions uabT2a_lz_log_req_compat.
Print Assumptions uabT2a_m5_req_log_compat_slot.
Print Assumptions uabT2a_te_dist_log_inv_one_inv.
Print Assumptions uabT2a_te_dist_log_exp_neg.
Print Assumptions uabT2a_sigm2_req_log_exp_neg.
Print Assumptions uabT2a_sigm2_req_log_compat.
Print Assumptions uabT2a_sigm2_b_log_exp_neg.
Print Assumptions uabT2a_sigm2_b_log_compat.
