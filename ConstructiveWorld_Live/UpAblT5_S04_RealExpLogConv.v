(* ==========================================================================
   UpAblT5_S04_RealExpLogConv.v - three supply slots for the real exp/log
   convergence interface (positive-inverse strict antitone bridge, strict
   log monotonicity, archimedean power).
   Mission. 使命: (1) abl_S04_inv_pos_lt_compat - the strictly antitone
     positive-inverse slot at the abstract interface layer; (2)
     abl_S04_log_lt_mono_cc - strict log monotonicity at the concrete Real
     layer; (3) abl_r_pow and abl_S04_r_arch_pow - the archimedean power
     witness at the concrete Real layer.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, InvPosLtCompat,
     CW220_Extensions (module BudgetReal), G05_LogSmall of the -Set lineage
     world; slot (1) consumes ipl_inv_pos_lt_compat (InvPosLtCompat), slot
     (2) consumes logd_log_lt_mono_real (G05_LogSmall), slot (3) consumes
     r_arch_pow_real (CW220_Extensions.BudgetReal).
   References. 对标: the inv_pos_lt_compat / log_lt_mono_cc / r_arch_pow
     slot family of the real exp/log convergence interface. Statement names
     carried over verbatim from the source piece; adaptation = the carrier
     alias for slot (1) is bound through the qualified class-field
     projection (the bare name R at the binding site resolves to the
     Notation R := Real of the concrete-layer supply modules, so the bare
     projection form raises "Illegal application (Non-functional
     construction)"); the same unpack form as InvPosLtCompat of this world.
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; the tail Print Assumptions probes
     report the closure face; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> "" -Q . ""
     UpAblT5_S04_RealExpLogConv.v (cpu_guard thermal wrapper,
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
Require Import InvPosLtCompat.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
Require Import G05_LogSmall.

(* ################ (1) inv_pos_lt_compat (slot shape of the source file,
   abstract interface layer) ################ *)
(* The statement depends on the interface alone, so the unpacking section
   carries the interface instance alone (same unpack preamble as
   InvPosLtCompat). *)
Section AblS04FreeEnergy.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* Projection aliases (unpack interface fields as local Lets). The carrier
   alias is bound through the qualified class-field projection: the bare
   name R at this binding site resolves to the Notation R := Real brought
   in by the concrete-layer supply modules (CW220_Extensions, G05_LogSmall),
   and the bare projection form would apply a Set to an instance. *)
Let R := @S01_BaseRing.R (@RI_base RI).
Let zero := @S01_BaseRing.zero (@RI_base RI).
Let one := @S01_BaseRing.one (@RI_base RI).
Let mult := @S01_BaseRing.mult (@RI_base RI).
Let inv_pos := @S01_BaseRing.inv_pos (@RI_base RI).
Let lt := @S01_BaseRing.lt (@RI_base RI).

Theorem abl_S04_inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblS04FreeEnergy.

(* ################ (2) log_lt_mono_cc (slot shape of the source file;
   concrete Real-layer supply form) ################ *)
Theorem abl_S04_log_lt_mono_cc : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  exact logd_log_lt_mono_real.
Qed.

(* ################ (3) r_arch_pow (slot shape of the source file; concrete
   Real-layer supply form) ################ *)
(* Repeated multiplication by the contraction factor, definition-level
   isomorphic to real_pow (CW220_Extensions.BudgetReal). *)
Fixpoint abl_r_pow (x : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult x (abl_r_pow x m)
  end.

(* Section prem discharged to the fully-applied form. *)
Theorem abl_S04_r_arch_pow :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun n : nat => real_lt (real_mult a (abl_r_pow kappa n)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  exact (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps).
Qed.

(* ---- assumption audit ---- *)
Print Assumptions abl_S04_inv_pos_lt_compat.
Print Assumptions abl_S04_log_lt_mono_cc.
Print Assumptions abl_S04_r_arch_pow.
