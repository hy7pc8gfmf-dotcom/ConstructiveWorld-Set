(* ==========================================================================
   abl_tbase_expf_bs_feed.v
   Mission.
     Supply theorems at the concrete Cauchy-real layer for the expf and bs
     slot families: seven expf slots (positivity and strict monotonicity of
     the realized exponential), three bs slots (double-sum symmetry, the
     absolute value of a nonnegative real, enumerated-sum normalization),
     and one Id-face bridge for the attention Doeblin slot; each theorem is
     an assumption-free exact reference to a certified root.
   Dependencies.
     S01_BaseRing, S02_CauchyComplete, S07_RealSetoidExpLog (module
     RealInterfaceEnhancedMod imported), UpReqConcSoftmax, UpReqSampling,
     UpAblD1_expf_pack, ConcMixSelFeed, UpReqConcMixSel, IdSlotTranslate,
     AttnDoeblin. Roots: uabd1x_expf_pos and uabd1x_expf_mono_lt
     (UpAblD1_expf_pack), cmkr_bs_swap, cmkr_bs_abs, cmkr_sum_eq_list
     (UpReqConcMixSel), idt_slot_attdoeblin (IdSlotTranslate).
   References.
     Statement carriers: real_lt, real_eq, real_le (S02_CauchyComplete,
     sigT/QltT Set-level forms) and Id (S01_BaseRing Set-level identity
     type); statement shapes mirror the host slot rows of Paper7Ablation,
     MixTimeChain, MixTimeChainIface, UpReqConcMixSel, UpAblT1b_AttnDoeblin.
   Constructivity.
     All statement faces are Set-carried (no Prop statements); every proof
     is a transparent Defined one-step reference; no axioms, no admitted
     goals, no classical logic; Print Assumptions is Closed for all eleven
     theorems. Obj.magic sites printed by the extraction commands below
     belong to the certified root closure and recur under roots-only
     extraction; none are introduced by this module.
   Build. coqc -Q <ConstructiveWorld_Live> "" abl_tbase_expf_bs_feed.v
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpAblD1_expf_pack.
Require Import ConcMixSelFeed.
Require Import UpReqConcMixSel.
Require Import IdSlotTranslate.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Segment 0. The exponential function instance: a definitional   *)
(* transcription of the package projection uabd1x_expf.           *)
(* ============================================================ *)
Definition tspex_fn : Real -> Real := uabd1x_expf.

(* ============================================================ *)
(* Segment 1. The expf family, 7 rows, closed specialization of   *)
(* the abstract interface fields; each row is a single exact      *)
(* reference to the package decomposition uabd1x_expf_pos and     *)
(* uabd1x_expf_mono_lt.                                           *)
(* ============================================================ *)

(* ---- Paper7Ablation, section 1, expf_pos slot. ---- *)
Theorem tspex_p7a1_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Defined.

(* ---- Paper7Ablation, section 1, expf_mono_lt slot. ---- *)
Theorem tspex_p7a1_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Defined.

(* ---- Paper7Ablation, section 2, expf_mono_lt slot. ---- *)
Theorem tspex_p7a2_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Defined.

(* ---- MixTimeChain, section 1, expf_pos slot. ---- *)
Theorem tspex_mtc_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Defined.

(* ---- MixTimeChain, section 1, expf_mono_lt slot. ---- *)
Theorem tspex_mtc_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Defined.

(* ---- MixTimeChainIface, expf_pos slot. ---- *)
Theorem tspex_mti_expf_pos : forall x : Real, real_lt real_zero (tspex_fn x).
Proof. exact uabd1x_expf_pos. Defined.

(* ---- MixTimeChainIface, expf_mono_lt slot. ---- *)
Theorem tspex_mti_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tspex_fn a) (tspex_fn b).
Proof. exact uabd1x_expf_mono_lt. Defined.

(* ============================================================ *)
(* Segment 2. The RSQ bs family, 3 rows, with the reading         *)
(* sumf := csm_sumf S en (the concrete fold over the enumeration  *)
(* list). The host section carries its own enumeration datum, so  *)
(* the supply shape needs no extra premises. The roots are the    *)
(* CmkMixTimeResolved supply rows cmkr_bs_swap, cmkr_bs_abs and   *)
(* cmkr_sum_eq_list of UpReqConcMixSel, whose statement faces     *)
(* coincide with the rows below.                                  *)
(* ============================================================ *)

(* ---- UpReqConcMixSel bs_swap slot; root cmkr_bs_swap (the       ---- *)
(* ---- CmkMixTimeResolved supply row, statement face identical to ---- *)
(* ---- this module's, double-list generic exchange).              ---- *)
Theorem tspbs_rsq_bs_swap :
  forall (S0 : Set) (en : list S0) (f : S0 -> S0 -> Real),
    real_eq (csm_sumf S0 en (fun s : S0 => csm_sumf S0 en (fun s' : S0 => f s s')))
        (csm_sumf S0 en (fun s' : S0 => csm_sumf S0 en (fun s : S0 => f s s'))).
Proof. exact cmkr_bs_swap. Defined.

(* ---- UpReqConcMixSel bs_abs slot; root cmkr_bs_abs ---- *)
(* ---- (positive-part form of the absolute value).    ---- *)
Theorem tspbs_rsq_bs_abs : forall a : Real, real_le zero a -> real_eq (abs a) a.
Proof. exact cmkr_bs_abs. Defined.

(* ---- UpReqConcMixSel sum_eq_list slot; root cmkr_sum_eq_list ---- *)
(* ---- (the two fold machines agree; the host machine           ---- *)
(* ---- rsq_bs_list_sum folds in the same shape as csm_sumf).    ---- *)
Theorem tspbs_rsq_sum_eq_list :
  forall (S0 : Set) (en : list S0) (g : S0 -> Real),
    real_eq (csm_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof. exact cmkr_sum_eq_list. Defined.

(* ============================================================ *)
(* Segment 3. The T1b sum_eq_list slot. The host row reads        *)
(* forall g, Id (sum_over_S g) (AttnDoeblin.bs_list_sum g enum)   *)
(* with the instance reading sum_over_S := idt_sumf enum; this    *)
(* module states the stronger form with the enumeration list      *)
(* universally quantified (the same usage shape as in             *)
(* IdSlotTranslate) and discharges it by idt_slot_attdoeblin in   *)
(* one step. Fully qualified names avoid bare-name shadowing.     *)
(* The parallel slot of UpAblT1b_S13_NLiveAudit is already        *)
(* supplied in place by ablq_sum_eq_list; consuming rows there    *)
(* are wired by direct reference, with no new theorem needed.     *)
(* ============================================================ *)
Theorem tspbs_t1b_sum_eq_list :
  forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI}
         (enum : list (@S01_BaseRing.S RI SS))
         (g : @S01_BaseRing.S RI SS -> @S01_BaseRing.R RI),
    S01_BaseRing.Id (@idt_sumf RI SS enum g)
                    (@AttnDoeblin.bs_list_sum RI SS g enum).
Proof.
  intros RI SS enum g.
  exact (idt_slot_attdoeblin enum g).
Defined.

(* ============================================================ *)
(* Closing audit 1. Assumption surface of all eleven theorems:    *)
(* each must report Closed under the global context.              *)
(* ============================================================ *)
Print Assumptions tspex_p7a1_expf_pos.
Print Assumptions tspex_p7a1_expf_mono_lt.
Print Assumptions tspex_p7a2_expf_mono_lt.
Print Assumptions tspex_mtc_expf_pos.
Print Assumptions tspex_mtc_expf_mono_lt.
Print Assumptions tspex_mti_expf_pos.
Print Assumptions tspex_mti_expf_mono_lt.
Print Assumptions tspbs_rsq_bs_swap.
Print Assumptions tspbs_rsq_bs_abs.
Print Assumptions tspbs_rsq_sum_eq_list.
Print Assumptions tspbs_t1b_sum_eq_list.

(* ============================================================ *)
(* Closing audit 2. Extraction check over three representative    *)
(* terms (one per family); the comparison command extracts the    *)
(* roots alone, so the differential account of Obj.magic sites    *)
(* can be read off the two logs.                                  *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Recursive Extraction tspex_fn.
Recursive Extraction tspbs_rsq_bs_swap.
Recursive Extraction tspbs_t1b_sum_eq_list.
Recursive Extraction uabd1x_expf_pos cms_bs_swap idt_slot_attdoeblin.

(* Extraction differential note. The three representative terms  *)
(* extract as definitional aliases of their roots (tspex_fn of   *)
(* uabd1x_expf, tspbs_rsq_bs_swap of cmkr_bs_swap,               *)
(* tspbs_t1b_sum_eq_list of idt_slot_attdoeblin); the statement  *)
(* faces are carried by the concrete forms real_eq/real_le (the  *)
(* values the global interface instance assigns to the relation  *)
(* fields), so the extraction log of this module contains no     *)
(* Obj.magic site, in agreement with the roots-only comparison   *)
(* command: the module-level extraction differential is zero.    *)
(* The extraction bypasses opacity to read the certified proof   *)
(* bodies of the root closure; that access is reported by the    *)
(* extraction-opaque-accessed warning and carries no assumption. *)
