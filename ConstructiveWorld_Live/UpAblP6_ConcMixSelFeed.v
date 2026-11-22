(* ==================================================================== *)
(*  UpAblP6_ConcMixSelFeed.v -- concrete-point instances of the          *)
(*  conc/mix/select interface on enumerated carriers.                    *)
(*  Mission.  Nineteen uacms_-prefixed pieces: three concrete data       *)
(*    definitions (the unit enumeration, the two-point bool enumeration, *)
(*    the two-branch folded function taking one on true and zero on      *)
(*    false) and sixteen instance certificates instantiating generic     *)
(*    ConcMixSelFeed pieces at those points: fold evaluation             *)
(*    companions, the order certificate le zero one, four sum-law        *)
(*    instances, two lt_plus instances at distinct points, the double    *)
(*    exchange and folding bridges on the two-point world, and the       *)
(*    companions on abs and lt_plus.  Statement names are listed at      *)
(*    their bodies below.                                                *)
(*  Dependencies.  S01_BaseRing..S15_TailFEPUp, UpReqSumD,               *)
(*    UpReqConcSoftmax, UpReqSampling, UpReqConcMixSel, UpReqConcB1,     *)
(*    ConcMixSelFeed, Stdlib List.  RealInterfaceEnhancedSetoid is       *)
(*    the argument-less Class of module RealInterfaceEnhancedMod         *)
(*    (S07_RealSetoidExpLog.v) with global Instance RealEnhancedReal;    *)
(*    req/lt/le are pinned by Notation to the concrete S02 carriers      *)
(*    real_eq/real_lt/real_le (ConcMixSelFeed carrier-binding form).     *)
(*  References.  The req-layer instance family of the sum/mix/select     *)
(*    interface: instantiation at concrete enumerated carriers.          *)
(*  Constructivity.  Statements ride the Set layer (req/le/lt/Id are     *)
(*    Set-valued; zero Prop statements); zero classical logic; zero      *)
(*    admitted literals; every proof ends in Defined.                    *)
(*  Build.  Rocq 9.3, coqc -Q <Set world> "" (cpu_guard wrapped);        *)
(*    Separate Extraction over all nineteen names, ocamlc compile,       *)
(*    sample driver run realizing the promised witness content.          *)
(* ==================================================================== *)

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
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import ConcMixSelFeed.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Carrier binding of the statement-face relation fields: req/lt/le are  *)
(* bound by Notation directly to the concrete S02_CauchyComplete forms   *)
(* real_eq/real_lt/real_le -- the informative bindings the global        *)
(* instance RealEnhancedReal assigns to these class fields, so no        *)
(* statement elaborates to a boxed class-field projection (which would   *)
(* extract as an erased type face).                                      *)
Notation lt := real_lt.
Notation req := real_eq.
Notation le := real_le.

(* =================== concrete enumerated data ======================== *)

(* Unit enumeration: S0 := unit, en := [tt]; the minimal nonempty carrier. *)
Definition uacms_en_unit : list unit := [tt].

(* Two-point enumeration: S0 := bool, en := [true; false]; the minimal   *)
(* multi-point carrier, keeping the bs_swap and sum_eq_list instances    *)
(* non-degenerate (a single point would make both arms convertible).     *)
Definition uacms_en_bool : list bool := [true; false].

(* Two-variable asymmetric folded function: the true branch yields one,  *)
(* the false branch yields zero, so the two double-folding arms          *)
(* (fun s => f s s') and (fun s' => f s' s) are not convertible and the  *)
(* exchange instance stays informative.                                  *)
Definition uacms_mix_f (b1 b2 : bool) : Real := if b1 then one else zero.

(* =============== evaluation companions of the concrete folds ========= *)

(* The unit fold unfolds definitionally to plus one zero: csm_sumf folds *)
(* along sumd_list_sum, so the single data point reduces by iota/beta.   *)
Theorem uacms_sumf_unit_eval :
  Id (csm_sumf unit uacms_en_unit (fun _ : unit => one)) (plus one zero).
Proof.
  exact (@id_refl _ (plus one zero)).
Defined.

(* The concrete fold normalizes through the field law plus_zero: the     *)
(* canonical value of the finite unit sum is one.                        *)
Theorem uacms_sumf_unit_norm :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => one)) one.
Proof.
  exact (plus_zero one).
Defined.

(* The two-point fold of the constant one evaluates to                  *)
(* plus one (plus one zero).                                             *)
Theorem uacms_sumf_bool_eval :
  Id (csm_sumf bool uacms_en_bool (fun _ : bool => one))
     (plus one (plus one zero)).
Proof.
  exact (@id_refl _ (plus one (plus one zero))).
Defined.

(* The second folding machine reaches the same literal sum on the same   *)
(* data: both arms of the sum_eq_list instance agree by evaluation.      *)
Theorem uacms_rsq_bool_eval :
  Id (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool)
     (plus one (plus one zero)).
Proof.
  exact (@id_refl _ (plus one (plus one zero))).
Defined.

(* =============== concrete order certificates ========================= *)

(* le zero one by the strict branch of lt_le_iff injected with one_pos.  *)
Theorem uacms_zero_le_one : le zero one.
Proof.
  exact (lt_le_iff zero one (inl one_pos)).
Defined.

(* =============== sum-law instances on the unit world ================== *)

(* Extensionality at the constant point: the pointwise premise holds by  *)
(* req_sym composed with plus_zero, and the conclusion relates two       *)
(* folds whose arms are not convertible (plus one zero versus           *)
(* plus (plus one zero) zero).                                           *)
Theorem uacms_sum_ext_unit_one :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => one))
      (csm_sumf unit uacms_en_unit (fun _ : unit => plus one zero)).
Proof.
  exact (cms_sum_ext unit uacms_en_unit
           (fun _ : unit => one) (fun _ : unit => plus one zero)
           (fun _ : unit => req_sym (plus one zero) one (plus_zero one))).
Defined.

(* Linearity at the scalar one: multiplying each summand by one and      *)
(* multiplying the sum by one agree as folds, non-trivially.             *)
Theorem uacms_sum_linear_unit :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => mult one one))
      (mult one (csm_sumf unit uacms_en_unit (fun _ : unit => one))).
Proof.
  exact (cms_sum_linear unit uacms_en_unit one (fun _ : unit => one)).
Defined.

(* Additivity of the constant-one fold with itself at the single point.  *)
Theorem uacms_sum_add_unit :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => plus one one))
      (plus (csm_sumf unit uacms_en_unit (fun _ : unit => one))
            (csm_sumf unit uacms_en_unit (fun _ : unit => one))).
Proof.
  exact (cms_sum_add unit uacms_en_unit
           (fun _ : unit => plus one one) (fun _ : unit => one)).
Defined.

(* Monotonicity: the zero fold is bounded by the one fold, pointwise     *)
(* certificate given by uacms_zero_le_one.                               *)
Theorem uacms_sum_le_unit :
  le (csm_sumf unit uacms_en_unit (fun _ : unit => zero))
     (csm_sumf unit uacms_en_unit (fun _ : unit => one)).
Proof.
  exact (cms_sum_le unit uacms_en_unit
           (fun _ : unit => zero) (fun _ : unit => one)
           (fun _ : unit => uacms_zero_le_one)).
Defined.

(* =============== lt_plus instances at two distinct points ============= *)

(* Selection-node shape at (a, b, c, d) := (zero, one, zero, zero):      *)
(* strict inequality plus reflexivity give lt (plus zero zero)           *)
(* (plus one zero).                                                      *)
Theorem uacms_lt_plus_sel_unit :
  lt (plus zero zero) (plus one zero).
Proof.
  exact (cms_lt_plus_compat_lt_le_sel zero one zero zero
           one_pos (le_refl zero)).
Defined.

(* Time-node shape at (a, b, c, d) := (zero, one, one, one): the second  *)
(* lt_plus node form, reachable at a different concrete point.           *)
Theorem uacms_lt_plus_time_point :
  lt (plus zero one) (plus one one).
Proof.
  exact (cms_lt_plus_compat_lt_le_time zero one one one
           one_pos (le_refl one)).
Defined.

(* =============== double exchange and folding bridges ================== *)

(* The double fold of uacms_mix_f over the two-point world exchanges its *)
(* two arms: the arms are not convertible, so the instance consumes the  *)
(* generic double-list exchange induction.                               *)
Theorem uacms_bs_swap_bool :
  req (csm_sumf bool uacms_en_bool
         (fun s : bool => csm_sumf bool uacms_en_bool
            (fun s' : bool => uacms_mix_f s s')))
      (csm_sumf bool uacms_en_bool
         (fun s' : bool => csm_sumf bool uacms_en_bool
            (fun s : bool => uacms_mix_f s s'))).
Proof.
  exact (cms_bs_swap bool uacms_en_bool uacms_mix_f).
Defined.

(* The two folding machines agree on the constant-one function over the  *)
(* two-point world; the evaluation companions above already exhibit the  *)
(* common value plus one (plus one zero).                                *)
Theorem uacms_sum_eq_list_bool :
  req (csm_sumf bool uacms_en_bool (fun _ : bool => one))
      (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool).
Proof.
  exact (cms_sum_eq_list bool uacms_en_bool (fun _ : bool => one)).
Defined.

(* The folding adapter itself, applied on the two-point list: both       *)
(* machines fold nil to zero and cons to plus of head and tail.          *)
Theorem uacms_fold_shim_bool :
  req (sumd_list_sum bool (fun _ : bool => one) uacms_en_bool)
      (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool).
Proof.
  exact (cms_fold_req_list_sum bool (fun _ : bool => one) uacms_en_bool).
Defined.

(* =============== companions at the concrete points ==================== *)

(* The absolute-value companion at one: premised on the order            *)
(* certificate above.                                                    *)
Theorem uacms_bs_abs_one : req (abs one) one.
Proof.
  exact (cms_bs_abs one uacms_zero_le_one).
Defined.

(* The lt_plus companion of the adjacent family, at the same point as    *)
(* the selection-node instance above.                                    *)
Theorem uacms_bs_lpc_unit :
  lt (plus zero zero) (plus one zero).
Proof.
  exact (cms_bs_lpc zero one zero zero one_pos (le_refl zero)).
Defined.

(* =============== assumption audit (per-piece Closed) ================== *)

Print Assumptions uacms_sumf_unit_eval.
Print Assumptions uacms_sumf_unit_norm.
Print Assumptions uacms_sumf_bool_eval.
Print Assumptions uacms_rsq_bool_eval.
Print Assumptions uacms_zero_le_one.
Print Assumptions uacms_sum_ext_unit_one.
Print Assumptions uacms_sum_linear_unit.
Print Assumptions uacms_sum_add_unit.
Print Assumptions uacms_sum_le_unit.
Print Assumptions uacms_lt_plus_sel_unit.
Print Assumptions uacms_lt_plus_time_point.
Print Assumptions uacms_bs_swap_bool.
Print Assumptions uacms_sum_eq_list_bool.
Print Assumptions uacms_fold_shim_bool.
Print Assumptions uacms_bs_abs_one.
Print Assumptions uacms_bs_lpc_unit.
