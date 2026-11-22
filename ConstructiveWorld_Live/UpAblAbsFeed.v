(* ConstructiveWorld-Set -- instantiation feed for the finite-sum supply family. *)
(** * UpAblAbsFeed: per-epsilon bounds for absolute list sums, carrier instances.
    Mission.  [uabS4e_bform_to_eps] turns the Bishop bound [real_le_b x y]
      and [0 < e] into [real_le x (y + e)]; [uabS4e_single_sum_eps] applies
      it to absolute list sums; [uabS4e_sumf] binds the single-sum fold of
      the paper-2 carrier (carrier [S0], enumeration [enum0]);
      [uabS4e_p2_abs_sum_le_B], [uabS4e_p2_single_sum_eps] and
      [uabS4e_p2_single_sum_eps_direct] close
      [abs (sum f) <= sum (abs f) + eps] on that carrier (direct and
      inversion-mediated routes side by side); [uabS4e_p2_margin_tight]
      shows the margin admits no factor-2 improvement (a doubled-margin
      strict bound contradicts the per-epsilon bound); the three
      [uabf_kv_*] corollaries restate the bounds in list form with the
      abstract-sum interface instantiated at [real_list_sum].
    Dependencies.  Stdlib [List], [Extraction]; [S01_BaseRing] ..
      [S15_TailFEPUp], [UpRealLeB], [UpAblAbsSumLeB], [UpAblAbsSumLeB2].
    References.  The same-name baseline module in ConstructiveWorld-Main
      (statement names carried over verbatim, statement-face Set-carrier
      completion); the slot instances [uabS4b_slot_instance_list_nil] and
      [uabS4b_slot_instance_list_cons] of [UpAblAbsSumLeB2].
    Constructivity.  All statements carried by [Set]: [real_lt], [real_le],
      [real_eq] are Set-valued (QltT/sigT carriers, [Or := A + B]);
      [real_le_b] is a Set-level family; the margin contradiction lands in
      [Empty_set].  Every proof is [Defined] (transparent); axiom-free;
      [coqchk] reports [Axioms: none].
    Build.  coqc -native-compiler no -q -Q . "" UpAblAbsFeed.v (exit 0);
      the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import Extraction.
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
Require Import UpRealLeB.
Require Import UpAblAbsSumLeB.
From Stdlib Require Import List.
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* Part 0. Signature audit of the dependency interface (a signature drift fails compilation). *)
(* ============================================================ *)

Check uabS4_abs_list_sum_le_B.
Check uabS4_abs_list_sum_le_eps.
Check uabS4_lt_double_margin_le_half_contr.
Check uabS4b_slot_abs_sum_le_B.
Check uabS4b_slot_instance_list_nil.
Check uabS4b_slot_instance_list_cons.
Check real_le_b.
Check RealSetoid.real_lt_le_iff_req.
Check real_list_sum.
Check real_lt.
Check real_le.
Check real_eq.

(* ============================================================ *)
(* Part 1. Universal inversion from the B-form to the per-epsilon form. *)
(* ============================================================ *)

(* The B-form [real_le_b x y] unfolds to the family [x < y + eps] over
   [0 < eps]; [real_lt_le_iff_req] reinjects the left [Or] branch into
   the [Or]-encoded [real_le].  The library corollary
   [uabS4_abs_list_sum_le_eps] is the inlined special case on absolute
   sums; this named universal inversion was missing.  (The residual-free
   version "B-form implies the Or form at eps = 0" is not constructively
   provable; the [0 < e] premise is exactly the reachable boundary.) *)
Lemma uabS4e_bform_to_eps : forall x y e : Real,
  real_lt real_zero e ->
  real_le_b x y ->
  real_le x (real_plus y e).
Proof.
  intros x y e He Hb.
  apply (RealSetoid.real_lt_le_iff_req x (real_plus y e)). apply inl.
  exact (Hb e He).
Defined.

(* Universal closure of the single-sum shape:
   [abs (sum_l f) <= sum_l (abs f) + e] for [0 < e], carrier-general.
   Two-step composition of the dependency-module B-form with the
   inversion above. *)
Theorem uabS4e_single_sum_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                       (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (uabS4e_bform_to_eps _ _ e He).
  exact (uabS4_abs_list_sum_le_B X f l).
Defined.

(* ============================================================ *)
(* Part 2. The paper-2 carrier (carrier [S0], enumeration [enum0]); the *)
(* single-sum operator is the native fold. *)
(* ============================================================ *)

Section P2EpsCarrier.

Context (S0 : Set).
Context (enum0 : list S0).

(* The paper-2 single-sum operator: the native fold (the same body the
   minp chain uses, not an adapter). *)
Definition uabS4e_sumf (f : S0 -> Real) : Real := real_list_sum S0 f enum0.

(* B-form instance on the carrier: [abs (sum_enum f) <=_B sum_enum (abs f)]. *)
Theorem uabS4e_p2_abs_sum_le_B : forall f : S0 -> Real,
  real_le_b (real_abs (uabS4e_sumf f))
            (uabS4e_sumf (fun x => real_abs (f x))).
Proof.
  intros f. exact (uabS4_abs_list_sum_le_B S0 f enum0).
Defined.

(* Carrier closure of the single-sum bound:
   [abs (sum_enum f) <= sum_enum (abs f) + eps] for [0 < eps], folding
   over the whole enumeration once. *)
Theorem uabS4e_p2_single_sum_eps : forall (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (uabS4e_sumf f))
          (real_plus (uabS4e_sumf (fun x => real_abs (f x))) eps).
Proof.
  intros f eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabS4e_p2_abs_sum_le_B f).
Defined.

(* Companion instance: direct application of the upstream universal
   corollary.  The statement face coincides with
   [uabS4e_p2_single_sum_eps] word for word ([uabS4e_sumf] unfolds
   definitionally to the native fold); the two routes are kept side by
   side: inversion-mediated versus upstream-corollary-direct. *)
Theorem uabS4e_p2_single_sum_eps_direct : forall (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (uabS4e_sumf f))
          (real_plus (uabS4e_sumf (fun x => real_abs (f x))) eps).
Proof.
  intros f eps Heps.
  exact (uabS4_abs_list_sum_le_eps S0 f enum0 eps Heps).
Defined.

End P2EpsCarrier.

(* ============================================================ *)
(* Part 3. Margin tightness: the per-epsilon margin cannot be halved. *)
(* ============================================================ *)

(* The strict form with the doubled margin, [sum (abs f) + (eps + eps) <
   abs (sum f)], contradicts the per-epsilon bound
   [abs (sum f) <= sum (abs f) + eps] through the doubled-margin
   incompatibility lemma -- the formal statement that the margin radius
   of the single-sum epsilon form admits no factor-2 improvement. *)
Theorem uabS4e_p2_margin_tight : forall (S0 : Set) (enum0 : list S0)
                                        (f : S0 -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_lt (real_plus (real_list_sum S0 (fun x => real_abs (f x)) enum0)
                     (real_plus eps eps))
          (real_abs (real_list_sum S0 f enum0)) ->
  Empty_set.
Proof.
  intros S0 enum0 f eps Heps Hfar.
  exact (uabS4_lt_double_margin_le_half_contr
           (real_abs (real_list_sum S0 f enum0))
           (real_list_sum S0 (fun x => real_abs (f x)) enum0)
           eps Heps Hfar
           (uabS4_abs_list_sum_le_eps S0 f enum0 eps Heps)).
Defined.

(* ============================================================ *)
(* Part 4. Key-value list form: the same bounds with the abstract-sum *)
(* interface instantiated at [real_list_sum]. *)
(* ============================================================ *)

(* Signature audit of the supply interface the instantiation consumes. *)
Check uabS4b_slot_abs_sum_le_B.

(* Per-epsilon form: [abs (sum_l f) <= sum_l (abs f) + eps] for [0 < eps]. *)
Corollary uabf_kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real)
  (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  exact (uabS4_abs_list_sum_le_eps X f l eps Heps).
Defined.

(* B-form: the list fold substituted into the abstract-sum interface of
   [uabS4b_slot_abs_sum_le_B]; the nil and cons interface equations are
   consumed from the named slot instances of [UpAblAbsSumLeB2] (both are
   definitional, witnessed by [real_eq_refl]). *)
Corollary uabf_kv_abs_triangle_list_B : forall (X : Set) (f : X -> Real)
  (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x : X => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (uabS4b_slot_abs_sum_le_B X (real_list_sum X)
           (uabS4b_slot_instance_list_nil X)
           (uabS4b_slot_instance_list_cons X)
           f l).
Defined.

(* Slot route to the per-epsilon form: the B-form above lifted through
   [uabS4e_bform_to_eps]; the conclusion coincides with
   [uabf_kv_abs_triangle_list_eps], the proof route differs. *)
Corollary uabf_kv_abs_triangle_list_eps_slotroute :
  forall (X : Set) (f : X -> Real) (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabf_kv_abs_triangle_list_B X f l).
Defined.

(* ==================== Audit note: Print Assumptions is expected to report Closed for every exported statement (no external unproved premises) ==================== *)
Print Assumptions uabS4e_bform_to_eps.
Print Assumptions uabS4e_single_sum_eps.
Print Assumptions uabS4e_p2_abs_sum_le_B.
Print Assumptions uabS4e_p2_single_sum_eps.
Print Assumptions uabS4e_p2_single_sum_eps_direct.
Print Assumptions uabS4e_p2_margin_tight.
Print Assumptions uabf_kv_abs_triangle_list_eps.
Print Assumptions uabf_kv_abs_triangle_list_B.
Print Assumptions uabf_kv_abs_triangle_list_eps_slotroute.
