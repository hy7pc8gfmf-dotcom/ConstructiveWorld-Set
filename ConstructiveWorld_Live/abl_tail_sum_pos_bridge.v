(* ConstructiveWorld-Set — sum_pos slot-carrier bridge family, witness-passed form. *)

(** * abl_tail_sum_pos_bridge: sigT-witness input extensions of the sum_pos slot family.

    Mission.  Four statements, one per slot carrier, each turning a Set-level
      nonemptiness witness [sigT (fun t => InT t en)] into strict positivity
      of a finite sum: (1) [tspb_sum_pos_slot_of_carrier_agree], the
      abstract-operator slot face (pointwise [req]-agreement with the
      enumerated list sum); (2) [tspb_ems_sum_pos_preserved_witness] at the
      concrete-softmax fold [csm_sumf]; (3) [tspb_tsi_Hsum_pos_witness], the
      TSI sums-machine slot face at [sumd_sumf]; (4) [tspb_slc_sumpos_witness]
      at the Real-layer fold [real_list_sum].
    Dependencies.  Stdlib [List], [Extraction]; [S01_BaseRing] through
      [S15_TailFEPUp], [UpReqSumD], [UpReqConcSoftmax],
      [PA_TempSoftmaxInstantiation] of this development.
    References.  The ConstructiveWorld-Main baseline module whose statement
      names are carried over verbatim (statement-face Set-carrier completion);
      the in-tree adaptation precedent [abl_tail_pos_certs.v]; the roots
      [sumd_sum_pos] and [sumd_list_sum_pos] (UpReqSumD) and
      [real_list_sum_pos] (S08).
    Constructivity.  Set-carried throughout: nonemptiness is an [InT] witness,
      [req]/[lt] are the Set-valued global twins [real_eq]/[real_lt] (the
      zero-argument interface class resolves through its global instance);
      nil branches close by [InT]-elimination; no admission vocabulary; no
      classical axioms; statements extract with [Obj.magic] = 0.
    Build.  [coqc -native-compiler no -q -Q <single development root> ""
      abl_tail_sum_pos_bridge.v] compiles cleanly (exit 0); the artifact
      starts with the bytes [436f7121 000160bc]. *)

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
Require Import PA_TempSoftmaxInstantiation.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Interface adaptation: the interface class of this tree is unparameterized;
   its carrier is the global Real (the zero-argument Class
   RealInterfaceEnhancedSetoid plus the global Instance RealEnhancedReal).
   The parameterized binders forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R}
   of the baseline are removed from the statement faces; the used field names
   resolve through the concrete global twins below (the bindings the global
   instance assigns), spelled with the Abbreviation vernacular of the
   abl_tail_pos_certs precedent.  Statement names are unchanged apart from
   the dropped binder arguments. *)
Abbreviation req := real_eq.
Abbreviation zero := real_zero.
Abbreviation lt := real_lt.

(* Empty-membership eliminator: no constructor of [InT] applies at the nil
   index, so the Set-level contradiction is built by inversion; the
   extracted face is a direct absurd-case marker with no informative
   pattern matching (Obj.magic-free). *)
Definition tspb_inT_nil_empty (S : Set) (x : S) (H : InT x nil) : Empty_set.
Proof. inversion H. Defined.

(* Duplication review (no repeated supply statements; whole-library grep):  *)
(*   The generic-enumeration sum_pos faces below are new in this tree:      *)
(*   (1) the abstract-operator face adds the carrier-agreement premise over *)
(*   an arbitrary operator, the slot-form input pattern of                  *)
(*   [tspp_sum_zero_nonneg_slot_of_carrier_agree] (abl_tail_pos_certs);     *)
(*   (2)-(3) the generic-en faces at the [csm_sumf] and [sumd_sumf]         *)
(*   carriers differ in the nonemptiness carrier from the in-service        *)
(*   negation-premise forms [uabT1_rte_fsum_pos] (UpAblT1_UpReqTempEntropy: *)
(*   Not (enum = nil)) and [sumd_sum_pos] (UpReqSumD, consumed in the       *)
(*   proofs): here nonemptiness is the Set-level [InT] witness itself;      *)
(*   (4) the [real_list_sum] face differs from [real_list_sum_pos]          *)
(*   (S08_RealMainlineDPO, consumed in the proof: premise [l <> nil]) by    *)
(*   the same witness-passed nonemptiness.  The cons-witness forms          *)
(*   [tspps_uralign_sum_pos_cons] (abl_tail_pos_supply_sum) fix a cons      *)
(*   head and stay at their own slots.  No same-statement match exists.     *)

(* Section 1.  Abstract-operator slot face: a summation operator that      *)
(*   agrees pointwise with the enumerated list sum under [req] carries the *)
(*   slot proposition, with the nonemptiness slot passed as a [sigT]       *)
(*   witness over [InT].  The sumd branch delegates to the negation-       *)
(*   premise form [sumd_sum_pos] (UpReqSumD); its nonemptiness premise is  *)
(*   discharged constructively from the witness (an [InT] witness rules    *)
(*   out [en = nil] on the Stdlib equality), which keeps the extraction    *)
(*   face free of informative elimination of the empty membership slot.    *)
Theorem tspb_sum_pos_slot_of_carrier_agree :
  forall (S : Set) (sumf : (S -> Real) -> Real) (en : list S),
    sigT (fun t : S => InT t en) ->
    (forall f : S -> Real, req (sumf f) (sumd_sumf S en f)) ->
    forall f : S -> Real, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Proof.
  intros S sumf en W Hagree f Hpt.
  apply (lt_id_r zero (sumd_sumf S en f) (sumf f)).
  - exact (req_sym (sumf f) (sumd_sumf S en f) (Hagree f)).
  - apply (sumd_sum_pos S en f).
    + intro Heq. destruct W as [x Hx]. rewrite Heq in Hx.
      exact (tspb_inT_nil_empty S x Hx).
    + exact Hpt.
Defined.

(* Section 2.  EMS slot carrier: the concrete-softmax fold [csm_sumf]      *)
(*   (UpReqConcSoftmax) at the generic enumeration, witness-passed form;   *)
(*   the fold reduces definitionally to the list-sum machine, whose        *)
(*   negation-premise form [sumd_list_sum_pos] takes the witness-derived   *)
(*   nonemptiness.                                                         *)
Theorem tspb_ems_sum_pos_preserved_witness :
  forall (S : Set) (en : list S),
    sigT (fun t : S => InT t en) ->
    forall f : S -> Real,
      (forall s : S, real_lt real_zero (f s)) ->
      real_lt real_zero (csm_sumf S en f).
Proof.
  intros S en W f Hpt.
  unfold csm_sumf.
  apply (sumd_list_sum_pos S f en).
  - intro Heq. destruct W as [x Hx]. rewrite Heq in Hx.
    exact (tspb_inT_nil_empty S x Hx).
  - exact Hpt.
Defined.

(* Section 3.  TSI slot face: the sums-machine slot [Hsum_pos] of          *)
(*   PA_TempSoftmaxInstantiation (the bridge instance [tsi_rie_setoid]     *)
(*   re-anchors to the canonical global instance in this tree), at the     *)
(*   [sumd_sumf] operator, generic enumeration, witness-passed form.       *)
Section TspbTsiPosSlotFeed.

Variable Token : Set.
Variable en : list Token.

Theorem tspb_tsi_Hsum_pos_witness :
  sigT (fun t : Token => InT t en) ->
  forall f : Token -> Real,
    (forall w : Token, lt zero (f w)) -> lt zero (sumd_sumf Token en f).
Proof.
  intros W f Hpt.
  apply (sumd_sum_pos Token en f).
  - intro Heq. destruct W as [x Hx]. rewrite Heq in Hx.
    exact (tspb_inT_nil_empty Token x Hx).
  - exact Hpt.
Defined.

End TspbTsiPosSlotFeed.

(* Section 4.  slc slot carrier: the Real-layer fold [real_list_sum]       *)
(*   (S08_RealMainlineDPO) at the generic enumeration; the fold-positivity *)
(*   root takes a nonemptiness premise, discharged constructively from the *)
(*   [InT] witness.                                                        *)
Theorem tspb_slc_sumpos_witness :
  forall (S : Set) (en : list S),
    sigT (fun t : S => InT t en) ->
    forall f : S -> Real,
      (forall s : S, real_lt real_zero (f s)) ->
      real_lt real_zero (real_list_sum S f en).
Proof.
  intros S en W f Hpt.
  destruct W as [x Hx].
  apply (real_list_sum_pos S f en Hpt).
  intro Heq.
  rewrite Heq in Hx.
  exact (match Hx with end).
Defined.

(* Section 5.  Assumption audit: Print Assumptions at every named exit,    *)
(*   each Closed under the global context; the name list and the Defined   *)
(*   count agree at 4.                                                     *)
Check sumd_sumf.
Check csm_sumf.
Check real_list_sum.
Check tsi_rie_setoid.
Check lt_id_r.
Check sumd_list_sum_pos_cons.
Print Assumptions tspb_sum_pos_slot_of_carrier_agree.
Print Assumptions tspb_ems_sum_pos_preserved_witness.
Print Assumptions tspb_tsi_Hsum_pos_witness.
Print Assumptions tspb_slc_sumpos_witness.

(* Section 6.  Extraction probe: one single-command pass over all four     *)
(*   names (a multi-command driver would silently keep only the last       *)
(*   command's output); this in-file pass prints the extracted terms to    *)
(*   the build log, and the delivery-face extraction runs through a        *)
(*   Separate Extraction driver against the built artifact.                *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspb_sum_pos_slot_of_carrier_agree
  tspb_ems_sum_pos_preserved_witness tspb_tsi_Hsum_pos_witness
  tspb_slc_sumpos_witness.
