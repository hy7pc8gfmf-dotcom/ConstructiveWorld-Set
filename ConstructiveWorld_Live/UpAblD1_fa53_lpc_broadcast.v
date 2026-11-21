(* ConstructiveWorld-Set -- strict/non-strict mixed monotonicity of addition,
   broadcast at nine name-prefixed substitution slots. *)

(** * UpAblD1_fa53_lpc_broadcast: the mixed monotonicity of addition, one
    statement per downstream assumption slot, closed by substitution.

    Mission.  Nine reference statements [uabd1_*] of the family
      lt a b -> le c d -> lt (plus a c) (plus b d) and its le/lt mirror:
      one in-section over the {RI}{DO} context, eight with [RI0]/[DO0]
      explicit.

    Dependencies.  The Require lines below: [S01_BaseRing] through
      [S15_TailFEPUp], [fa53_compat_abs] (the supply theorems), and
      [TempSoftmaxInstantiation].

    References.  Supply theorems fa53_compat_abs.v:117 and :137; consumer
      statement slots UpReqCauchy.v:123-124, UpReqAttnIter.v:147/:149,
      UpReqConcMixSel.v:75/:736/:771, UpReqAttnGibbs.v:1198, and
      UpReqAttnMixTime.v:104; tree-face re-anchor per the in-tree precedents
      UpAblD1S2_e752_UpReqAttnIter.v / UpAblD1S3_fep_UpReqAttnGibbs.v.

    Constructivity.  Statements are Set-carried (order predicates are
      Set-valued interface fields; no Prop statement faces).  The per-carrier
      setoid bridge is zero-argument in this tree, so the argumented setoid
      applications re-anchor to the interface fields of [RI0]; all statements
      close under the global context, exported transparent (Defined).

    Build.  [coqc -Q <single-root .vo world> "" -o
      UpAblD1_fa53_lpc_broadcast.vo UpAblD1_fa53_lpc_broadcast.v] (Rocq 9.1.0)
      against the read-only dependency .vo world; artifact starts [436f7121]. *)

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
Require Import fa53_compat_abs.
Require TempSoftmaxInstantiation.

(* Slot 9: the interface statement form of UpReqAttnMixTime.v:104, stated
   inside a section over the {RI}{DO} context with the interface fields
   bare (the Id-carrier face). *)
Section UabD1LpcBroadcast.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Theorem uabd1_upreqattnmixtime_bs_lpc :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (fa53_lt_plus_compat_lt_le_dec a b c d Hab Hcd).
Defined.

End UabD1LpcBroadcast.

(* Slots 1-8: the req-carrier (RealInterfaceEnhancedSetoid) statement forms
   of the downstream slots.  Tree-face re-anchor (per the in-tree precedents
   UpAblD1S2_e752_UpReqAttnIter.v / UpAblD1S3_fep_UpReqAttnGibbs.v; the
   assembly instance is documented in PA_TempSoftmaxInstantiation): the class
   RealInterfaceEnhancedSetoid is zero-argument in this tree (its fields live
   at the global Real/real_eq carrier) and its bridge instance takes no
   carrier argument, so the argumented setoid applications of the upstream
   statement faces read as the interface fields of RI0 over the carrier
   @S01_BaseRing.R RI0; each statement is supplied verbatim by the
   discharged face of the matching fa53 supply theorem. *)

(* Slot 1 (UpReqCauchy.v:123). *)
Theorem uabd1_upreqcauchy_lt_plus_compat_lt_le :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 2 (UpReqCauchy.v:124, le/lt mirror). *)
Theorem uabd1_upreqcauchy_lt_plus_compat_le_lt :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.le RI0 a b ->
    @S01_BaseRing.lt RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_le_lt_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 3 (UpReqAttnIter.v:147). *)
Theorem uabd1_upreqattniter_lt_plus_compat_lt_le_i :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 4 (UpReqAttnIter.v:149, le/lt mirror). *)
Theorem uabd1_upreqattniter_lt_plus_compat_le_lt_i :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.le RI0 a b ->
    @S01_BaseRing.lt RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_le_lt_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 5 (UpReqConcMixSel.v:75, Section CmkMixSelect). *)
Theorem uabd1_upreqconcmixsel_s2_lt_plus_compat_lt_le :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 6 (UpReqConcMixSel.v:736, Section CmkMixTime). *)
Theorem uabd1_upreqconcmixsel_cmt_lt_plus_compat_lt_le :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 7 (UpReqConcMixSel.v:771). *)
Theorem uabd1_upreqconcmixsel_bs_lpc :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Slot 8 (UpReqAttnGibbs.v:1198). *)
Theorem uabd1_upreqattngibbs_req_lt_plus_compat_lt_le_h :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Defined.

(* Assumption audit tail: each statement must read
   [Closed under the global context]. *)
Print Assumptions uabd1_upreqattnmixtime_bs_lpc.
Print Assumptions uabd1_upreqcauchy_lt_plus_compat_lt_le.
Print Assumptions uabd1_upreqcauchy_lt_plus_compat_le_lt.
Print Assumptions uabd1_upreqattniter_lt_plus_compat_lt_le_i.
Print Assumptions uabd1_upreqattniter_lt_plus_compat_le_lt_i.
Print Assumptions uabd1_upreqconcmixsel_s2_lt_plus_compat_lt_le.
Print Assumptions uabd1_upreqconcmixsel_cmt_lt_plus_compat_lt_le.
Print Assumptions uabd1_upreqconcmixsel_bs_lpc.
Print Assumptions uabd1_upreqattngibbs_req_lt_plus_compat_lt_le_h.
