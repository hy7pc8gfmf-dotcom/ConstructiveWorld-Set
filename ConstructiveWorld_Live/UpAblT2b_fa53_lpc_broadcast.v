(* ConstructiveWorld-Set -- strict/non-strict mixed monotonicity of addition,
   broadcast at eleven name-prefixed substitution slots. *)
(** * UpAblT2b_fa53_lpc_broadcast: the mixed monotonicity of addition, one
    reference statement per downstream assumption slot.
    Mission.  Eleven statements [uabt2b_*] of the family lt a b -> le c d ->
      lt (plus a c) (plus b d) and its le/lt mirror: eight in-section over
      the {RI}{DO} context, one with [RI0]/[DO0] explicit.  Each proof joins
      the non-strict branch [le_plus_compat] (reflexivity on the shared
      summand), the strict one-sided translation [fa53_lt_plus_translate_r]/
      [_l], and [le_lt_trans] in the direction the strict summand requires;
      the trichotomy decomposition and its decidable-order data slot are
      dropped, narrowing the dependency face.
    Dependencies.  The Require lines below: [S01_BaseRing] through
      [S15_TailFEPUp], [fa53_compat_abs] (the strict-translation supply),
      and [TempSoftmaxInstantiation].
    References.  Consumer slots: S04_RealExpLogConv.v:285/:286,
      S06_DiffSamplingGibbs.v:4018/:4019, S05_AlignmentGRPO.v:2308/:2310,
      S13_NLiveAudit.v:2349, UpEntropyGain.v:86, UpFirewall.v:107,
      UpReqAlgebra.v:1474, AttnDoeblin.v:158; supply face
      fa53_compat_abs.v:90/:102; re-anchor precedents
      UpAblD1_fa53_lpc_broadcast.v / UpAblD1S2_e752_UpReqAttnIter.v.
    Constructivity.  Statements are Set-carried (order predicates are
      Set-valued interface fields; no Prop statement faces).  The
      per-carrier setoid bridge is zero-argument in this tree, so the
      argumented setoid applications of the req-carrier slot re-anchor to
      the interface fields of [RI0]; all statements close under the global
      context, exported transparent (Defined).
    Build.  [coqc -Q <single-root .vo world> "" UpAblT2b_fa53_lpc_broadcast.v]
      (Rocq 9.1.0) against the read-only dependency .vo world; artifact
      starts [436f7121 000160bc]. *)
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

Section UabT2bLpcBroadcast.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* Slot 1 (S04_RealExpLogConv.v:285, strict premise first). *)
Theorem uabt2b_s04_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 2 (S04_RealExpLogConv.v:286, le/lt mirror). *)
Theorem uabt2b_s04_lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus b c) (plus b d)
           (le_plus_compat a b c c Hab (le_refl c))
           (fa53_lt_plus_translate_l c d b Hcd)).
Defined.

(* Slot 3 (S06_DiffSamplingGibbs.v:4018). *)
Theorem uabt2b_s06_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 4 (S06_DiffSamplingGibbs.v:4019, le/lt mirror). *)
Theorem uabt2b_s06_lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus b c) (plus b d)
           (le_plus_compat a b c c Hab (le_refl c))
           (fa53_lt_plus_translate_l c d b Hcd)).
Defined.

(* Slot 5 (S05_AlignmentGRPO.v:2308, le/lt mirror first). *)
Theorem uabt2b_s05_lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus b c) (plus b d)
           (le_plus_compat a b c c Hab (le_refl c))
           (fa53_lt_plus_translate_l c d b Hcd)).
Defined.

(* Slot 6 (S05_AlignmentGRPO.v:2310). *)
Theorem uabt2b_s05_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 7 (S13_NLiveAudit.v:2349, two-line statement form). *)
Theorem uabt2b_s13_lt_plus_compat_lt_le_h :
  forall a b c d : R,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 8 (UpEntropyGain.v:86, two-line statement form). *)
Theorem uabt2b_upentropygain_lt_plus_compat_lt_le :
  forall a b c d : R,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 9 (UpFirewall.v:107, two-line statement form). *)
Theorem uabt2b_upfirewall_lt_plus_compat_lt_le :
  forall a b c d : R,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

(* Slot 10 (AttnDoeblin.v:158, two-line statement form). *)
Theorem uabt2b_attndoeblin_lt_plus_compat_lt_le_h :
  forall a b c d : R,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (le_lt_trans (plus a c) (plus a d) (plus b d)
           (le_plus_compat a a c d (le_refl a) Hcd)
           (fa53_lt_plus_translate_r a b d Hab)).
Defined.

End UabT2bLpcBroadcast.

(* Slot 11: the req-carrier statement form of UpReqAlgebra.v:1474, exiting
   the section with the carrier and order instance explicit.  Tree-face
   re-anchor (per the in-tree precedents UpAblD1_fa53_lpc_broadcast.v and
   UpAblD1S2_e752_UpReqAttnIter.v; the assembly instance is documented in
   PA_TempSoftmaxInstantiation): the per-carrier setoid bridge is
   zero-argument in this tree, so the argumented setoid applications of the
   upstream statement face read as the interface fields of [RI0] over the
   carrier @S01_BaseRing.R RI0. *)
Theorem uabt2b_upreqalgebra_req_lt_plus_compat_lt_le :
  forall (RI0 : RealInterfaceEnhanced) (DO0 : DecidableOrder RI0)
         (a b c d : @S01_BaseRing.R RI0),
    @S01_BaseRing.lt RI0 a b ->
    @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c)
                         (@S01_BaseRing.plus RI0 b d).
Proof.
  intros RI0 DO0 a b c d Hab Hcd.
  exact (@S01_BaseRing.le_lt_trans RI0
           (@S01_BaseRing.plus RI0 a c)
           (@S01_BaseRing.plus RI0 a d)
           (@S01_BaseRing.plus RI0 b d)
           (@S01_BaseRing.le_plus_compat RI0 a a c d
              (@S01_BaseRing.le_refl RI0 a) Hcd)
           (@fa53_lt_plus_translate_r RI0 DO0 a b d Hab)).
Defined.

(* Assumption audit tail: each statement must read
   [Closed under the global context]. *)
Print Assumptions uabt2b_s04_lt_plus_compat_lt_le.
Print Assumptions uabt2b_s04_lt_plus_compat_le_lt.
Print Assumptions uabt2b_s06_lt_plus_compat_lt_le.
Print Assumptions uabt2b_s06_lt_plus_compat_le_lt.
Print Assumptions uabt2b_s05_lt_plus_compat_le_lt.
Print Assumptions uabt2b_s05_lt_plus_compat_lt_le.
Print Assumptions uabt2b_s13_lt_plus_compat_lt_le_h.
Print Assumptions uabt2b_upentropygain_lt_plus_compat_lt_le.
Print Assumptions uabt2b_upfirewall_lt_plus_compat_lt_le.
Print Assumptions uabt2b_attndoeblin_lt_plus_compat_lt_le_h.
Print Assumptions uabt2b_upreqalgebra_req_lt_plus_compat_lt_le.
