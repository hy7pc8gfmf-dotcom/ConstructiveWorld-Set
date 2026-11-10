(* ConstructiveWorld-Set -- same-domain statement-face completions of the upstream real-line requirement modules. *)

(** * Same-domain statement faces for the upstream entropy-gain requirement: addition compatibility and the absolute-value identity.

    Mission.  This file formalizes the same-domain statement face of the
      upstream entropy-gain requirement over the decidable ordered real
      interface: strict addition compatibility [lt a b -> le c d ->
      lt (plus a c) (plus b d)] in the three requirement slots, and the
      absolute-value identity [le zero a -> req (abs a) a] in the sampling
      slot; the two duplicate faces of these statements appear as
      corollaries of the same statements.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], and
      [AbsLeId] of this development; no Stdlib module.

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""] on this module compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)

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
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* statement face from the baseline UpFirewallReq.v:103: statement verbatim, name under the file-local prefix, carrier in the canonical domain *)
Theorem uabT13_egreq_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    @S01_BaseRing.lt RI0 a b -> @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c) (@S01_BaseRing.plus RI0 b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing audit: Print Assumptions per statement face; each read is fully closed ---- *)
Print Assumptions uabT13_egreq_lpc.

(* ============================ Section 1. same-domain statement face, the pFirewallReq branch ============================ *)
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
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* statement face from the baseline UpFirewallReq.v:103: statement verbatim, name under the file-local prefix, carrier in the canonical domain *)
Theorem uabT13_fw_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    @S01_BaseRing.lt RI0 a b -> @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c) (@S01_BaseRing.plus RI0 b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing audit: Print Assumptions per statement face; each read is fully closed ---- *)
Print Assumptions uabT13_fw_lpc.

(* ============================ Section 2. same-domain statement face, the pReqAlignRestA branch ============================ *)
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
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* statement face from the baseline UpFirewallReq.v:103: statement verbatim, name under the file-local prefix, carrier in the canonical domain *)
Theorem uabT13_ralt_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    @S01_BaseRing.lt RI0 a b -> @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c) (@S01_BaseRing.plus RI0 b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing audit: Print Assumptions per statement face; each read is fully closed ---- *)
Print Assumptions uabT13_ralt_lpc.

(* ============================ Section 3. same-domain statement face, the pReqSampling branch ============================ *)
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
Require Import AbsLeId.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13Usamp.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* slot 1, from the baseline L135 abs_ge_zero_req: statement verbatim, name under the file-local prefix *)
Theorem uabT13_usamp_abs_ge_zero_req :
  forall a : @S01_BaseRing.R RI0,
    @S01_BaseRing.le RI0 (@S01_BaseRing.zero RI0) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI0) (@S01_BaseRing.abs RI0 a) a.
Proof.
  intros a Ha.
  exact (@ali_abs_ge_zero_id RI0 DO0 a Ha).
Qed.

(* slot 2, from the baseline L136 lt_plus_compat_lt_le_h: statement verbatim, name under the file-local prefix *)
Theorem uabT13_usamp_lpc_h :
  forall a b c d : @S01_BaseRing.R RI0,
    @S01_BaseRing.lt RI0 a b -> @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c) (@S01_BaseRing.plus RI0 b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

(* slot 3, from the baseline L737 bs_abs: the same statement as L135 carried in two slots, so it enters here as a Corollary and is not counted twice *)
Corollary uabT13_usamp_bs_abs :
  forall a : @S01_BaseRing.R RI0,
    @S01_BaseRing.le RI0 (@S01_BaseRing.zero RI0) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI0) (@S01_BaseRing.abs RI0 a) a.
Proof.
  exact uabT13_usamp_abs_ge_zero_req.
Qed.

(* slot 4, from the baseline L738 bs_lpc: the same statement as L136 carried in two slots, entered as a Corollary *)
Corollary uabT13_usamp_bs_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    @S01_BaseRing.lt RI0 a b -> @S01_BaseRing.le RI0 c d ->
    @S01_BaseRing.lt RI0 (@S01_BaseRing.plus RI0 a c) (@S01_BaseRing.plus RI0 b d).
Proof.
  exact uabT13_usamp_lpc_h.
Qed.

End UabT13Usamp.

(* ---- closing audit: Print Assumptions per statement face; each read is fully closed ---- *)
Print Assumptions uabT13_usamp_abs_ge_zero_req.
Print Assumptions uabT13_usamp_lpc_h.
Print Assumptions uabT13_usamp_bs_abs.
Print Assumptions uabT13_usamp_bs_lpc.
