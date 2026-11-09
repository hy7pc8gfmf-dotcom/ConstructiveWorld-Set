(* Entropy-gain requirement slots: four same-domain statement blocks on the
   constructive real line; statement names carry the house prefix verbatim.
   Mission.  Formalize two laws as prefixed same-domain slots.  The order
      compatibility law, from lt a b and le c d to infer lt (plus a c) (plus b d),
      restated in three independent blocks under the RealInterfaceEnhanced
      and DecidableOrder context, and the absolute-value law, from le zero a
      to infer the equality of abs a and a, in a four-slot sampling block
      whose last two slots restate the first two as corollaries; the
      absolute-value pair is pinned to the concrete real_le/real_eq face.
   Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv,
      S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog,
      S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5,
      S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp,
      fa53_compat_abs, AbsLeId, TempSoftmaxInstantiation; each block repeats
      this Require face; the previous generation's RealInterfaceEnhancedMod
      import is dropped (its concrete bindings shadowed the generic face).
   References.  Source anchors: UpFirewallReq source line 103 for the three
      compatibility slots; source lines 135, 136, 737, 738 for the sampling
      slots, where lines 737 and 738 restate lines 135 and 136 in twin slots,
      registered as corollaries.  Interface-generation note: the generic
      equality face req has no field in this tree's RealInterfaceEnhanced
      (S01_BaseRing.v:184-260, equality face = Id), so the absolute-value
      pair is pinned to the concrete real_le/real_eq face with the
      ali_real_abs_ge_zero_id witness (AbsLeId.v:91); the order-compatibility
      slots keep the generic face with the fa53 witness (fa53_compat_abs.v:117).
   Constructivity.  axiom-free; every proof closes by one exact term
      (fa53_lt_plus_compat_lt_le_dec, ali_real_abs_ge_zero_id); Print
      Assumptions at each export reads Closed.
   Build.  coqc -native-compiler no -Q . ""; fingerprint [436f7121 000160bc].
*)
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

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* mirrors UpFirewallReq source line 103: statement verbatim under a prefixed name, carried on the canonical domain *)
Theorem uabT13_egreq_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing block: Print Assumptions at each export, all read as closed ---- *)
Print Assumptions uabT13_egreq_lpc.

(* ============================ same-domain statement face, §1 (pFirewallReq branch) ============================ *)
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

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* mirrors UpFirewallReq source line 103: statement verbatim under a prefixed name, carried on the canonical domain *)
Theorem uabT13_fw_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing block: Print Assumptions at each export, all read as closed ---- *)
Print Assumptions uabT13_fw_lpc.

(* ============================ same-domain statement face, §2 (pReqAlignRestA branch) ============================ *)
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

Section UabT13FwLpc.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* mirrors UpFirewallReq source line 103: statement verbatim under a prefixed name, carried on the canonical domain *)
Theorem uabT13_ralt_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

End UabT13FwLpc.

(* ---- closing block: Print Assumptions at each export, all read as closed ---- *)
Print Assumptions uabT13_ralt_lpc.

(* ============================ same-domain statement face, §3 (pReqSampling branch) ============================ *)
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

Section UabT13Usamp.

Context {RI0 : RealInterfaceEnhanced}.
Context {DO0 : DecidableOrder RI0}.

(* slot 1: from source line 135, abs_ge_zero_req (name prefixed; pinned to the
   concrete real_le/real_eq face -- this tree's generic interface layer has no
   req field, see the interface-generation note in the header) *)
Theorem uabT13_usamp_abs_ge_zero_req :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a Ha.
  exact (ali_real_abs_ge_zero_id a Ha).
Qed.

(* slot 2: from source line 136, lt_plus_compat_lt_le_h (statement verbatim, name prefixed) *)
Theorem uabT13_usamp_lpc_h :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI0 DO0 a b c d Hab Hcd).
Qed.

(* slot 3: from source line 737, bs_abs; same statement as line 135 in a twin slot, carried as a corollary and not counted twice *)
Corollary uabT13_usamp_bs_abs :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact uabT13_usamp_abs_ge_zero_req.
Qed.

(* slot 4: from source line 738, bs_lpc; same statement as line 136 in a twin slot *)
Corollary uabT13_usamp_bs_lpc :
  forall a b c d : @S01_BaseRing.R RI0,
    lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact uabT13_usamp_lpc_h.
Qed.

End UabT13Usamp.

(* ---- closing block: Print Assumptions at each export, all read as closed ---- *)
Print Assumptions uabT13_usamp_abs_ge_zero_req.
Print Assumptions uabT13_usamp_lpc_h.
Print Assumptions uabT13_usamp_bs_abs.
Print Assumptions uabT13_usamp_bs_lpc.
