(* ConstructiveWorld-Set -- FA-D1 D1-④ precedent log bridge, same-domain statement face. *)

(** * UpAblD1S2_reqlog_UpReqCauchy: FA-D1 D1-④ precedent log bridge.

    Mission.  formalize the FA-D1 D1-④ precedent log bridge as one same-domain
      statement face: the upstream log compatibility statements
      log_req_compat and log inverse statements log_inv_exp_neg_req restated
      verbatim over R := Real from AlignIdUnclosed, UpReqAlign3,
      UpReqAlignClose and UpReqDpoLoss, plus the strict form log_lt_mono_cc
      from UpReqCauchy, so one module carries the whole reqlog precedent face.

    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO
      S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, G05_LogSmall.

    References.  AlignIdUnclosed.v L89, L92; UpReqAlign3.v L81, L84;
      UpReqAlignClose.v L48, L51; UpReqCauchy.v L821-822; UpReqDpoLoss.v
      L64, L67 (the slot anchors below); interface note: the four
      le_antisym apply sites shed the retired Real binder shell for the
      RealInterfaceEnhancedSetoid interface, whose Real carrier is folded
      into the instance RealEnhancedReal (S07_RealSetoidExpLog.v; call-form
      precedent S10_KVQuantTrig.v L12450), statement names untouched.

    Constructivity.  axiom-free and admission-free; the statement face is
      Set-carried; Print Assumptions closes every item.

    Build.  Rocq 9.3, [coqc -native-compiler no -Q . ""] wrapped in cpu_guard
      load capping; artifact magic [436f7121 000160bc]. *)

(* ============================ §1 FA-D1 D1-④ precedent log bridge (reqlog_AlignIdUnclosed branch) ============================ *)
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

(* ---- slot 1 ← AlignIdUnclosed.v L89 log_req_compat (verbatim, R := Real) ---- *)
Theorem uabd1s2_aiu_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (@RealInterfaceEnhancedMod.le_antisym RealInterfaceEnhancedMod.RealEnhancedReal (log x Hx) (log y Hy)).
  apply (real_log_le_mono x y Hx Hy).
  right; exact Hxy.
  apply (real_log_le_mono y x Hy Hx).
  right; exact (req_sym _ _ Hxy).
Qed.

(* ---- slot 2 ← AlignIdUnclosed.v L92 log_inv_exp_neg_req (verbatim, R := Real) ---- *)
Theorem uabd1s2_aiu_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: per-item Print Assumptions at end of file (G2 record) ---- *)
Print Assumptions uabd1s2_aiu_log_req_compat.
Print Assumptions uabd1s2_aiu_log_inv_exp_neg_req.

(* ============================ §2 FA-D1 D1-④ precedent log bridge (reqlog_UpReqAlign3 branch) ============================ *)
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

(* ---- slot 1 ← UpReqAlign3.v L81 log_req_compat (verbatim, R := Real) ---- *)
Theorem uabd1s2_align3_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (@RealInterfaceEnhancedMod.le_antisym RealInterfaceEnhancedMod.RealEnhancedReal (log x Hx) (log y Hy)).
  apply (real_log_le_mono x y Hx Hy).
  right; exact Hxy.
  apply (real_log_le_mono y x Hy Hx).
  right; exact (req_sym _ _ Hxy).
Qed.

(* ---- slot 2 ← UpReqAlign3.v L84 log_inv_exp_neg_req (verbatim, R := Real) ---- *)
Theorem uabd1s2_align3_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: per-item Print Assumptions at end of file (G2 record) ---- *)
Print Assumptions uabd1s2_align3_log_req_compat.
Print Assumptions uabd1s2_align3_log_inv_exp_neg_req.

(* ============================ §3 FA-D1 D1-④ precedent log bridge (reqlog_UpReqAlignClose branch) ============================ *)
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

(* ---- slot 1 ← UpReqAlignClose.v L48 log_req_compat (verbatim, R := Real) ---- *)
Theorem uabd1s2_aclose_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (@RealInterfaceEnhancedMod.le_antisym RealInterfaceEnhancedMod.RealEnhancedReal (log x Hx) (log y Hy)).
  apply (real_log_le_mono x y Hx Hy).
  right; exact Hxy.
  apply (real_log_le_mono y x Hy Hx).
  right; exact (req_sym _ _ Hxy).
Qed.

(* ---- slot 2 ← UpReqAlignClose.v L51 log_inv_exp_neg_req (verbatim, R := Real) ---- *)
Theorem uabd1s2_aclose_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: per-item Print Assumptions at end of file (G2 record) ---- *)
Print Assumptions uabd1s2_aclose_log_req_compat.
Print Assumptions uabd1s2_aclose_log_inv_exp_neg_req.

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

(* ---- slot 1 ← UpReqCauchy.v L821-822 log_lt_mono_cc (verbatim, R := Real) ---- *)
Theorem uabd1s2_cauchy_log_lt_mono_cc :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (logd_log_lt_mono_real a b Ha Hb Hlt).
Qed.

(* ---- closing: per-item Print Assumptions at end of file (G2 record) ---- *)
Print Assumptions uabd1s2_cauchy_log_lt_mono_cc.

(* ============================ §4 FA-D1 D1-④ precedent log bridge (reqlog_UpReqDpoLoss branch) ============================ *)
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

(* ---- slot 1 ← UpReqDpoLoss.v L64 rdl_log_req_compat (verbatim, R := Real) ---- *)
Theorem uabd1s2_dpo_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (@RealInterfaceEnhancedMod.le_antisym RealInterfaceEnhancedMod.RealEnhancedReal (log x Hx) (log y Hy)).
  apply (real_log_le_mono x y Hx Hy).
  right; exact Hxy.
  apply (real_log_le_mono y x Hy Hx).
  right; exact (req_sym _ _ Hxy).
Qed.

(* ---- slot 2 ← UpReqDpoLoss.v L67 rdl_log_inv_exp_neg_req (verbatim, R := Real) ---- *)
Theorem uabd1s2_dpo_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: per-item Print Assumptions at end of file (G2 record) ---- *)
Print Assumptions uabd1s2_dpo_log_req_compat.
Print Assumptions uabd1s2_dpo_log_inv_exp_neg_req.
