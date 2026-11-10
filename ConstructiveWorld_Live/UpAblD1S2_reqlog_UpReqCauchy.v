(* ConstructiveWorld-Set -- precedent log bridges for the FA-D1 D1-4 slot family. *)

(** * UpAblD1S2_reqlog_UpReqCauchy: precedent log bridge over the real logarithm.

    Mission.  The FA-D1 D1-4 precedent log bridge: strict and non-strict
      monotonicity of the real logarithm and the inversion identity for
      [exp_neg], replayed verbatim from five upstream slot files.  Main statements:
      [uabd1s2_aiu_log_req_compat], [uabd1s2_aiu_log_inv_exp_neg_req],
      [uabd1s2_align3_log_req_compat], [uabd1s2_align3_log_inv_exp_neg_req],
      [uabd1s2_aclose_log_req_compat], [uabd1s2_aclose_log_inv_exp_neg_req],
      [uabd1s2_cauchy_log_lt_mono_cc], [uabd1s2_dpo_log_req_compat],
      [uabd1s2_dpo_log_inv_exp_neg_req].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [G05_LogSmall] of this development.

    References.  This development, UpAblD1S2_reqlog_UpReqCauchy.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S2_reqlog_UpReqCauchy.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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

(* extraction-face concrete-carrier binding (the G05_LogSmall.v:47-81 template
   layer): the notation face binds the interface statement faces onto the
   concrete Real-layer carriers, so Separate Extraction renders concrete types
   (real_eq/real_lt) instead of the abstract projection types -- Obj.magic = 0,
   the wrapper-indirect-consumption precedent (batch registered), statement
   faces untouched. *)
Abbreviation req := real_eq.
Abbreviation req_sym := real_eq_sym.
Abbreviation zero := real_zero.
Abbreviation lt := real_lt.
Abbreviation log := real_log.
Abbreviation log_inv := real_log_inv.
Abbreviation exp_neg := real_exp_neg.
Abbreviation exp_neg_pos := real_exp_neg_pos.

(* ---- slot 1, from AlignIdUnclosed.v: log_req_compat, verbatim with R := Real ---- *)
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

(* ---- slot 2, from AlignIdUnclosed.v: log_inv_exp_neg_req, verbatim with R := Real ---- *)
Theorem uabd1s2_aiu_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: the assumption face of every statement is printed as the audit record ---- *)
Print Assumptions uabd1s2_aiu_log_req_compat.
Print Assumptions uabd1s2_aiu_log_inv_exp_neg_req.

(* ============================ Section 2. FA-D1 D1-4 precedent log bridge, the reqlog_UpReqAlign3 branch ============================ *)
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
(* filtered re-import: the bare interface names stay bound to the
   concrete-carrier abbreviations declared in section 1 above *)
Import RealInterfaceEnhancedMod (one).

(* ---- slot 1, fromUpReqAlign3.v: log_req_compat, verbatim with R := Real ---- *)
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

(* ---- slot 2, from UpReqAlign3.v: log_inv_exp_neg_req, verbatim with R := Real ---- *)
Theorem uabd1s2_align3_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: the assumption face of every statement is printed as the audit record ---- *)
Print Assumptions uabd1s2_align3_log_req_compat.
Print Assumptions uabd1s2_align3_log_inv_exp_neg_req.

(* ============================ Section 3. FA-D1 D1-4 precedent log bridge, the reqlog_UpReqAlignClose branch ============================ *)
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
(* filtered re-import: the bare interface names stay bound to the
   concrete-carrier abbreviations declared in section 1 above *)
Import RealInterfaceEnhancedMod (one).

(* ---- slot 1, fromUpReqAlignClose.v: log_req_compat, verbatim with R := Real ---- *)
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

(* ---- slot 2, from UpReqAlignClose.v: log_inv_exp_neg_req, verbatim with R := Real ---- *)
Theorem uabd1s2_aclose_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: the assumption face of every statement is printed as the audit record ---- *)
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
(* filtered re-import: the bare interface names stay bound to the
   concrete-carrier abbreviations declared in section 1 above *)
Import RealInterfaceEnhancedMod (one).

(* ---- slot 1, fromUpReqCauchy.v: log_lt_mono_cc, verbatim with R := Real ---- *)
Theorem uabd1s2_cauchy_log_lt_mono_cc :
  forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (log a Ha) (log b Hb).
Proof.
  intros a b Ha Hb Hlt.
  exact (logd_log_lt_mono_real a b Ha Hb Hlt).
Qed.

(* ---- closing: the assumption face of every statement is printed as the audit record ---- *)
Print Assumptions uabd1s2_cauchy_log_lt_mono_cc.

(* ============================ Section 4. FA-D1 D1-4 precedent log bridge, the reqlog_UpReqDpoLoss branch ============================ *)
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
(* filtered re-import: the bare interface names stay bound to the
   concrete-carrier abbreviations declared in section 1 above *)
Import RealInterfaceEnhancedMod (one).

(* ---- slot 1, fromUpReqDpoLoss.v: rdl_log_req_compat, verbatim with R := Real ---- *)
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

(* ---- slot 2, from UpReqDpoLoss.v: rdl_log_inv_exp_neg_req, verbatim with R := Real ---- *)
Theorem uabd1s2_dpo_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- closing: the assumption face of every statement is printed as the audit record ---- *)
Print Assumptions uabd1s2_dpo_log_req_compat.
Print Assumptions uabd1s2_dpo_log_inv_exp_neg_req.
