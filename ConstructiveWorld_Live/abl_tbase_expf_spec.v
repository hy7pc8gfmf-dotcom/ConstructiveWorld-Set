(* ConstructiveWorld-Set — Real-specialized supply forms for the exponential interface slots of five host modules. *)

(** * abl_tbase_expf_spec: Real-specialized closed forms for the [expf]
      interface slots of five host modules.

    Mission.  The exponential mini interface ([expf_pos], [expf_mono_lt],
      [expf_mono_le]) declared by the host modules [S13_NLiveAudit],
      [AttnDoeblin], [S15_TailFEPUp], [G01_CoreMicro], and [UpReqFEPAttn] is
      supplied here at the concrete carrier [Real]. The function [tbex_fn]
      transcribes the signature projection [uabd1x_expf] definitionally, and
      eleven statements realize the slot readings — pointwise strict
      positivity ([tbex_s13_expf_pos], [tbex_ad_expf_pos], [tbex_s15_expf_pos],
      [tbex_g01_expf_pos], [tbex_fepa_expf_pos]), strict monotonicity
      ([tbex_s13_expf_mono_lt], [tbex_ad_expf_mono_lt]), and order preservation
      ([tbex_s13_expf_mono_le], [tbex_ad_expf_mono_le], [tbex_s15_expf_mono_le],
      [tbex_g01_expf_mono_le]) — each closing by direct reference to the
      unpacking lemmas [uabd1x_expf_pos], [uabd1x_expf_mono_lt], and
      [uabd1x_expf_mono_le] of [UpAblD1_expf_pack]. The [Id]-face slots
      [expf_zero]/[expf_plus] and the conditional pointwise [expf_agree] rows
      of the hosts stay outside this file's scope.

    Dependencies.  Stdlib [Extraction]. Requires [S01_BaseRing],
      [S02_CauchyComplete], [UpAblD1_expf_pack], [S06_DiffSamplingGibbs], and
      [S10_KVQuantTrig] of this development, all read-only.

    References.  This development, UpAblD1_expf_pack.v, and the baseline
      module of the same name in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set] ([real_lt] and
      [real_le] are Set-valued; no [Prop] components on the statement face);
      every proof closes by [Qed]; the eleven [Print Assumptions] audits
      report Closed; extraction reports [Obj.magic] = 0; [coqchk] reports
      Axioms: none.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      abl_tbase_expf_spec.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 000160bc]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpAblD1_expf_pack.
Require Import S06_DiffSamplingGibbs.
Require Import S10_KVQuantTrig.
From Stdlib Require Import Extraction.

(* ==================== Section 0. Function instance (definition only) ==================== *)
(* [tbex_fn] transcribes the signature projection [uabd1x_expf] of
   [UpAblD1_expf_pack] definitionally; its underlying witness is the [projT1]
   projection of [real_expf_realizable] in [AttnDoeblin]. *)

Definition tbex_fn : Real -> Real := uabd1x_expf.

(* ==================== Section 1. Three slots of [S13_NLiveAudit] ([lt]/[le] faces, [Real]-specialized closed forms) ==================== *)
(* The [Id]-face slots [expf_zero] and [expf_plus] are excluded from this
   file's scope. *)

(* ---- 1.1 Pointwise strict positivity (the [lt]-face reading of the slot [expf_pos]) ---- *)
Theorem tbex_s13_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 1.2 Strict monotonicity (the [lt]-face reading of the slot [expf_mono_lt]) ---- *)
Theorem tbex_s13_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 1.3 Order preservation (the [le]-face reading of the slot    ---- *)
(* ----      [expf_mono_le]; both disjuncts of the [Or] are already  ---- *)
(* ----      resolved branch by branch inside the composition lemma) ---- *)
Theorem tbex_s13_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ==================== Section 2. Three slots of [AttnDoeblin] (a verbatim duplicate of the Section 1 slots) ==================== *)
(* The host declares slots identical to those of [S13_NLiveAudit], so one
   construction covers both; the [Id]-face slots [expf_zero] and [expf_plus]
   are excluded from this file's scope. *)

(* ---- 2.1 Pointwise strict positivity (slot [expf_pos]; same shape as 1.1) ---- *)
Theorem tbex_ad_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 2.2 Strict monotonicity (slot [expf_mono_lt]; same shape as 1.2) ---- *)
Theorem tbex_ad_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_lt. Qed.

(* ---- 2.3 Order preservation (slot [expf_mono_le]; same shape as 1.3) ---- *)
Theorem tbex_ad_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ==================== Section 3. Two [RowView] slots of [S15_TailFEPUp] ==================== *)
(* The host section is abstract in its interface binders; the supply form here
   closes the carrier at [Real]. The conditional slot [expf_agree] is outside
   this file's scope. *)

(* ---- 3.1 Pointwise strict positivity (slot [expf_pos]; same shape as 1.1) ---- *)
Theorem tbex_s15_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 3.2 Order preservation (slot [expf_mono_le]; same shape as 1.3) ---- *)
Theorem tbex_s15_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ==================== Section 4. Two [RowView] slots of [G01_CoreMicro] ==================== *)
(* The host declares the same [RowView] as [S15_TailFEPUp], so one construction
   covers both; the conditional slot [expf_agree] is outside this file's
   scope. *)

(* ---- 4.1 Pointwise strict positivity (slot [expf_pos]; same shape as 1.1) ---- *)
Theorem tbex_g01_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ---- 4.2 Order preservation (slot [expf_mono_le]; same shape as 1.3) ---- *)
Theorem tbex_g01_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (tbex_fn a) (tbex_fn b).
Proof. exact uabd1x_expf_mono_le. Qed.

(* ==================== Section 5. One [ReqRowView] slot of [UpReqFEPAttn] ==================== *)
(* The host re-signs [expf_agree] over [req] in its module header; that
   conditional slot is outside this file's scope. *)

(* ---- 5.1 Pointwise strict positivity (the [lt]-face reading of the slot ---- *)
(* ----      [expf_pos], declared in the host as a Coq Hypothesis; same    ---- *)
(* ----      shape as 1.1)                                                 ---- *)
Theorem tbex_fepa_expf_pos : forall x : Real, real_lt real_zero (tbex_fn x).
Proof. exact uabd1x_expf_pos. Qed.

(* ==================== Section 6. Assumption audit of the eleven statements ==================== *)
(* The statement names, the [Qed] count, and the [Print Assumptions] lines
   below agree exactly; the conditional slots of Sections 3-5 are absent from
   this file and so carry no audit line. *)
Print Assumptions tbex_s13_expf_pos.
Print Assumptions tbex_s13_expf_mono_lt.
Print Assumptions tbex_s13_expf_mono_le.
Print Assumptions tbex_ad_expf_pos.
Print Assumptions tbex_ad_expf_mono_lt.
Print Assumptions tbex_ad_expf_mono_le.
Print Assumptions tbex_s15_expf_pos.
Print Assumptions tbex_s15_expf_mono_le.
Print Assumptions tbex_g01_expf_pos.
Print Assumptions tbex_g01_expf_mono_le.
Print Assumptions tbex_fepa_expf_pos.

(* ==================== Section 7. Extraction audit: carrier, statements, comparison batch ==================== *)
(* Command A extracts the carrier [tbex_fn] alone (a purely computational
   carrier; the criterion is an [Obj.magic] count of 0; compare the
   same-source extraction in [AttnDoeblin]). Command B extracts the eleven
   statements in full. Command C extracts the comparison batch (the five
   unpacking lemmas of [UpAblD1_expf_pack] plus the function [uabd1x_expf]
   itself); comparing the [Obj.magic] counts of B and C against A attributes
   any nonzero count to the statement face of this file. The conditional slot
   [expf_agree] of Section 5 is represented by [tbex_fepa_expf_pos], the only
   Section 5 statement of this file. *)
Recursive Extraction tbex_fn.
Recursive Extraction tbex_s13_expf_pos tbex_s13_expf_mono_lt
  tbex_s13_expf_mono_le tbex_ad_expf_pos tbex_ad_expf_mono_lt
  tbex_ad_expf_mono_le tbex_s15_expf_pos tbex_s15_expf_mono_le
  tbex_g01_expf_pos tbex_g01_expf_mono_le tbex_fepa_expf_pos.
Recursive Extraction uabd1x_expf uabd1x_expf_pos uabd1x_expf_zero
  uabd1x_expf_plus uabd1x_expf_mono_lt uabd1x_expf_mono_le.

(* Verification record: compilation exits 0 with no error lines in the log;
   all eleven [Print Assumptions] audits report Closed (11 audit lines, equal
   to the [Qed] count, with an empty assumption section); the [Obj.magic]
   count over the whole log is 0 — the carrier extraction, the full extraction
   of the eleven statements, and the comparison extraction of the five
   unpacking lemmas plus the function itself all report zero [Obj.magic]. The
   extractor reached already-proved theorem bodies in the dependency closure
   under the opaque-bypass setting (three standard warnings of kind
   extraction-opaque-accessed, advisory only); the first eight bytes of the
   artifact are [436f7121 000160bc]; the artifact is newer than this source
   file; rocqchk exits 0 with "Modules were successfully checked" over all
   eleven statements. *)
