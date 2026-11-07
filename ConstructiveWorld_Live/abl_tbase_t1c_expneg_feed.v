(* ConstructiveWorld-Set — Real-specialized supply for the exp_neg log slot of UpAblT1c_UpFirewallReq. *)
(** * abl_tbase_t1c_expneg_feed: the T1C named landing of the exp_neg three-slot group.

    Mission.  The host module [UpAblT1c_UpFirewallReq] declares the slot premise
      [uabt1c_dist_log_exp_neg_slot : forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u)]
      (L121-122); this file instantiates [R := Real] and supplies the closed form [tbne_t1c_log_exp_neg_real] feeding that slot face.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog] (the [req]/[log]/[exp_neg] carriers; [RealInterfaceEnhancedMod]
      hosted in S07), plus [G01_CoreMicro] and [G05_LogSmall] (the root supply); the host
      module is not Required and stays byte-identical.

    References.  Root supply: [logd_log_exp_neg_real] ([G05_LogSmall.v] L343-346; itself
      verbatim same-shape as [real_log_exp_neg], [CW_ConstructiveWorld_219] L42231).
      Same-style supplies: [tblr_ulogcompd_tsup_log_exp_neg] and
      [tblr_ulogrdf_tsup_log_exp_neg] ([abl_tbase_logrest.v] L123-141); [tspy_frd_log_exp_neg_real]
      and [tspy_tmw_log_exp_neg_real] serve the other two exp_neg slots.  Statement name and
      binder [u] carried from the host verbatim.

    Constructivity.  No admitted declarations, no dangling premises, no classical logic;
      the proof closes with [Qed] by a direct [exact] reference to the root supply (the
      standard supply-file form; non-triviality is inherited from the root file's
      [real_log_exp_neg] combination chain).  Statement carriers [req]/[lt] are [Set]-forms
      with no [Prop]; [Print Assumptions] is expected [Closed]; extraction expects
      [Obj.magic] = 0 with the pointer alias [logd_log_exp_neg_real].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" abl_tbase_t1c_expneg_feed.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]; [coqchk] over the environment reports no global assumptions. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import G01_CoreMicro.
Require Import G05_LogSmall.

(* ============================================================ *)
(* Section 1. The slot statement specialized at Real — the       *)
(*   statement of [uabt1c_dist_log_exp_neg_slot] in              *)
(*   [UpAblT1c_UpFirewallReq.v] (L121-122) verbatim, with the    *)
(*   binder name [u] as in the host and the abstract carrier [R] *)
(*   instantiated at [Real].                                     *)
(* ============================================================ *)

Theorem tbne_t1c_log_exp_neg_real :
  forall u : Real, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* ============================================================ *)
(* Print Assumptions audit                                       *)
(* ============================================================ *)

Print Assumptions tbne_t1c_log_exp_neg_real.
