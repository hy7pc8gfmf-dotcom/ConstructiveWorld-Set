(* ==========================================================================
   abl_tbase_logrest.v — remaining log identities of the abl foundation
   cluster: inv_one_inv, argument compatibility, exp_neg, monotonicity.

   Mission.  Six theorems restating four root log lemmas of the group layer
     under the cluster slot signatures, verbatim: two copies of
     log(1/x) = -log x, one copy of the argument compatibility of log,
     two copies of log(e^{-u}) = -u, and one copy of the monotonicity
     of real_log (positive ends, a <= b entails log a <= log b).

   Dependencies.  The library files in the Require face below: backbone
     S01_BaseRing .. S07_RealSetoidExpLog, S14_B5BatchBlock (home of the
     monotone seed real_log_le_mono), G01_CoreMicro, G05_LogSmall. Bare
     carrier names (req, lt, zero, opp, inv_pos, log, exp_neg) resolve
     through the notation export of G05_LogSmall, as in G05 itself. No
     interface import and no Stdlib imports.

   References.  logd_log_inv_one_inv_real, logd_log_compat_real,
     logd_log_exp_neg_real (G05_LogSmall); real_log_le_mono
     (S14_B5BatchBlock); abl_tbase_logbridge.v serves the sibling slots.

   Constructivity.  Every statement is carried by Set: req, lt and le are
     Set-valued interface fields, the real_* comparisons are Set-valued
     definitions and Real is a Set; no Prop component occurs. Proofs
     close by Defined; Print Assumptions reports Closed for all six.

   Build.  coqc -Q <ConstructiveWorld_Live root> "" abl_tbase_logrest.v;
     artifact begins 436f7121 00015ff4. Separate Extraction of the module
     yields Obj.magic 0 on both the .ml and the .mli side.
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S14_B5BatchBlock.
Require Import G01_CoreMicro.
Require Import G05_LogSmall.

(* ---- inv_one_inv: log(1/x) = -log x, firewall-cluster copy ---- *)

Theorem tblr_ufw_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- inv_one_inv: log(1/x) = -log x, second copy ---- *)

Theorem tblr_ut1c_log_inv_one_inv :
  forall (x : Real) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_real x Hx Hi).
Defined.

(* ---- argument compatibility: req x y gives req (log x) (log y) ---- *)

Theorem tblr_ufepa_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (logd_log_compat_real x y Hx Hy Hxy).
Defined.

(* ---- exp_neg: log(e^{-u}) = -u, comparison-cluster copy ---- *)

Theorem tblr_ulogcompd_tsup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- exp_neg: log(e^{-u}) = -u, second copy ---- *)

Theorem tblr_ulogrdf_tsup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Proof.
  intro u.
  exact (logd_log_exp_neg_real u).
Defined.

(* ---- monotonicity: 0 < a, 0 < b and a <= b give log a <= log b ---- *)

Theorem tblr_s12_sf_log_antitone_le :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b ->
    real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (real_log_le_mono a b Ha Hb Hab).
Defined.

(* Assumption audit: each line reports Closed under the global context. *)
Print Assumptions tblr_ufw_log_inv_one_inv.
Print Assumptions tblr_ut1c_log_inv_one_inv.
Print Assumptions tblr_ufepa_log_req_compat.
Print Assumptions tblr_ulogcompd_tsup_log_exp_neg.
Print Assumptions tblr_ulogrdf_tsup_log_exp_neg.
Print Assumptions tblr_s12_sf_log_antitone_le.
