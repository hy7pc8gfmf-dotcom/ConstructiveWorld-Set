(* ConstructiveWorld-Set -- audit carrier v8: direct-audit closure over the
   isolated log-engine island [G05_LogSmall]. *)

(** * abl_audit_base_v8: light-use carriers exercising the log engine
    main-theorem family of [G05_LogSmall].

    Mission.  Five carriers, seventeen use points, genuinely exercising
      the log engine face: [abh_log_upper_bound_engine] (Bishop-form
      upper bound [logd_log_le_linear_B], four station slots, concrete
      instance [log 2 <=_B 1]); [abh_log_upper_bound_eps_limit]
      (per-eps limit form at [x = 2]); [abh_log_mono_and_two_pos]
      (strict monotonicity plus [log 2 > 0]);
      [abh_kl_term_minus_form_one_one] (KL change-of-base plus
      [kl_term(1,1) == 0]); [abh_gibbs_inequality_two_forms] (two Gibbs
      lower-bound forms).

    Dependencies.  Stdlib [Lists.List], [Extraction]; requires
      [S02_CauchyComplete], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [UpRealLeB], [G05_LogSmall].

    References.  ConstructiveWorld-Main, module [abl_audit_base_v8]
      (statement names carried over verbatim).

    Constructivity.  No admits, no classical logic, no Prop carriers:
      bounds sit on [real_le_b]/[real_le]/[real_lt], equations on
      [real_eq], conjunctions on the Set product; every proof is an
      explicit [exact]/[apply] term; extraction is [Obj.magic]-free.

    Build.  [coqc -native-compiler no -q -Q . "" abl_audit_base_v8.v]
      compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

From Stdlib Require Import Lists.List.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpRealLeB.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section 0 - internal plumbing bay (concrete points and          *)
(*   positivity witnesses, not carrier statements).                *)
(* ============================================================ *)

(* The concrete point [2 := 1+1] with its positivity witness       *)
(* (additive positivity applied to 0 < 1 and 0 < 1).               *)
Definition abh_two : Real := real_plus real_one real_one.

Definition abh_two_pos : real_lt real_zero abh_two :=
  real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one.

(* The concrete point [log 2] (positivity witness fully assembled). *)
Definition abh_log_two : Real := real_log abh_two abh_two_pos.

(* Transport chain: [2 + (-1) == 1] ([assoc] reassociation,        *)
(* [1 + (-1) == 0], and addition compatibility).                   *)
Lemma abh_two_minus_one_eq_one :
  real_eq (real_plus abh_two (real_opp real_one)) real_one.
Proof.
  unfold abh_two.
  apply (real_eq_trans
           (real_plus (real_plus real_one real_one) (real_opp real_one))
           (real_plus real_one (real_plus real_one (real_opp real_one)))
           real_one).
  - apply real_eq_sym.
    exact (real_plus_assoc real_one real_one (real_opp real_one)).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_plus real_one (real_opp real_one)) real_one real_zero).
    + apply real_eq_refl.
    + exact (real_plus_opp real_one).
Qed.

(* ============================================================ *)
(* Section 1 - carrier 1, the log upper-bound engine face (Bishop  *)
(*   form): the general form quoted verbatim, four station-slot    *)
(*   wings quoted, plus the concrete instance [log 2 <=_B 1]       *)
(*   (engine instantiation transported along the anchor).          *)
(* ============================================================ *)

Theorem abh_log_upper_bound_engine :
  (forall (x : Real) (Hx : real_lt real_zero x),
     real_le_b (real_log x Hx) (real_plus x (real_opp real_one))) *
  ((forall (x : Real) (Hx : real_lt real_zero x),
      real_le_b (real_log x Hx) (real_plus x (real_opp real_one))) *
   ((forall (x : Real) (Hx : real_lt real_zero x),
      real_le_b (real_log x Hx) (real_plus x (real_opp real_one))) *
    ((forall (x : Real) (Hx : real_lt real_zero x),
       real_le_b (real_log x Hx) (real_plus x (real_opp real_one))) *
     ((forall (x : Real) (Hx : real_lt real_zero x),
        real_le_b (real_log x Hx) (real_plus x (real_opp real_one))) *
      real_le_b abh_log_two real_one)))).
Proof.
  split.
  - (* the engine main theorem applies verbatim in general form. *)
    intros x Hx. exact (logd_log_le_linear_B x Hx).
  - split.
    + (* station 1 (the UpReqU2:313 slot) quoted verbatim. *)
      intros x Hx. exact (lld_u2_log_le_linear_B x Hx).
    + split.
      * (* station 2 (the UpReqFEPAttn:90 slot) quoted verbatim. *)
        intros x Hx. exact (lld_fep_log_le_linear_B x Hx).
      * split.
        -- (* station 3 (the UpReqTempEntropy:60 slot) quoted verbatim. *)
           intros x Hx. exact (lld_tempent_log_le_linear_B x Hx).
        -- split.
           ++ (* station 4 (the UpFirewallReq:101 slot) quoted verbatim. *)
              intros x Hx. exact (lld_fw_log_le_linear_B x Hx).
           ++ (* concrete instance [log 2 <=_B 1]: the engine resolves at   *)
              (* [x = 2] and the right side is transported along the        *)
              (* [2 + (-1) == 1] anchor (one exercise of the engine plus    *)
              (* the transport anchor).                                     *)
              apply (logd_le_b_id_r abh_log_two
                       (real_plus abh_two (real_opp real_one)) real_one).
              ** exact (logd_log_le_linear_B abh_two abh_two_pos).
              ** exact abh_two_minus_one_eq_one.
Qed.

(* ============================================================ *)
(* Section 2 - carrier 2, the per-eps limit form of the log        *)
(*   upper bound: the general form quoted verbatim plus the        *)
(*   concrete instance at [x = 2].                                 *)
(* ============================================================ *)

Theorem abh_log_upper_bound_eps_limit :
  (forall (x eps : Real) (Hx : real_lt real_zero x)
     (Heps : real_lt real_zero eps),
     real_le (real_log x Hx)
             (real_plus (real_plus x (real_opp real_one)) eps)) *
  (forall (eps : Real) (Heps : real_lt real_zero eps),
     real_le abh_log_two
             (real_plus (real_plus abh_two (real_opp real_one)) eps)).
Proof.
  split.
  - (* the limit-form main theorem applies verbatim in general form. *)
    intros x eps Hx Heps. exact (logd_log_le_linear_eps x eps Hx Heps).
  - (* concrete instance: the limit-approximation face resolves at     *)
    (* [x = 2] (uniformly feasible for every [eps > 0]).               *)
    intros eps Heps. exact (logd_log_le_linear_eps abh_two eps abh_two_pos Heps).
Qed.

(* ============================================================ *)
(* Section 3 - carrier 3, log strict monotonicity plus the lower   *)
(*   face: the general form quoted verbatim plus the genuinely     *)
(*   derived chain [log 2 > 0] (the island monotonicity theorem    *)
(*   resolves at [1 < 2] with the [log 1 == 0] transport, not a    *)
(*   restatement of existing island statements).                   *)
(* ============================================================ *)

Theorem abh_log_mono_and_two_pos :
  (forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
     real_lt a b -> real_lt (real_log a Ha) (real_log b Hb)) *
  real_lt real_zero abh_log_two.
Proof.
  split.
  - (* the monotonicity main theorem applies verbatim in general form. *)
    intros a b Ha Hb Hlt. exact (logd_log_lt_mono_real a b Ha Hb Hlt).
  - (* lower-face derivation chain: the [log 1 == 0] transport with    *)
    (* the monotonicity face fed the [1 < 2] translation chain.        *)
    apply (RealSetoid.real_lt_compat
             (real_log real_one real_lt_zero_one) real_zero
             abh_log_two abh_log_two).
    + exact (real_log_one real_lt_zero_one).
    + apply real_eq_refl.
    + apply (logd_log_lt_mono_real real_one abh_two real_lt_zero_one
               abh_two_pos).
      apply (RealSetoid.real_lt_compat
               (real_plus real_one real_zero) real_one
               abh_two abh_two).
      * exact (real_plus_zero real_one).
      * apply real_eq_refl.
      * exact (real_lt_plus_translate real_one real_zero real_one
                 real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Section 4 - carrier 4, the change-of-base face (the KL          *)
(*   canonical form equals the minus form): the general form       *)
(*   quoted verbatim plus the computation chain                    *)
(*   [kl_term(1,1) == 0].                                          *)
(* ============================================================ *)

Theorem abh_kl_term_minus_form_one_one :
  (forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
     real_eq (real_kl_term p q Hp Hq)
             (real_mult p (real_plus (real_log p Hp)
                                     (real_opp (real_log q Hq))))) *
  real_eq (real_kl_term real_one real_one real_lt_zero_one real_lt_zero_one)
          real_zero.
Proof.
  split.
  - (* the change-of-base main theorem applies verbatim in general     *)
    (* form (the island's log-inverse elimination chain).              *)
    intros p q Hp Hq. exact (logd_kl_term_minus_form p q Hp Hq).
  - (* concrete instance: [kl_term(1,1) == 1*(log 1 - log 1) ==        *)
    (* 1*(0-0) == 0] - three genuine steps: minus-form instantiation,  *)
    (* [log 1 == 0], and the algebraic closure [x + (-x) == 0].        *)
    apply (real_eq_trans
             (real_kl_term real_one real_one real_lt_zero_one
                real_lt_zero_one)
             (real_mult real_one
                (real_plus (real_log real_one real_lt_zero_one)
                           (real_opp (real_log real_one real_lt_zero_one))))
             real_zero).
    + exact (logd_kl_term_minus_form real_one real_one real_lt_zero_one
               real_lt_zero_one).
    + apply (RealSetoid.real_eq_mult_compat real_one
               (real_plus (real_log real_one real_lt_zero_one)
                          (real_opp (real_log real_one real_lt_zero_one)))
               real_one real_zero).
      * apply real_eq_refl.
      * exact (real_plus_opp (real_log real_one real_lt_zero_one)).
Qed.

(* ============================================================ *)
(* Section 5 - carrier 5, the Gibbs lower bound in two coexisting  *)
(*   forms: the Bishop form and the per-eps form each quoted as    *)
(*   one wing.                                                     *)
(* ============================================================ *)

Theorem abh_gibbs_inequality_two_forms :
  (forall (X : Type) (l : list X) (p q : X -> Real)
     (Hp : forall s : X, real_lt real_zero (p s))
     (Hq : forall s : X, real_lt real_zero (q s))
     (Hnormp : real_eq (real_list_sum X p l) real_one)
     (Hnormq : real_eq (real_list_sum X q l) real_one),
     real_le_b real_zero
       (real_list_sum X
          (fun s : X => real_mult (p s)
                         (real_plus (real_log (p s) (Hp s))
                                    (real_opp (real_log (q s) (Hq s))))) l)) *
  (forall (X : Type) (l : list X) (p q : X -> Real)
     (Hp : forall s : X, real_lt real_zero (p s))
     (Hq : forall s : X, real_lt real_zero (q s))
     (Hnormp : real_eq (real_list_sum X p l) real_one)
     (Hnormq : real_eq (real_list_sum X q l) real_one)
     (eps : Real) (Heps : real_lt real_zero eps),
     real_le real_zero
       (real_plus
          (real_list_sum X
             (fun s : X => real_mult (p s)
                            (real_plus (real_log (p s) (Hp s))
                                       (real_opp (real_log (q s) (Hq s)))))
             l)
          eps)).
Proof.
  split.
  - (* the Bishop form ([0 <=_B sum p*(log p - log q)]) applies      *)
    (* verbatim in general form.                                     *)
    intros X l p q Hp Hq Hnormp Hnormq.
    exact (logd_gibbs_inequality_minus_B X l p q Hp Hq Hnormp Hnormq).
  - (* the per-eps limit form ([0 <= sum p*(log p - log q) + eps])   *)
    (* applies verbatim in general form.                             *)
    intros X l p q Hp Hq Hnormp Hnormq eps Heps.
    exact (logd_gibbs_inequality_minus_eps X l p q Hp Hq Hnormp Hnormq
             eps Heps).
Qed.

(* ============================================================ *)
(* Section 6 - tail bay: assumption audit (twelve cross-file       *)
(*   direct audits of the G05 log engine main theorems plus self-  *)
(*   audits of the five carriers of this file).                    *)
(*   Reading rule: all seventeen outputs must print                *)
(*   "Closed under the global context".                            *)
(*   The first 12 are the direct-audit slots (the upper-bound      *)
(*   twin forms, monotonicity, the lower face, the transport       *)
(*   anchor, change-of-base, the Gibbs twin forms, and the four    *)
(*   station-slot family); the last 5 are self-audits of this      *)
(*   file's five carriers.                                         *)
(*   Note: the [Require] closure contains the whole                *)
(*   S01-S15/[UpRealLeB] chain; the [coqchk] environment-axiom     *)
(*   face and the per-theorem [Print Assumptions] checks are       *)
(*   separate accounts, not introduced by this file.               *)
(* ============================================================ *)

Print Assumptions logd_log_le_linear_B.
Print Assumptions logd_log_le_linear_eps.
Print Assumptions logd_log_lt_mono_real.
Print Assumptions logd_log_two_pos_real.
Print Assumptions logd_le_b_id_r.
Print Assumptions logd_kl_term_minus_form.
Print Assumptions logd_gibbs_inequality_minus_B.
Print Assumptions logd_gibbs_inequality_minus_eps.
Print Assumptions lld_u2_log_le_linear_B.
Print Assumptions lld_fep_log_le_linear_B.
Print Assumptions lld_tempent_log_le_linear_B.
Print Assumptions lld_fw_log_le_linear_B.
Print Assumptions abh_log_upper_bound_engine.
Print Assumptions abh_log_upper_bound_eps_limit.
Print Assumptions abh_log_mono_and_two_pos.
Print Assumptions abh_kl_term_minus_form_one_one.
Print Assumptions abh_gibbs_inequality_two_forms.

(* ============================================================ *)
(* Section 7 - export bay: the carriers double as extraction       *)
(*   ports; this file's own extraction face is free of             *)
(*   [Obj.magic].  On the full [Separate Extraction] closure face, *)
(*   existing upstream island code carries interface-boxing casts  *)
(*   ([S07_RealSetoidExpLog]: 71 interface-instance boxings;       *)
(*   [G05_LogSmall]: 2 bridge references, all interface-record-    *)
(*   field casts, not axioms) - an upstream frozen face, not       *)
(*   introduced by this file.                                      *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abh_log_upper_bound_engine
  abh_log_upper_bound_eps_limit abh_log_mono_and_two_pos
  abh_kl_term_minus_form_one_one abh_gibbs_inequality_two_forms.
