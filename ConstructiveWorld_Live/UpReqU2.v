(* ConstructiveWorld-Set — U2 upgrade face: the logarithmic req-compatibility bridge and the alignment-family witness machinery. *)
(** * UpReqU2: the [ReqLogBridge] extension, [req_u2_kl_arg2_ext], and the
      seven-statement U2 main body in [req] form.

    Mission.  File-level lemmas: [log_req_compat] (req compatibility of [log]
      from the monotone le bridge), [log_req_witness_compat],
      [log_req_compat_real] (resolved at the [Real] instance via
      [real_log_le_mono]), [req_u2_kl_arg2_ext] (pointwise req
      extensionality of KL), and [u2_rlhf_optimal_seed_discharge]
      (discharging the rlhf_optimal_seed premise by FEP assembly); the
      section main body proves the alignment/unique-fixed-point family.

    Dependencies.  Requires [S01_BaseRing]–[S15_TailFEPUp] and the
      [UpReqAlgebra]/[UpReqDist]/[UpReqAlign]/[UpReqAlign2]/[UpReqAlign3]/
      [UpSigMigrate2] modules of this development; pure term-mode, no [Morphisms].

    References.  This development; the baseline module of the same name in
      ConstructiveWorld-Main, whose statement names are carried over verbatim
      (statement-face Set-carrier completion), following its [U2FixedPoint]
      section ([L23281]-[L23791]; [rlhf_optimal@19049]).

    Constructivity.  All named statements are carried by [Set] (Set-valued
      [req]/[lt]/[le]/[And]/[Or]); the honest bridges ([sum_zero_nonneg],
      [log_le_linear], [log_req_compat], [log_inv_exp_neg_req],
      [req2_gibbs_inequality]) are Section premises, so [Print Assumptions]
      stays Closed; extraction gives [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpReqU2.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require Import UpSigMigrate2.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the
   global Real, and the field names below are bound to the global constants. *)
Notation R := Real.
Notation req := real_eq.
Notation req_refl := real_eq_refl.
Notation req_sym := real_eq_sym.
Notation req_trans := real_eq_trans.
Notation zero := real_zero.
Notation one := real_one.
Notation plus := real_plus.
Notation mult := real_mult.
Notation opp := real_opp.
Notation lt := real_lt.
Notation le := real_le.
Notation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Notation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Notation req_opp_compat := RealSetoid.real_eq_opp_compat.
Notation req_lt_compat := RealSetoid.real_lt_compat.
Notation plus_comm := real_plus_comm.
Notation plus_zero := real_plus_zero.
Notation plus_opp := real_plus_opp.
Notation mult_comm := real_mult_comm.
Notation mult_one := real_mult_one.
Notation mult_zero := real_mult_zero.
Notation le_refl := real_le_refl.
Notation le_antisym := real_le_antisym.
Notation lt_le_iff := RealSetoid.real_lt_le_iff_req.
Notation le_id_l := RealSetoid.real_le_id_l.
Notation le_id_r := RealSetoid.real_le_id_r.
Notation inv_pos := real_inv_pos.
Notation le_plus_compat := real_le_plus_compat.
Notation opp_le_compat := real_opp_le_compat.
Notation inv_pos_pos := real_inv_pos_pos.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation log := real_log.
Notation log_inv := real_log_inv.

(* ============================================================ *)
(* Deliverable 1: [log_req_compat] — the [ReqLogBridge] extension (a file-level lemma) *)
(* ============================================================ *)

(* single-premise bridge form: req compatibility of [log] follows from the
   monotone le bridge.
   Route: [req x y] is raised to [le] by the right branch of [lt_le_iff], then
   closed in both directions by [le_antisym].
   Same shape as [real_log_le_mono]; discharges the explicit-application
   template (see [log_req_compat_real]). *)
Lemma log_req_compat : 
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    le x y -> le (log x Hx) (log y Hy)) ->
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros Hmono x y Hx Hy Hxy.
  apply (le_antisym (log x Hx) (log y Hy)).
  - apply (Hmono x y Hx Hy).
    exact (lt_le_iff x y (inr Hxy)).
  - apply (Hmono y x Hy Hx).
    exact (lt_le_iff y x (inr (req_sym x y Hxy))).
Qed.

(* Deliverable 1a: witness independence of [log] — converting between two
   positivity witnesses at the same point (the x ≡ x special case;
   consumes the Align3-shaped compatibility premise, no monotonicity needed). *)
Lemma log_req_witness_compat : 
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)) ->
  forall (x : R) (Hx : lt zero x) (Hx' : lt zero x),
    req (log x Hx) (log x Hx').
Proof.
  intros Hcompat x Hx Hx'.
  exact (Hcompat x x Hx Hx' (req_refl x)).
Qed.

(* Deliverable 1b: resolution at the concrete instance (the explicit-application
   template) — closed unconditionally on the [Real] layer.
   Seed: [real_log_le_mono] ([L112104]) supplied explicitly at the
   single-premise position of the abstract bridge. *)
Lemma log_req_compat_real : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (log_req_compat (fun (a b : Real) (Ha : lt zero a) (Hb : lt zero b) (Hab : le a b) => real_log_le_mono a b Ha Hb Hab) x y Hx Hy Hxy).
Qed.

(* ============================================================ *)
(* Deliverable 2: [req_u2_kl_arg2_ext] — pointwise req extensionality of KL     *)
(* in its second argument (premise-carried restatement of the upstream          *)
(* u2_kl_arg2_ext@23369: the pointwise req premise version)                     *)
(* ============================================================ *)
(* honest signature change: the log premises are made explicit ([Hp]/[Hq]) and *)
(* the positivity of [Hq'] is transported via [req_lt_compat].                 *)
Lemma req_u2_kl_arg2_ext :
  forall  (S : Set)
         (sumf : (S -> R) -> R),
    (forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
      req x y -> req (log x Hx) (log y Hy)) ->
    forall (p q q' : S -> R) (Hp : forall s : S, lt zero (p s))
                            (Hq : forall s : S, lt zero (q s))
                            (Hq' : forall s : S, lt zero (q' s)),
      (forall s : S, req (q s) (q' s)) ->
      req (req2_rel_ent S sumf p q Hp Hq)
          (req2_rel_ent S sumf p q' Hp Hq').
Proof.
  intros S sumf Hext Hlog p q q' Hp Hq Hq' Hqq'.
  unfold req2_rel_ent.
  apply (Hext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q s) (Hq s))))
              (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q' s) (Hq' s))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
                         (req_minus (log (p s) (Hp s)) (log (q s) (Hq s)))
                         (req_minus (log (p s) (Hp s)) (log (q' s) (Hq' s)))
                         (req_refl (p s))).
  exact (req2_minus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                           (log (q s) (Hq s)) (log (q' s) (Hq' s))
                           (req_refl (log (p s) (Hp s)))
                           (Hlog (q s) (q' s) (Hq s) (Hq' s) (Hqq' s))).
Qed.

(* ============================================================ *)
(* Deliverable 3: [u2_rlhf_optimal_seed_discharge] — FEP assembly discharging   *)
(* the rlhf_optimal_seed premise (req counterpart of the upstream               *)
(* rlhf_optimal@19049; follows the resolution method of                         *)
(* [UpSigMigrate2.a_rlhf_optimal]: FEP decomposition ⟹ F(pistar) ≤ F(p) ⟹      *)
(* order-preserving negation via [opp].                                         *)


(*  the same decomposition is consumed at u := pistar, and the first term drops
    out by KL(pistar‖pistar) == 0 ([w_rel_ent_self_zero]), giving: *)

(*  KL ≥ 0 is the [req2_gibbs_inequality] premise (entry 5; this file leaves its
    explicit premises untouched) + order preservation under β>0;
    closing = [le_id_l]/[le_id_r] conversions + the δ unfolding of [req_minus]
    (plus·opp) + [opp_le_compat].
    Premise demotion: the in-section rlhf_optimal_seed becomes a [Definition]
    consuming this lemma (section parameters fed once, no reproof); the
    U2a/U2e usage chains keep [Print Assumptions] Closed. *)
(* ============================================================ *)
Lemma u2_rlhf_optimal_seed_discharge :
  forall  (S : Set)
         (sumf : (S -> R) -> R),
    (forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) ->
    (forall f g : S -> R,
      req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))) ->
    (forall (a : R) (f : S -> R),
      req (sumf (fun s => mult a (f s))) (mult a (sumf f))) ->
    (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
      req x y -> req (log x Hx) (log y Hy)) ->
    (forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
    forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
           (ZAL_pos : lt zero (req2_Z_align S sumf reward beta beta_pos
                                             pi_ref)),
      (forall (q r : S -> R) (Hq : req2_pos_dist S q)
                              (Hr : req2_pos_dist S r),
        le zero (req2_rel_ent S sumf q r Hq Hr)) ->
      forall (p : S -> R) (Hn : req2_norm_one S sumf p)
             (Hp : req2_pos_dist S p),
        le (req2_J S sumf reward beta pi_ref pi_ref_pos p Hp)
           (req2_J S sumf reward beta pi_ref pi_ref_pos
                    (req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos)
                    (req2_pi_star_pos S sumf reward beta beta_pos pi_ref
                                       pi_ref_pos ZAL_pos)).
Proof.
  intros S sumf Hext Hadd Hlin Hlog Hinv reward beta beta_pos
         pi_ref pi_ref_pos ZAL_pos Hgibbs p Hn Hp.
  set (PSTR := req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos).
  set (PSTR_pos := req2_pi_star_pos S sumf reward beta beta_pos pi_ref
                                     pi_ref_pos ZAL_pos).
  set (ZAL := req2_Z_align S sumf reward beta beta_pos pi_ref).
  set (LOGZ := mult beta (log ZAL ZAL_pos)).
  set (FAP := req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp).
  set (FAPI := req2_F_align S sumf reward beta pi_ref pi_ref_pos
                             PSTR PSTR_pos).
  set (KLp := req2_rel_ent S sumf p PSTR Hp PSTR_pos).
  set (KLself := req2_rel_ent S sumf PSTR PSTR PSTR_pos PSTR_pos).
  
  assert (HdecP : req FAP (req_minus (mult beta KLp) LOGZ))
    by exact (r2_F_align_kl_diff S sumf Hext Hadd Hlin Hlog Hinv
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 p Hp Hn).
  (* 2. the same decomposition consumed at pistar (pistar normalization = [w_pi_star_normalized]) *)
  assert (HPSTRn : req2_norm_one S sumf PSTR)
    by exact (w_pi_star_normalized S sumf Hlin reward beta beta_pos pi_ref
                                   ZAL_pos).
  assert (HdecI : req FAPI (req_minus (mult beta KLself) LOGZ))
    by exact (r2_F_align_kl_diff S sumf Hext Hadd Hlin Hlog Hinv
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 PSTR PSTR_pos HPSTRn).
  (* 3. KL(pistar‖pistar) == 0 (w_rel_ent_self_zero) ⟹ β·KL(pistar‖pistar) == 0
     ⟹ F(pistar) == −β·log ZAL *)
  assert (Hklself : req KLself zero)
    by exact (w_rel_ent_self_zero S sumf Hext Hlin PSTR PSTR_pos).
  assert (HbK0 : req (mult beta KLself) zero)
    by exact (req_trans (mult beta KLself) (mult beta zero) zero
                 (req_mult_compat beta beta KLself zero (req_refl beta) Hklself)
                 (mult_zero beta)).
  assert (HFAPI : req FAPI (opp LOGZ))
    by exact (req_trans FAPI (req_minus (mult beta KLself) LOGZ) (opp LOGZ) HdecI
         (req_trans (req_minus (mult beta KLself) LOGZ) (req_minus zero LOGZ)
                    (opp LOGZ)
                    (req2_minus_compat (mult beta KLself) zero LOGZ LOGZ
                                       HbK0 (req_refl LOGZ))
                    (req_trans (req_minus zero LOGZ) (plus zero (opp LOGZ))
                               (opp LOGZ)
                               (req_refl (req_minus zero LOGZ))
                               (req_plus_zero_l (opp LOGZ))))).
  (* 4. KL ≥ 0 (premise) + order preservation under β>0 ⟹ 0 ≤ β·KL(p‖pistar) *)
  assert (Hdkl : le zero (mult beta KLp))
    by exact (r2_le_mult_nonneg beta KLp
                                (lt_le_iff zero beta (inl beta_pos))
                                (Hgibbs p PSTR Hp PSTR_pos)).
  (* 5. F(pistar) ≤ F(pistar) + β·KL == F(p) ([le_plus_compat] keeps the left summand; conversion finishes) *)
  assert (Hfin : le FAPI (plus FAPI (mult beta KLp)))
    by exact (le_id_l FAPI (plus FAPI zero) (plus FAPI (mult beta KLp))
                      (req_sym (plus FAPI zero) FAPI (plus_zero FAPI))
                      (le_plus_compat FAPI FAPI zero (mult beta KLp)
                                      (le_refl FAPI) Hdkl)).
  assert (Hconv : req (plus FAPI (mult beta KLp)) FAP)
    by exact (req_sym FAP (plus FAPI (mult beta KLp))
               (req_trans FAP (req_minus (mult beta KLp) LOGZ)
                          (plus FAPI (mult beta KLp))
                          HdecP
                          (req_trans (req_minus (mult beta KLp) LOGZ)
                                     (plus (mult beta KLp) FAPI)
                                     (plus FAPI (mult beta KLp))
                                     (req_trans (req_minus (mult beta KLp) LOGZ)
                                                (plus (mult beta KLp)
                                                      (opp LOGZ))
                                                (plus (mult beta KLp) FAPI)
                                                (req_refl (req_minus
                                                             (mult beta KLp)
                                                             LOGZ))
                                                (req_plus_compat
                                                   (mult beta KLp)
                                                   (mult beta KLp)
                                                   (opp LOGZ) FAPI
                                                   (req_refl (mult beta KLp))
                                                   (req_sym FAPI (opp LOGZ)
                                                            HFAPI)))
                                     (plus_comm (mult beta KLp) FAPI)))).
  (* 6. negation ([opp] order-preserving): J(p) = −F(p) ≤ −F(pistar) = J(pistar) *)
  exact (opp_le_compat FAPI FAP
                       (le_id_r FAPI (plus FAPI (mult beta KLp)) FAP
                                Hconv Hfin)).
Qed.

(* ============================================================ *)
(* [ReqU2FixedPoint]: the U2 main-body section (section parameters share the skeleton of [UpReqAlign3.Req3AlignCore]) *)
(* ============================================================ *)
Section ReqU2FixedPoint.

Context {RIS : RealInterfaceEnhancedSetoid}.
Variable S : Set.

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero -> forall s : S, req (f s) zero.

(* ---- [ReqLogBridge] bridge premises at the same positions (reduced and discharged by the file-level lemmas) ---- *)
Hypothesis log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
(* ---- exit bridge premises of [req_gibbs_equality] (the plain-le form, not derivable from the interface) ---- *)
Hypothesis log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis log_eq_linear :
  forall (x : R) (Hx : lt zero x), req (log x Hx) (req_minus x one) -> req x one.

Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable eta_le_one : le eta one.

(* ---- section-local aliases (all δ-transparent thin wrappers of the upstream [req2] definitions, as in [UpReqAlign3]) ---- *)
Definition pos3 (p : S -> R) : Set := req2_pos_dist S p.
Definition nrm (p : S -> R) : Set := req2_norm_one S sumf p.
Definition AL (s : S) : R :=
  req2_align_energy S reward beta pi_ref pi_ref_pos s.
Definition KLE (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q) : R :=
  req2_rel_ent S sumf p q Hp Hq.
Definition JJ (p : S -> R) (Hp : pos3 p) : R :=
  req2_J S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition FA (p : S -> R) (Hp : pos3 p) : R :=
  req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp.
Definition NPX (pi_t : S -> R) (Hpi_t : pos3 pi_t) (s : S) : R :=
  req2_pi_next S sumf sum_pos reward beta beta_pos pi_ref pi_ref_pos
                eta pi_t Hpi_t s.
Definition ZAL : R :=
  req2_Z_align S sumf reward beta beta_pos pi_ref.
Variable ZAL_pos : lt zero ZAL.
Definition PSTR (s : S) : R :=
  req2_pi_star S sumf reward beta beta_pos pi_ref ZAL_pos s.
Definition PSTR_pos : pos3 PSTR :=
  req2_pi_star_pos S sumf reward beta beta_pos pi_ref pi_ref_pos ZAL_pos.

(* transparent witnesses (the witness arguments of Set-valued relations are
   data: they must be [Definition]s, not Qed-wrapped — otherwise they are not
   convertible with the raw applications inside the upstream statements) *)
Definition npx_pos (pi_t : S -> R) (Hpi_t : pos3 pi_t) : pos3 (NPX pi_t Hpi_t) :=
  req2_pi_next_pos S sumf sum_pos reward beta beta_pos pi_ref
                    pi_ref_pos eta pi_t Hpi_t.

(* ---- honest bridge premises (depending on [PSTR]/[NPX]; declared after their definitions) ---- *)
Hypothesis req2_gibbs_inequality :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    le zero (KLE p q Hp Hq).
(* ---- [req_backward_kl_step_le] (former premise entry 6, resolved and demoted
   to a using definition — no longer a premise) ----
   proved as an incremental result of [UpReqAlign3]: the main theorem
   [req2_backward_kl_step] plus [r2_backward_kl_step_le] (the le-shaped
   counterpart, matching the upstream policy_iter_backward_kl_step_le@22790);
   here the section's [req2_gibbs_inequality] premise and the [ZAL_pos] witness
   are supplied at the argument face, all section parameters explicit in
   [@]-form, fed once — no reproof, no adaptation; the U2c use site is
   unchanged. *)
Definition req_backward_kl_step_le :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (KLE PSTR (NPX pi_t Hpi_t) PSTR_pos (npx_pos pi_t Hpi_t))
       (plus (mult (req_minus one eta) (KLE PSTR pi_t PSTR_pos Hpi_t))
             (KLE pi_t (NPX pi_t Hpi_t) Hpi_t (npx_pos pi_t Hpi_t))) :=
  r2_backward_kl_step_le S sumf
    sum_ext sum_add sum_linear sum_pos
    log_req_compat log_inv_exp_neg_req
    reward beta beta_pos pi_ref pi_ref_pos eta
    eta_pos ZAL_pos req2_gibbs_inequality.
(* ---- [rlhf_optimal_seed] (former premise, resolved and demoted to a using
   definition — no longer a premise) ----
   FEP assembly resolution = [u2_rlhf_optimal_seed_discharge] (file-level
   Deliverable 3): the [r2_F_align_kl_diff] decomposition + [w_rel_ent_self_zero]
   + the [req2_gibbs_inequality] premise + order preservation under β>0 +
   order-preserving negation via [opp] (the [a_rlhf_optimal] method).  Section
   parameters are fed once, no reproof; the U2a/U2e usage chains keep
   [Print Assumptions] Closed. *)
Definition rlhf_optimal_seed :
  forall (p : S -> R) (Hn : nrm p) (Hp : pos3 p),
    le (JJ p Hp) (JJ PSTR PSTR_pos) :=
  u2_rlhf_optimal_seed_discharge  S sumf sum_ext sum_add sum_linear
                                 log_req_compat log_inv_exp_neg_req
                                 reward beta beta_pos pi_ref pi_ref_pos ZAL_pos
                                 req2_gibbs_inequality.

(* ---- witness-conversion lemmas (positivity witnesses are data: the log
   witness enters the value, and [FA]/[JJ] are req-extensional in the witness;
   results stated in the PSTR_pos witness world are reached after the
   conversion provided here) ---- *)
Lemma r2u_FA_witness_ext :
  forall (p : S -> R) (Hp Hq : pos3 p), req (FA p Hp) (FA p Hq).
Proof.
  intros p Hp Hq.
  unfold FA, req2_F_align.
  apply (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                         (sumf (fun s => mult (p s) (AL s)))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hq s)))))).
  - exact (req_refl (sumf (fun s => mult (p s) (AL s)))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                           (sumf (fun s => mult (p s) (log (p s) (Hq s))))
                           (req_refl beta)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (p s) (log (p s) (Hq s)))).
    intro s.
    exact (req_mult_compat (p s) (p s) (log (p s) (Hp s)) (log (p s) (Hq s))
                           (req_refl (p s))
                           (log_req_compat (p s) (p s) (Hp s) (Hq s)
                                           (req_refl (p s)))).
Qed.

Lemma r2u_JJ_witness_ext :
  forall (p : S -> R) (Hp Hq : pos3 p), req (JJ p Hp) (JJ p Hq).
Proof.
  intros p Hp Hq.
  exact (req_opp_compat (FA p Hp) (FA p Hq) (r2u_FA_witness_ext p Hp Hq)).
Qed.

(* ---- wrappers consuming the upstream lemmas (section parameters fed once; no reproof) ---- *)
Lemma w2_pi_next_normalized :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t), req (sumf (NPX pi_t Hpi_t)) one.
Proof.
  intros pi_t Hpi_t.
  exact (w_pi_next_normalized S sumf sum_linear sum_pos reward beta beta_pos                              pi_ref pi_ref_pos eta pi_t Hpi_t).
Qed.

Lemma w2_pi_star_normalized : req (sumf PSTR) one.
Proof.
  exact (w_pi_star_normalized S sumf sum_linear reward beta beta_pos pi_ref ZAL_pos).
Qed.

Lemma w2_rel_ent_self_zero :
  forall (p : S -> R) (Hp : pos3 p), req (KLE p p Hp Hp) zero.
Proof.
  intros p Hp.
  exact (w_rel_ent_self_zero S sumf sum_ext sum_linear p Hp).
Qed.

Lemma w2_policy_improvement_mono :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    le (JJ pi_t Hpi_t) (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  exact (r2_policy_improvement_mono S sumf sum_ext sum_add sum_linear sum_pos                                    log_req_compat log_inv_exp_neg_req                                    reward beta beta_pos pi_ref pi_ref_pos                                    eta eta_pos eta_le_one                                    req2_gibbs_inequality pi_t Hpi_t Hn).
Qed.

Lemma w2_gap_diff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (req_minus (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
        (mult beta
              (plus (mult (req_minus (inv_pos eta eta_pos) one)
                          (KLE (NPX pi_t Hpi_t) pi_t
                               (npx_pos pi_t Hpi_t) Hpi_t))
                    (mult (inv_pos eta eta_pos)
                          (KLE pi_t (NPX pi_t Hpi_t)
                               Hpi_t (npx_pos pi_t Hpi_t))))).
Proof.
  intros pi_t Hpi_t Hn.
  exact (r2_gap_diff S sumf sum_ext sum_add sum_linear sum_pos                     log_req_compat log_inv_exp_neg_req                     reward beta beta_pos pi_ref pi_ref_pos eta eta_pos                     pi_t Hpi_t Hn).
Qed.

(* exit assembly of [req_gibbs_equality]: [sum_zero_nonneg] and the log bridge
   premises fed once.
   The log_inv_one_inv premise of [req_log_inv_one_inv] (the [UpReqAlgebra]
   [ReqLogBridge] lemma) demands an arbitrary [Hi] — aligned after conversion
   by [log_req_witness_compat]). *)
Lemma w2_gibbs_eq :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    nrm p -> nrm q -> req (KLE p q Hp Hq) zero ->
    forall s : S, req (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl0 s.
  exact (req_gibbs_equality S sumf sum_ext sum_add sum_linear sum_zero_nonneg                            (fun (x : R) (Hx : lt zero x)                                     (Hi : lt zero (inv_pos x Hx)) =>                               req_trans (log (inv_pos x Hx) Hi)                                         (log (inv_pos x Hx) (inv_pos_pos x Hx))                                         (opp (log x Hx))                                 (log_req_witness_compat  log_req_compat                                                         (inv_pos x Hx)                                                         Hi (inv_pos_pos x Hx))                                 (req_log_inv_one_inv log_req_compat x Hx))                            log_le_linear log_eq_linear p q Hp Hq                            Hnp Hnq Hkl0 s).
Qed.

(* ============================================================ *)
(* Main body 1: pointwise req extensionality of the alignment objective in      *)
(* the policy (counterpart of the upstream u2_align_objective_ext@23396)        *)
(*   upstream proof: unfold align_objective; id_cong opp; free_energy_ext.      *)
(*   req counterpart: [JJ] ≡ [opp (req2_F_align)]; FA extensionality =          *)
(*   [sum_ext] + [log_req_compat] assembly.                                     *)
(* ============================================================ *)
Theorem req_u2_align_objective_ext :
  forall (p q : S -> R) (Hp : pos3 p) (Hq : pos3 q),
    (forall s : S, req (p s) (q s)) -> req (JJ p Hp) (JJ q Hq).
Proof.
  intros p q Hp Hq Hpq.
  unfold JJ, req2_J.
  apply (req_opp_compat (req2_F_align S sumf reward beta pi_ref pi_ref_pos p Hp)
                        (req2_F_align S sumf reward beta pi_ref pi_ref_pos q Hq)).
  unfold req2_F_align.
  apply (req_plus_compat (sumf (fun s => mult (p s) (AL s)))
                         (sumf (fun s => mult (q s) (AL s)))
                         (mult beta (sumf (fun s => mult (p s) (log (p s) (Hp s)))))
                         (mult beta (sumf (fun s => mult (q s) (log (q s) (Hq s)))))).
  - apply (sum_ext (fun s => mult (p s) (AL s))
                   (fun s => mult (q s) (AL s))).
    intro s.
    exact (req_mult_compat (p s) (q s) (AL s) (AL s) (Hpq s) (req_refl (AL s))).
  - apply (req_mult_compat beta beta
                           (sumf (fun s => mult (p s) (log (p s) (Hp s))))
                           (sumf (fun s => mult (q s) (log (q s) (Hq s))))
                           (req_refl beta)).
    apply (sum_ext (fun s => mult (p s) (log (p s) (Hp s)))
                   (fun s => mult (q s) (log (q s) (Hq s)))).
    intro s.
    exact (req_mult_compat (p s) (q s) (log (p s) (Hp s)) (log (q s) (Hq s))
                           (Hpq s)
                           (log_req_compat (p s) (q s) (Hp s) (Hq s) (Hpq s))).
Qed.

(* ============================================================ *)
(* U2a: [pi_star] is a fixed point of the one-step improvement operator [NPX]   *)
(*   (counterpart of the upstream u2_pi_next_pi_star_fixed@23425; a six-step    *)
(*   chain, step by step: squeeze J to an equality -> gap identity -> beta      *)
(*   cancellation -> nonnegativity -> a zero sum of nonnegatives ->             *)
(*   pointwise conclusion via gibbs_equality)                                   *)
(* ============================================================ *)
Theorem req_u2_pi_next_pi_star_fixed :
  forall (ps_pos : pos3 PSTR) (ps_norm : nrm PSTR),
    forall s : S, req (NPX PSTR ps_pos s) (PSTR s).
Proof.
  intros ps_pos ps_norm s0.
  set (Np := NPX PSTR ps_pos).
  set (K1 := KLE Np PSTR (npx_pos PSTR ps_pos) ps_pos).
  set (K2 := KLE PSTR Np ps_pos (npx_pos PSTR ps_pos)).
  assert (HNp_norm : nrm Np) by exact (w2_pi_next_normalized PSTR ps_pos).
  (* 1. squeeze: J(NPX pi_star) <= J(pi_star) and J(pi_star) <= J(NPX pi_star);
       the right inequality is stated in the PSTR_pos witness world and reaches
       ps_pos after conversion by [r2u_JJ_witness_ext] *)
  assert (Hopt : le (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR PSTR_pos))
    by exact (rlhf_optimal_seed Np HNp_norm (npx_pos PSTR ps_pos)).
  assert (HoptR : le (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
    by exact (le_id_r (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR PSTR_pos)
                      (JJ PSTR ps_pos)
                      (r2u_JJ_witness_ext PSTR PSTR_pos ps_pos) Hopt).
  assert (Hmono : le (JJ PSTR ps_pos) (JJ Np (npx_pos PSTR ps_pos)))
    by exact (w2_policy_improvement_mono PSTR ps_pos ps_norm).
  assert (Hjeq : req (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
    by exact (le_antisym _ _ HoptR Hmono).
  assert (Hdiff0 : req (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                  (JJ PSTR ps_pos)) zero)
    by exact (req_minus_self_zero _ _ Hjeq).
  (* 2. gap identity: J(NPX pi_star) − J(pi_star) == beta·[(1/eta−1)·K1 + (1/eta)·K2] *)
  assert (Hgap : req (req_minus (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
                    (mult beta
                          (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2))))
    by exact (w2_gap_diff PSTR ps_pos ps_norm).
  (* 3. cancellation by beta > 0 ([req_mult_cancel_l]): the bracketed sum == 0 *)
  assert (HX0 : req (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                          (mult (inv_pos eta eta_pos) K2)) zero).
  { apply (req_mult_cancel_l beta
                             (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                   (mult (inv_pos eta eta_pos) K2))
                             zero beta_pos).
    exact (req_trans (mult beta
                           (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                 (mult (inv_pos eta eta_pos) K2)))
                     (req_minus (JJ Np (npx_pos PSTR ps_pos)) (JJ PSTR ps_pos))
                     (mult beta zero)
                     (req_sym (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                         (JJ PSTR ps_pos))
                              (mult beta
                                    (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                          (mult (inv_pos eta eta_pos) K2)))
                              Hgap)
                     (req_trans (req_minus (JJ Np (npx_pos PSTR ps_pos))
                                           (JJ PSTR ps_pos))
                                zero
                                (mult beta zero)
                                Hdiff0
                                (req_sym (mult beta zero) zero
                                         (mult_zero beta)))). }
  (* 4. nonnegativity: (1/eta−1) >= 0 (one step via [r2_inv_ge_one]), K1 >= 0, K2 >= 0 *)
  assert (HP : le zero (req_minus (inv_pos eta eta_pos) one))
    by exact (req_le_minus_nonneg one (inv_pos eta eta_pos)
                                  (r2_inv_ge_one eta eta_pos eta_le_one)).
  assert (HK1 : le zero K1)
    by exact (req2_gibbs_inequality Np PSTR (npx_pos PSTR ps_pos) ps_pos).
  assert (HK2 : le zero K2)
    by exact (req2_gibbs_inequality PSTR Np ps_pos (npx_pos PSTR ps_pos)).
  assert (HPK1 : le zero (mult (req_minus (inv_pos eta eta_pos) one) K1))
    by exact (r2_le_mult_nonneg _ _ HP HK1).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2))
    by exact (r2_le_mult_nonneg _ _
             (lt_le_iff zero (inv_pos eta eta_pos) (inl (inv_pos_pos eta eta_pos)))
             HK2).
  (* 5. a sum of nonnegatives is zero => (1/eta)·K2 == 0 => (1/eta > 0) K2 == 0 *)
  assert (HQK2z : req (mult (inv_pos eta eta_pos) K2) zero).
  { apply (req_u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                                  (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                  HQK2 HPK1).
    exact (req_trans (plus (mult (inv_pos eta eta_pos) K2)
                           (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                           (mult (inv_pos eta eta_pos) K2))
                     zero
                     (plus_comm (mult (inv_pos eta eta_pos) K2)
                                (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     HX0). }
  assert (HK2z : req K2 zero).
  { apply (req_mult_cancel_l (inv_pos eta eta_pos) K2 zero
                             (inv_pos_pos eta eta_pos)).
    exact (req_trans (mult (inv_pos eta eta_pos) K2)
                     zero
                     (mult (inv_pos eta eta_pos) zero)
                     HQK2z
                     (req_sym (mult (inv_pos eta eta_pos) zero) zero
                              (mult_zero (inv_pos eta eta_pos)))). }
  (* 6. gibbs_equality: K2 == 0 => pi_star == NPX pi_star pointwise => conclusion ([req_sym]) *)
  assert (Hpi : forall s : S, req (PSTR s) (Np s))
    by (intro s;
        exact (w2_gibbs_eq PSTR Np ps_pos (npx_pos PSTR ps_pos)
                           ps_norm HNp_norm HK2z s)).
  exact (req_sym (PSTR s0) (Np s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* U2b: no progress => fixed point (counterpart of the upstream                 *)
(* u2_no_progress_fixed_point@23517; steps 3–6 mirror U2a, with the goal        *)
(* equality handing over J-diff == 0 directly, no squeeze needed)               *)
(* ============================================================ *)
Theorem req_u2_no_progress_fixed_point :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
    forall s : S, req (NPX pi_t Hpi_t s) (pi_t s).
Proof.
  intros pi_t Hpi_t Hn Hno s0.
  set (Np := NPX pi_t Hpi_t).
  set (K1 := KLE Np pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  set (K2 := KLE pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  assert (HNp_norm : nrm Np) by exact (w2_pi_next_normalized pi_t Hpi_t).
  (* 1. goal difference == 0 (the no-progress premise) *)
  assert (Hdiff0 : req (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t)) zero)
    by exact (req_minus_self_zero _ _ Hno).
  (* 2. gap identity *)
  assert (Hgap : req (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
                    (mult beta
                          (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                (mult (inv_pos eta eta_pos) K2))))
    by exact (w2_gap_diff pi_t Hpi_t Hn).
  (* 3. cancellation by beta > 0 *)
  assert (HX0 : req (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                          (mult (inv_pos eta eta_pos) K2)) zero).
  { apply (req_mult_cancel_l beta
                             (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                   (mult (inv_pos eta eta_pos) K2))
                             zero beta_pos).
    exact (req_trans (mult beta
                           (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                 (mult (inv_pos eta eta_pos) K2)))
                     (req_minus (JJ Np (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t))
                     (mult beta zero)
                     (req_sym (req_minus (JJ Np (npx_pos pi_t Hpi_t))
                                         (JJ pi_t Hpi_t))
                              (mult beta
                                    (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                          (mult (inv_pos eta eta_pos) K2)))
                              Hgap)
                     (req_trans (req_minus (JJ Np (npx_pos pi_t Hpi_t))
                                           (JJ pi_t Hpi_t))
                                zero
                                (mult beta zero)
                                Hdiff0
                                (req_sym (mult beta zero) zero
                                         (mult_zero beta)))). }
  (* 4. nonnegativity *)
  assert (HP : le zero (req_minus (inv_pos eta eta_pos) one))
    by exact (req_le_minus_nonneg one (inv_pos eta eta_pos)
                                  (r2_inv_ge_one eta eta_pos eta_le_one)).
  assert (HK1 : le zero K1)
    by exact (req2_gibbs_inequality Np pi_t (npx_pos pi_t Hpi_t) Hpi_t).
  assert (HK2 : le zero K2)
    by exact (req2_gibbs_inequality pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  assert (HPK1 : le zero (mult (req_minus (inv_pos eta eta_pos) one) K1))
    by exact (r2_le_mult_nonneg _ _ HP HK1).
  assert (HQK2 : le zero (mult (inv_pos eta eta_pos) K2))
    by exact (r2_le_mult_nonneg _ _
             (lt_le_iff zero (inv_pos eta eta_pos) (inl (inv_pos_pos eta eta_pos)))
             HK2).
  (* 5. (1/eta)·K2 == 0 => K2 == 0 *)
  assert (HQK2z : req (mult (inv_pos eta eta_pos) K2) zero).
  { apply (req_u2_nonneg_sum_zero (mult (inv_pos eta eta_pos) K2)
                                  (mult (req_minus (inv_pos eta eta_pos) one) K1)
                                  HQK2 HPK1).
    exact (req_trans (plus (mult (inv_pos eta eta_pos) K2)
                           (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     (plus (mult (req_minus (inv_pos eta eta_pos) one) K1)
                           (mult (inv_pos eta eta_pos) K2))
                     zero
                     (plus_comm (mult (inv_pos eta eta_pos) K2)
                                (mult (req_minus (inv_pos eta eta_pos) one) K1))
                     HX0). }
  assert (HK2z : req K2 zero).
  { apply (req_mult_cancel_l (inv_pos eta eta_pos) K2 zero
                             (inv_pos_pos eta eta_pos)).
    exact (req_trans (mult (inv_pos eta eta_pos) K2)
                     zero
                     (mult (inv_pos eta eta_pos) zero)
                     HQK2z
                     (req_sym (mult (inv_pos eta eta_pos) zero) zero
                              (mult_zero (inv_pos eta eta_pos)))). }
  (* 6. gibbs_equality: K2 == 0 => pi_t == NPX pi_t pointwise => conclusion ([req_sym]) *)
  assert (Hpi : forall s : S, req (pi_t s) (Np s))
    by (intro s;
        exact (w2_gibbs_eq pi_t Np Hpi_t (npx_pos pi_t Hpi_t)
                           Hn HNp_norm HK2z s)).
  exact (req_sym (pi_t s0) (Np s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* U2c: unique fixed point => pi_star (counterpart of the upstream              *)
(* u2_fixed_point_unique@23576)                                                 *)
(*   proof: [Hfix] congruently transports KLE(pi_star‖NPX) == A and             *)
(*     KLE(pi_t‖NPX) == 0; the backward one-step KL inequality (the using       *)
(*     definition [req_backward_kl_step_le], former premise entry 6, resolved)  *)
(*     reduces to A <= (1−eta)·A;                                               *)
(*     [Hma]: (1−eta)·A == A − eta·A, hence A <= A − eta·A; [req_u2_minus_minus] *)
(*     and [req_le_minus_nonneg] give 0 <= −eta·A, and order-preserving         *)
(*     negation twice yields eta·A <= 0;                                        *)
(*     the [req2_gibbs] premise gives 0 <= A, squeezing eta·A == 0, and         *)
(*     cancellation by eta > 0 gives A == 0; [w2_gibbs_eq] makes it pointwise:  *)
(*     pi_t == pi_star pointwise.                                               *)
(* ============================================================ *)
Theorem req_u2_fixed_point_unique :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    (forall s : S, req (NPX pi_t Hpi_t s) (pi_t s)) ->
    forall s : S, req (pi_t s) (PSTR s).
Proof.
  intros pi_t Hpi_t Hn Hfix s0.
  set (Np := NPX pi_t Hpi_t).
  set (A := KLE PSTR pi_t PSTR_pos Hpi_t).
  set (ANp := KLE PSTR Np PSTR_pos (npx_pos pi_t Hpi_t)).
  set (TNp := KLE pi_t Np Hpi_t (npx_pos pi_t Hpi_t)).
  (* 1. congruent transport: KL(pi_star‖Np) == A and KL(pi_t‖Np) == 0 *)
  assert (Hc1 : req ANp A)
    by exact (req_u2_kl_arg2_ext  S sumf sum_ext log_req_compat
                                 PSTR Np pi_t PSTR_pos
                                 (npx_pos pi_t Hpi_t) Hpi_t Hfix).
  assert (Hc2 : req TNp (KLE pi_t pi_t Hpi_t Hpi_t))
    by exact (req_u2_kl_arg2_ext  S sumf sum_ext log_req_compat
                                 pi_t Np pi_t Hpi_t
                                 (npx_pos pi_t Hpi_t) Hpi_t Hfix).
  assert (HC0 : req TNp zero)
    by exact (req_trans TNp (KLE pi_t pi_t Hpi_t Hpi_t) zero Hc2
                         (w2_rel_ent_self_zero pi_t Hpi_t)).
  (* 2. backward one-step KL (the <= bridge): KL(pi_star‖Np) <= (1−eta)·A + KL(pi_t‖Np) *)
  assert (H1 : le ANp (plus (mult (req_minus one eta) A) TNp))
    by exact (req_backward_kl_step_le pi_t Hpi_t Hn).
  assert (H3 : le A (plus (mult (req_minus one eta) A) TNp))
    by exact (le_id_l A ANp (plus (mult (req_minus one eta) A) TNp)
                       (req_sym ANp A Hc1) H1).
  assert (H4 : req (plus (mult (req_minus one eta) A) TNp)
                   (mult (req_minus one eta) A)).
  { exact (req_trans (plus (mult (req_minus one eta) A) TNp)
                     (plus (mult (req_minus one eta) A) zero)
                     (mult (req_minus one eta) A)
                     (req_plus_compat (mult (req_minus one eta) A)
                                      (mult (req_minus one eta) A)
                                      TNp zero
                                      (req_refl (mult (req_minus one eta) A))
                                      HC0)
                     (plus_zero (mult (req_minus one eta) A))). }
  assert (HleA : le A (mult (req_minus one eta) A))
    by exact (le_id_r A (plus (mult (req_minus one eta) A) TNp)
                      (mult (req_minus one eta) A) H4 H3).
  (* 3. (1−eta)·A == A − eta·A, hence A <= A − eta·A *)
  assert (Hma : req (mult (req_minus one eta) A) (req_minus A (mult eta A))).
  { exact (req_trans (mult (req_minus one eta) A)
                     (req_minus (mult one A) (mult eta A))
                     (req_minus A (mult eta A))
                     (req_mult_minus_distr_r one eta A)
                     (req2_minus_compat (mult one A) A (mult eta A) (mult eta A)
                                        (req_trans (mult one A) (mult A one) A
                                                   (mult_comm one A)
                                                   (mult_one A))
                                        (req_refl (mult eta A)))). }
  assert (HleB : le A (req_minus A (mult eta A)))
    by exact (le_id_r A (mult (req_minus one eta) A)
                      (req_minus A (mult eta A)) Hma HleA).
  (* 4. 0 <= −eta·A ([req_le_minus_nonneg] plus (A − eta·A) − A == −eta·A) *)
  assert (Hz1 : le zero (req_minus (req_minus A (mult eta A)) A))
    by exact (req_le_minus_nonneg A (req_minus A (mult eta A)) HleB).
  assert (Hz2 : le zero (opp (mult eta A))).
  { exact (le_id_r zero (req_minus (req_minus A (mult eta A)) A)
                   (opp (mult eta A))
                   (req_u2_minus_minus A (mult eta A)) Hz1). }
  (* 5. eta·A <= 0 (order-preserving negation twice; opp zero == zero by hand) *)
  assert (Hoppz : req (opp zero) zero).
  { exact (req_plus_cancel_l zero (opp zero) zero
             (req_trans (plus zero (opp zero)) zero (plus zero zero)
                        (plus_opp zero)
                        (req_sym (plus zero zero) zero (plus_zero zero)))). }
  assert (Hopp0 : le (opp (opp (mult eta A))) (opp zero))
    by exact (opp_le_compat zero (opp (mult eta A)) Hz2).
  assert (Hopp1 : le (opp (opp (mult eta A))) zero)
    by exact (le_id_r (opp (opp (mult eta A))) (opp zero) zero Hoppz Hopp0).
  assert (Heta_le0 : le (mult eta A) zero)
    by exact (le_id_l (mult eta A) (opp (opp (mult eta A))) zero
                      (req_sym (opp (opp (mult eta A))) (mult eta A)
                               (req_double_neg (mult eta A)))
                      Hopp1).
  (* 6. 0 <= eta·A (the [req2_gibbs] premise: 0 <= A; eta >= 0 => 0 <= eta·A) *)
  assert (HA0 : le zero A)
    by exact (req2_gibbs_inequality PSTR pi_t PSTR_pos Hpi_t).
  assert (Heta0 : le zero eta)
    by exact (lt_le_iff zero eta (inl eta_pos)).
  assert (HX0 : le zero (mult eta A))
    by exact (r2_le_mult_nonneg eta A Heta0 HA0).
  (* 7. eta·A == 0 => (cancellation by eta > 0) A == 0 => [w2_gibbs_eq] => pi_t == pi_star *)
  assert (HXz : req (mult eta A) zero)
    by exact (req_sym zero (mult eta A)
                      (le_antisym zero (mult eta A) HX0 Heta_le0)).
  assert (HAz : req A zero).
  { exact (req_mult_cancel_l eta A zero eta_pos
             (req_trans (mult eta A) zero (mult eta zero) HXz
                        (req_sym (mult eta zero) zero (mult_zero eta)))). }
  assert (HPSTRn : nrm PSTR) by exact w2_pi_star_normalized.
  assert (Hpi : forall s : S, req (PSTR s) (pi_t s))
    by (intro s;
        exact (w2_gibbs_eq PSTR pi_t PSTR_pos Hpi_t HPSTRn Hn HAz s)).
  exact (req_sym (PSTR s0) (pi_t s0) (Hpi s0)).
Qed.

(* ============================================================ *)
(* Corollary: no progress => already optimal (counterpart of the upstream       *)
(* u2_no_progress_optimal@23718; assembly of U2b + U2c)                         *)
(* ============================================================ *)
Theorem req_u2_no_progress_optimal :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
    forall s : S, req (pi_t s) (PSTR s).
Proof.
  intros pi_t Hpi_t Hn Hno s0.
  assert (Hfp : forall s : S, req (NPX pi_t Hpi_t s) (pi_t s))
    by (intro s; exact (req_u2_no_progress_fixed_point pi_t Hpi_t Hn Hno s)).
  exact (req_u2_fixed_point_unique pi_t Hpi_t Hn Hfp s0).
Qed.

(* ============================================================ *)
(* Converse: already optimal => no progress (counterpart of the upstream        *)
(* u2_optimal_no_progress@23737; pointwise equality + objective extensionality  *)
(* give J(pi_t) == J(pi_star); the rlhf premise and the monotonicity squeeze)   *)
(* ============================================================ *)
Theorem req_u2_optimal_no_progress :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
    (forall s : S, req (pi_t s) (PSTR s)) ->
    req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t).
Proof.
  intros pi_t Hpi_t Hn Hpi.
  assert (HNp_norm : nrm (NPX pi_t Hpi_t))
    by exact (w2_pi_next_normalized pi_t Hpi_t).
  assert (Hext : req (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos))
    by exact (req_u2_align_objective_ext pi_t PSTR Hpi_t PSTR_pos Hpi).
  assert (Hopt : le (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ PSTR PSTR_pos))
    by exact (rlhf_optimal_seed (NPX pi_t Hpi_t) HNp_norm
                                (npx_pos pi_t Hpi_t)).
  assert (Hmono : le (JJ pi_t Hpi_t)
                     (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)))
    by exact (w2_policy_improvement_mono pi_t Hpi_t Hn).
  assert (Hle1 : le (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ pi_t Hpi_t))
    by exact (le_id_r (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                      (JJ PSTR PSTR_pos) (JJ pi_t Hpi_t)
                      (req_sym (JJ pi_t Hpi_t) (JJ PSTR PSTR_pos) Hext)
                      Hopt).
  exact (le_antisym (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t))
                    (JJ pi_t Hpi_t) Hle1 Hmono).
Qed.

(* ============================================================ *)
(* Equivalence characterization (both directions, with the Set-level            *)
(* [And] := A*B product; counterpart of the upstream                            *)
(* u2_objective_eq_optimal_iff@23769)                                           *)
(* ============================================================ *)
Theorem req_u2_objective_eq_optimal_iff :
  forall (pi_t : S -> R) (Hpi_t : pos3 pi_t) (Hn : nrm pi_t),
  And (req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t) ->
        forall s : S, req (pi_t s) (PSTR s))
      ((forall s : S, req (pi_t s) (PSTR s)) ->
        req (JJ (NPX pi_t Hpi_t) (npx_pos pi_t Hpi_t)) (JJ pi_t Hpi_t)).
Proof.
  intros pi_t Hpi_t Hn.
  split.
  - intro H. exact (req_u2_no_progress_optimal pi_t Hpi_t Hn H).
  - intro H. exact (req_u2_optimal_no_progress pi_t Hpi_t Hn H).
Qed.

End ReqU2FixedPoint.
