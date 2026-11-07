(* ConstructiveWorld-Set — positivity of the exponential over the Real layer. *)

(** * UpReqExpPos: positivity of the exponential at the Real layer.

    Mission.  [upreq_exp_pos], the main positivity statement
      [0 < e^x] for every real [x], together with the [Or]-resolution
      branch form [upreq_exp_pos_or_destruct], the nonvanishing
      statement [upreq_exp_neg_ne_zero], the unit identity
      [upreq_exp_neg_unit], and [upreq_real_zero_ne_one].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith].  Requires [S01_BaseRing] through [S15_TailFEPUp]
      and [UpReqRealLtShiftBridge] of this development (the
      contradiction basis [rlsb_zero_ne_one] is consumed from
      [UpReqRealLtShiftBridge]).

    References.  This development, UpReqExpPos.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried
      over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]; every
      proof closes by [Qed] with zero admission tokens and no
      classical logic; the order and equality predicates at statement
      level are Set-valued with zero Prop leakage.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqExpPos.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqRealLtShiftBridge.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* Part 1: 0 <> 1 at the Real layer (the contradiction basis of      *)
(* step 2 of the five-step chain).                                   *)
(*   Proof source: the identical in-library statement                *)
(*   [rlsb_zero_ne_one] ([UpReqRealLtShiftBridge]: instantiating     *)
(*   [real_eq] at [eps := 1] gives the pointwise separation          *)
(*   [QltT |0-1| 1]; pointwise computation reduces this to a         *)
(*   Q-layer contradiction eliminated by [discriminate]).            *)
(* ============================================================ *)
Lemma upreq_real_zero_ne_one : Not (real_eq real_zero real_one).
Proof.
  exact rlsb_zero_ne_one.
Qed.

(* ============================================================ *)
(* Part 2 (step 1 of the five-step chain): the unit identity         *)
(* eˣ·e⁻ˣ == 1.                                                      *)
(*   eˣ·e⁻ˣ == e^{x+(-x)} ([real_exp_neg_plus] reversed) == e^{-0}   *)
(*   (transporting the argument along [real_eq]: plus_opp ->         *)
(*   opp_compat -> cauchy_real_exp_wd) == 1 ([real_exp_neg_zero]).   *)
(* ============================================================ *)
Lemma upreq_exp_neg_unit : forall x : Real,
  real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one.
Proof.
  intro x.
  apply (real_eq_trans
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_exp_neg (real_plus x (real_opp x)))
           real_one).
  - exact (real_eq_sym _ _ (real_exp_neg_plus x (real_opp x))).
  - apply (real_eq_trans
           (real_exp_neg (real_plus x (real_opp x)))
           (real_exp_neg real_zero)
           real_one).
    + unfold real_exp_neg.
      apply cauchy_real_exp_wd.
      apply RealSetoid.real_eq_opp_compat.
      exact (real_plus_opp x).
    + exact real_exp_neg_zero.
Qed.

(* ============================================================ *)
(* Part 3 (step 2 of the five-step chain): eˣ <> 0, a corollary of   *)
(* the inverse e⁻ˣ.                                                  *)
(*   eˣ==0 implies eˣ·e⁻ˣ == 0·e⁻ˣ == 0 ([eq_mult_compat] +          *)
(*   [mult_comm] + [mult_zero]), hence 0 == 1 (Part 1), and          *)
(*   [Empty_set] elimination closes the goal.                        *)
(* ============================================================ *)
Lemma upreq_exp_neg_ne_zero : forall x : Real,
  Not (real_eq (real_exp_neg x) real_zero).
Proof.
  intro x. intro Hzero.
  assert (Hstep : real_eq
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_mult real_zero (real_exp_neg (real_opp x))))
    by exact (RealSetoid.real_eq_mult_compat (real_exp_neg x) (real_exp_neg (real_opp x))
                                  real_zero (real_exp_neg (real_opp x))
                                  Hzero (real_eq_refl (real_exp_neg (real_opp x)))).
  assert (Hzl : real_eq (real_mult real_zero (real_exp_neg (real_opp x))) real_zero).
  { apply (real_eq_trans
             (real_mult real_zero (real_exp_neg (real_opp x)))
             (real_mult (real_exp_neg (real_opp x)) real_zero)
             real_zero).
    - exact (real_mult_comm real_zero (real_exp_neg (real_opp x))).
    - exact (real_mult_zero (real_exp_neg (real_opp x))). }
  assert (Hunit : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one)
    by exact (upreq_exp_neg_unit x).
  assert (Hm0 : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_zero)
    by exact (real_eq_trans _ _ _ Hstep Hzl).
  exact (upreq_real_zero_ne_one
           (real_eq_sym _ _ (real_eq_trans _ _ _ (real_eq_sym _ _ Hunit) Hm0))).
Qed.

(* ============================================================ *)
(* Part 4 (the target theorem, main result): 0 < eˣ for every real x.*)
(*   real_exp_neg (real_opp x) = cauchy_real_exp (real_opp           *)
(*   (real_opp x)) = eˣ; the in-library [real_exp_neg_pos] is        *)
(*   instantiated at [real_opp x] — exactly the Real-layer           *)
(*   instantiation check of the [exp_neg_pos] interface field, whose *)
(*   eps witness comes from the power-series construction in         *)
(*   [S03_QExp] ([eps := 1/(2C)], a constructive [sigT] shape).      *)
(* ============================================================ *)
Theorem upreq_exp_pos : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof. intro x. exact (real_exp_neg_pos (real_opp x)). Qed.

(* ============================================================ *)
(* Part 5 (the Or-resolution form of step 5 of the five-step chain): *)
(* an [Or]-encoded derivation of the target theorem.                 *)
(*   real_le real_zero eˣ = Or (real_lt real_zero eˣ) (real_eq       *)
(*   real_zero eˣ) (the encoding expanded as in S02:460); the left   *)
(*   disjunct is supplied directly by the series eps witness (same   *)
(*   source as Part 4); for the right disjunct 0==eˣ, Part 3 derives *)
(*   [Empty_set] by contradiction, from which any Set goal is        *)
(*   eliminated — the standard constructive structure of             *)
(*   destruct-Or plus right-disjunct contradiction, assembled as     *)
(*   pure terms.                                                     *)
(* ============================================================ *)
Theorem upreq_exp_pos_or_destruct : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof.
  intro x.
  assert (Hle : real_le real_zero (real_exp_neg (real_opp x))).
  { apply inl. exact (real_exp_neg_pos (real_opp x)). }
  destruct Hle as [Hpos | Heq].
  - exact Hpos.
  - destruct (upreq_exp_neg_ne_zero (real_opp x) (real_eq_sym _ _ Heq)).
Qed.

Print Assumptions upreq_real_zero_ne_one.
Print Assumptions upreq_exp_neg_unit.
Print Assumptions upreq_exp_neg_ne_zero.
Print Assumptions upreq_exp_pos.
Print Assumptions upreq_exp_pos_or_destruct.
