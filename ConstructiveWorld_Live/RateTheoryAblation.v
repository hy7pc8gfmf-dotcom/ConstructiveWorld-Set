(* ConstructiveWorld-Set -- RateTheoryAblation: ablation control pieces of
   the Markov-chain convergence-rate theory (theorem 4.1-4.4 decomposition). *)
(** * RateTheoryAblation: ablation control pieces for Markov-chain
    convergence rates, carried on Set.

    Mission.  [rta_delta_le_one_of_minorization] derives delta <= 1 from the
      row-normalization + uniform-reference + pointwise-minorization premises
      alone (the first cut removing the redundant delta_le_one premise at the
      theorem 4.1/4.2 interfaces); [rta_iter_contraction_wo_le_one] is the
      premise-thinned n-step iterate contraction; [rta_strict_branch_real] is
      the Real-carrier strict branch of theorem 4.4; [rta_rpow_powb_eq] is
      the pointwise bridge between the rate carriers [tv_rpow] and [powb_pow];
      [rta_omd_powb_mono_b] is the theorem 4.3 consumption form.

    Dependencies.  Stdlib [List], [QArith.Qring]; the chain S01..S15 of this
      development, [UpRealLeB], [UpRealLeB2], [G07_KLWall], [KLWallClosed]
      and [UpTVDoeblin]; the [CW_ConstructiveWorld_219] dependency note of
      the baseline header.

    References.  Component-wise decomposition of Markov-chain convergence
      rates (ablation analysis); theorems 4.1, 4.2, 4.3 and 4.4 of the
      source paper; [tv_doeblin_iter] interface order pinned at L1991.

    Constructivity.  All statements are carried by Set (order predicates and
      equality are Set-valued, no Prop leakage); every proof ends in [Qed];
      zero admission literals, no classical logic; [Print Assumptions]
      reports Closed for the five main statements.

    Build.  [rocq c -native-compiler no -q -Q . "" RateTheoryAblation.v] on
      Rocq 9.1.0, compilation wrapped by the cpu_guard wrapper. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpTVDoeblin.

(* ============================================================ *)
(* Sec. 1 delta_le_one premise elimination: minorization +        *)
(*   two-sided normalization implies delta <= 1 (the first cut    *)
(*   removing the redundant delta_le_one premise at the theorem   *)
(*   4.1/4.2 interfaces)                                          *)
(* ============================================================ *)

Theorem rta_delta_le_one_of_minorization :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  (* Pointwise minorization (take i := nil; K_row/Hmin hold for every i) *)
  pose proof (HKrow nil) as Hrow0.
  assert (Hpt : forall j : list Real,
           real_le (real_mult delta (u j)) (K nil j))
    by (intro j; apply Hmin).
  (* Monotonicity of the pointwise sum: sum(delta*u) <= sum(K nil) *)
  assert (Hle : real_le
                  (real_list_sum (list Real)
                     (fun j : list Real => real_mult delta (u j)) states)
                  (real_list_sum (list Real) (K nil) states)).
  { exact (@real_list_sum_le (list Real)
             (fun j : list Real => real_mult delta (u j))
             (K nil) states Hpt). }
  (* LHS: sum(delta*u) == delta*sum(u) == delta*1 == delta (scalar-linearity + setoid chain) *)
  assert (Hlhs : real_eq
                   (real_list_sum (list Real)
                      (fun j : list Real => real_mult delta (u j)) states)
                   delta).
  { apply (real_eq_trans _
             (real_mult delta (real_list_sum (list Real) u states)) _).
    - exact (@real_list_sum_linear (list Real) delta u states).
    - apply (real_eq_trans _ (real_mult delta real_one) _).
      + apply (RealSetoid.real_eq_mult_compat delta
                 (real_list_sum (list Real) u states)
                 delta real_one (real_eq_refl delta) Hunorm).
      + exact (real_mult_one delta). }
  (* Assembly: delta <= sum(delta*u) <= sum(K nil) == 1 *)
  apply (real_le_trans delta
           (real_list_sum (list Real)
              (fun j : list Real => real_mult delta (u j)) states)
           real_one).
  - apply (RealSetoid.real_eq_le _ _).
    exact (real_eq_sym _ _ Hlhs).
  - apply (real_le_trans _
             (real_list_sum (list Real) (K nil) states) _).
    + exact Hle.
    + apply (RealSetoid.real_eq_le _ _). exact Hrow0.
Qed.

(* ============================================================ *)
(* Sec. 2 Theorem 4.2 premise-thinning instance: the n-step       *)
(*   iterate contraction WITHOUT delta_le_one (hence without      *)
(*   delta_pos/K_pos/n_pos) -- delta <= 1 is derived from         *)
(*   minorization by Sec. 1 (consumes the full-argument form of   *)
(*   tv_doeblin_iter after its extraction; interface argument     *)
(*   order empirically pinned at UpTVDoeblin.v L1991)             *)
(* ============================================================ *)

Theorem rta_iter_contraction_wo_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
  (forall i : list Real,
     real_eq (real_list_sum (list Real) (K i) states) real_one) ->
  real_eq (real_list_sum (list Real) u states) real_one ->
  (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
  (forall f : list Real -> Real,
     real_le (real_abs (real_list_sum (list Real) f states))
             (real_list_sum (list Real)
                (fun w : list Real => real_abs (f w)) states)) ->
  forall (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tv_doeblin states
             (tv_titer states K n mu) (tv_titer states K n nu))
          (real_mult (tv_rpow (tv_omd delta) n)
                     (tv_doeblin states mu nu)).
Proof.
  intros states K u delta HKrow Hunorm Hmin Labs n mu nu Hmu Hnu.
  apply (tv_doeblin_iter states K HKrow u Hunorm delta           (rta_delta_le_one_of_minorization states K u delta              HKrow Hunorm Hmin)           Hmin Labs n mu nu Hmu Hnu).
Qed.

(* ============================================================ *)
(* Sec. 3 Real-carrier counterpart branch of Theorem 4.4: the     *)
(*   composition of a positivity certificate with the Bishop      *)
(*   contraction for 0 <= eta < 1 (klc_strict_branch is Q-carrier *)
(*   only; this piece is Real-carrier, the positivity certificate *)
(*   obtained constructively by the translation chain of real_lt  *)
(*   -- the generalized tv_omd_pos_of_lt form)                    *)
(* ============================================================ *)

Theorem rta_strict_branch_real : forall (eta : Real) (t t1 : nat),
  real_le real_zero eta -> real_lt eta real_one -> NatLe t t1 ->
  prod (real_lt real_zero (real_plus real_one (real_opp eta)))
       (real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
                  (powb_pow (real_plus real_one (real_opp eta)) t)).
Proof.
  intros eta t t1 H0 Hlt Hle. split.
  - (* 0 < 1-eta: translation of eta < 1 + the eta+(-eta)==0 reshaping (same chain as tv_omd_pos_of_lt) *)
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus eta (real_opp eta))
             (real_plus real_one (real_opp eta))).
    + exact (real_eq_sym (real_plus eta (real_opp eta)) real_zero
               (real_plus_opp eta)).
    + exact (real_lt_plus_compat_lt_le eta real_one (real_opp eta)
               (real_opp eta) Hlt (real_le_refl (real_opp eta))).
  - (* Bishop contraction: klc_closed_powb_mono is used with 0 <= eta <= 1 *)
    exact (klc_closed_powb_mono eta t t1 H0 (inl Hlt) Hle).
Qed.

(* ============================================================ *)
(* Sec. 4 Rate-layer bridge: pointwise equality of tv_rpow (the   *)
(*   Sec. 4.2 rate carrier, UpTVDoeblin L1552) and powb_pow (the  *)
(*   Sec. 4.3 rate-algebra carrier, G07_KLWall L1025) -- an eq    *)
(*   proof of two isomorphic Fixpoints (the interface translation *)
(*   piece between the rate layer and the rate-algebra layer)     *)
(* ============================================================ *)

Lemma rta_rpow_powb_eq : forall (a : Real) (n : nat),
  real_eq (tv_rpow a n) (powb_pow a n).
Proof.
  intros a n. induction n as [| n IH].
  - cbn [tv_rpow powb_pow]. apply real_eq_refl.
  - cbn [tv_rpow powb_pow].
    apply (RealSetoid.real_eq_mult_compat a (tv_rpow a n)
             a (powb_pow a n) (real_eq_refl a) IH).
Qed.

(* ============================================================ *)
(* Sec. 5 The consumption form of Theorem 4.3 on the tv_rpow rate *)
(*   layer: Bishop monotonicity of the power sequence of the      *)
(*   Doeblin residual rate (1-delta) -- klc_closed_powb_mono is   *)
(*   carried to the rate layer via the Sec. 4 bridge (the         *)
(*   degenerate-endpoint handling of the Sec. 4.1/4.2 rate        *)
(*   algebra closes here)                                         *)
(* ============================================================ *)

Theorem rta_omd_powb_mono_b : forall (delta : Real) (n m : nat),
  real_le real_zero delta -> real_le delta real_one -> NatLe n m ->
  real_le_b (tv_rpow (tv_omd delta) m) (tv_rpow (tv_omd delta) n).
Proof.
  intros delta n m H0 H1 Hle.
  pose proof (klc_closed_powb_mono delta n m H0 H1 Hle) as Hklc.
  unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           (powb_pow (real_plus real_one (real_opp delta)) m)
           (tv_rpow (tv_omd delta) m)
           (real_plus (powb_pow (real_plus real_one (real_opp delta)) n) eps)
           (real_plus (tv_rpow (tv_omd delta) n) eps)).
  - exact (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) m).
  - apply (RealSetoid.real_eq_plus_compat
             (powb_pow (real_plus real_one (real_opp delta)) n) eps
             (tv_rpow (tv_omd delta) n) eps
             (rta_rpow_powb_eq (real_plus real_one (real_opp delta)) n)
             (real_eq_refl eps)).
  - exact (Hklc eps Heps).
Qed.

(* ============================================================ *)
(* Audit port (G4: zero axioms, Closed; G1 min-pa audit slot)     *)
(* ============================================================ *)
Print Assumptions rta_delta_le_one_of_minorization.
Print Assumptions rta_iter_contraction_wo_le_one.
Print Assumptions rta_strict_branch_real.
Print Assumptions rta_rpow_powb_eq.
Print Assumptions rta_omd_powb_mono_b.
