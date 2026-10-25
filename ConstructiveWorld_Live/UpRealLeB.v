(* ConstructiveWorld-Set — Bishop-form non-strict order on the constructive reals, with completion lemmas. *)

(** * UpRealLeB: the Bishop-form non-strict order [real_le_b] and its completion theory.

    Mission.  The Bishop predicate [real_le_b x y := forall eps > 0, x < y +
      eps] on the Cauchy reals, the one-way bridge [real_le_to_le_b] from the
      Or-encoded order, the completion lemma [real_le_closure_b] (an eps-family
      with an explicit positivity certificate completes to Bishop form), its
      [D := 1] specialization [real_le_closure_b_one], and applications: RLHF
      optimality [real_rlhf_optimal_B], PPO conservativeness
      [real_ppo_conservative_B], and eighteen Bishop-form companions.

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].  Requires the
      backbone [S01_BaseRing] .. [S15_TailFEPUp]; all work is on the global
      constructive reals [Real] of this development.

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All statements are carried by [Set]; the bridge is
      one-way by design (the converse decides a constructively undecidable
      disjunction — see the closing register).  [real_ppo_conservative_B]
      carries an explicit positivity premise and an honest scalar-extraction
      interface [real_sum_over_S_linear].  Statements extract with
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpRealLeB.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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

(* ============================================================ *)
(* Part A: the Bishop predicate, the one-way bridge, the completion lemma. *)
(* ============================================================ *)

(* Bishop non-strict order: x <=_B y := forall eps > 0, x < y + eps            *)
(* (a Set-level forall over [Real]; conclusion and premises all in [Set]).     *)
Definition real_le_b (x y : Real) : Set :=
  forall eps : Real, real_lt real_zero eps -> real_lt x (real_plus y eps).

(* Helper: 0 < eps implies y < y + eps (order translation plus y + 0 == y). *)
Lemma real_lt_plus_r_zero : forall (y eps : Real),
  real_lt real_zero eps -> real_lt y (real_plus y eps).
Proof.
  intros y eps Heps.
  apply (RealSetoid.real_lt_id_l y (real_plus y real_zero) (real_plus y eps)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_lt_plus_translate y real_zero eps). exact Heps.
Qed.

(* One-way bridge: Or-encoded [real_le x y] implies [real_le_b x y].          *)
(* lt branch: x < y < y + eps by transitivity; eq branch: rewrite x == y to    *)
(* x < x + eps by compatibility.                                              *)
Lemma real_le_to_le_b : forall x y : Real, real_le x y -> real_le_b x y.
Proof.
  intros x y Hle. unfold real_le_b. unfold real_le in Hle.
  intros eps Heps.
  destruct Hle as [Hlt | Heq].
  - apply (real_lt_trans x y (real_plus y eps)).
    + exact Hlt.
    + apply (real_lt_plus_r_zero y eps). exact Heps.
  - apply (RealSetoid.real_lt_compat x x (real_plus x eps) (real_plus y eps)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_plus_compat x eps y eps).
      * exact Heq.
      * apply real_eq_refl.
    + apply (real_lt_plus_r_zero x eps). exact Heps.
Qed.

(* Completion lemma (core): an eps-remainder family with an explicit           *)
(* positivity certificate for D completes to Bishop form.  Construction:       *)
(* e0 := eps' * inv(2D); then D*e0 == eps'*(inv(2D)*D) < eps'*1 == eps'        *)
(* because inv(2D)*D < 1 (D < 2D gives inv(2D) < inv(D) by anti-monotonicity,  *)
(* so inv(2D)*D < inv(D)*D == 1).  Both Or branches close; no density used.    *)
Lemma real_le_closure_b : forall (x y D : Real),
  real_lt real_zero D ->
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y (real_mult D eps))) ->
  real_le_b x y.
Proof.
  intros x y D HD H. unfold real_le_b. intros eps' Heps'.
  assert (HD2 : real_lt real_zero (real_plus D D))
    by exact (real_plus_positive D D HD HD).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus D D) HD2))
    by exact (real_inv_pos_pos (real_plus D D) HD2).
  assert (He0pos : real_lt real_zero
                     (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus D D) HD2)
                                 Heps' Hinv2pos).
  (* Key bound: D * (eps' * inv(2D)) < eps'. *)
  assert (Hkey : real_lt
                   (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                   eps').
  {
    assert (HDlt : real_lt D (real_plus D D)).
    {
      apply (RealSetoid.real_lt_id_l D (real_plus D real_zero) (real_plus D D)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate D real_zero D). exact HD.
    }
    assert (Hmono : real_lt (real_inv_pos (real_plus D D) HD2) (real_inv_pos D HD))
      by exact (real_inv_pos_lt_contra D (real_plus D D) HD HD2 HDlt).
    assert (Hm1 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D)
                          (real_mult (real_inv_pos D HD) D))
      by exact (real_mult_lt_compat (real_inv_pos (real_plus D D) HD2)
                                    (real_inv_pos D HD) D Hmono HD).
    assert (Heq1 : real_eq (real_mult (real_inv_pos D HD) D) real_one).
    {
      apply (real_eq_trans _ (real_mult D (real_inv_pos D HD)) _).
      - apply real_mult_comm.
      - apply real_inv_pos_correct.
    }
    assert (Hlt2 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D) real_one)
      by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos D HD) D)
                                         real_one Heq1 Hm1).
    assert (Hlt3 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                           (real_mult eps' real_one))
      by exact (real_mult_lt_compat_l (real_mult (real_inv_pos (real_plus D D) HD2) D)
                                      real_one eps' Hlt2 Heps').
    assert (Hlt4 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                           eps')
      by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps'
                                         (real_mult_one eps') Hlt3).
    (* Rewrite D * (eps' * inv(2D)) == eps' * (inv(2D) * D). *)
    assert (HC1 : real_eq (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                          (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))).
    {
      apply (real_eq_trans _ (real_mult (real_mult D eps')
                                        (real_inv_pos (real_plus D D) HD2)) _).
      - apply real_mult_assoc.
      - apply (real_eq_trans _
                 (real_mult (real_mult eps' D) (real_inv_pos (real_plus D D) HD2)) _).
        + apply (RealSetoid.real_eq_mult_compat (real_mult D eps')
                                                (real_inv_pos (real_plus D D) HD2)
                                                (real_mult eps' D)
                                                (real_inv_pos (real_plus D D) HD2)).
          * apply real_mult_comm.
          * apply real_eq_refl.
        + apply (real_eq_trans _
                   (real_mult eps' (real_mult D (real_inv_pos (real_plus D D) HD2))) _).
          * apply real_eq_sym. apply real_mult_assoc.
          * apply (RealSetoid.real_eq_mult_compat eps'
                     (real_mult D (real_inv_pos (real_plus D D) HD2))
                     eps'
                     (real_mult (real_inv_pos (real_plus D D) HD2) D)).
            -- apply real_eq_refl.
            -- apply real_mult_comm.
    }
    exact (RealSetoid.real_lt_id_l _ _ _ HC1 Hlt4).
  }
  destruct (H (real_mult eps' (real_inv_pos (real_plus D D) HD2)) He0pos)
    as [Hlt | Heq].
  - (* lt branch: x < y + D*e0 < y + eps' (order translation + transitivity). *)
    apply (real_lt_trans x
             (real_plus y (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2))))
             (real_plus y eps')).
    + exact Hlt.
    + apply (real_lt_plus_translate y _ _). exact Hkey.
  - (* eq branch: x == y + D*e0 gives x < y + eps' by rewriting. *)
    apply (RealSetoid.real_lt_id_l x
             (real_plus y (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2))))
             (real_plus y eps')).
    + exact Heq.
    + apply (real_lt_plus_translate y _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* Part B: RLHF optimality in Bishop form, J(pi) <=_B J(pi-star), with the        *)
(* D_pos positivity certificate as an existing interface variable.  The       *)
(* section variables mirror the RealRLHFMain consumption face; no new         *)
(* premises — a full upgrade.                                                 *)
(* ============================================================ *)

Section RealRLHFLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_align_r : Real.
Variable Z_align_r_pos : real_lt real_zero Z_align_r.
(* Honest interface (same names and shapes as the RLHF main module). *)
Variable real_gibbs_sum_eps : forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one) (eps : Real),
  real_lt real_zero eps ->
  real_le real_zero
    (real_plus
       (real_sum_over_S
          (fun s : S =>
           real_kl_term (p s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
             (Hp s)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s)))
       eps).
Variable real_kl_decomp_full : forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
  (Hnormp : real_eq (real_sum_over_S p) real_one),
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S =>
                    real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).

(* J(pi) <=_B J(pi-star): the Bishop-form completion of RLHF optimality; the      *)
(* positivity certificate D_pos for D is an existing interface variable, so   *)
(* no new premises are added.                                                 *)
Theorem real_rlhf_optimal_B :
  forall (pi : S -> Real) (Hpi : forall s : S, real_lt real_zero (pi s))
    (Hnormpi : real_eq (real_sum_over_S pi) real_one),
  real_le_b (real_opp (real_free_energy S real_sum_over_S real_base_loss D pi Hpi))
            (real_opp
               (real_free_energy S real_sum_over_S real_base_loss D
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))).
Proof.
  intros pi Hpi Hnormpi.
  unfold real_le_b. intros eps' Heps'.
  assert (HD2 : real_lt real_zero (real_plus D D))
    by exact (real_plus_positive D D D_pos D_pos).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus D D) HD2))
    by exact (real_inv_pos_pos (real_plus D D) HD2).
  assert (He0pos : real_lt real_zero
                     (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus D D) HD2)
                                 Heps' Hinv2pos).
  assert (HDlt : real_lt D (real_plus D D)).
  { apply (RealSetoid.real_lt_id_l D (real_plus D real_zero) (real_plus D D)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate D real_zero D). exact D_pos. }
  assert (Hmono : real_lt (real_inv_pos (real_plus D D) HD2) (real_inv_pos D D_pos))
    by exact (real_inv_pos_lt_contra D (real_plus D D) D_pos HD2 HDlt).
  assert (Hm1 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D)
                        (real_mult (real_inv_pos D D_pos) D))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus D D) HD2)
                                  (real_inv_pos D D_pos) D Hmono D_pos).
  assert (Heq1 : real_eq (real_mult (real_inv_pos D D_pos) D) real_one).
  { apply (real_eq_trans _ (real_mult D (real_inv_pos D D_pos)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hlt2 : real_lt (real_mult (real_inv_pos (real_plus D D) HD2) D) real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos D D_pos) D)
                                       real_one Heq1 Hm1).
  assert (Hlt3 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                         (real_mult eps' real_one))
    by exact (real_mult_lt_compat_l (real_mult (real_inv_pos (real_plus D D) HD2) D)
                                    real_one eps' Hlt2 Heps').
  assert (Hlt4 : real_lt (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))
                         eps')
    by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps'
                                       (real_mult_one eps') Hlt3).
  assert (HC1 : real_eq (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                        (real_mult eps' (real_mult (real_inv_pos (real_plus D D) HD2) D))).
  { apply (real_eq_trans _ (real_mult (real_mult D eps')
                                      (real_inv_pos (real_plus D D) HD2)) _).
    - apply real_mult_assoc.
    - apply (real_eq_trans _
               (real_mult (real_mult eps' D) (real_inv_pos (real_plus D D) HD2)) _).
      + apply (RealSetoid.real_eq_mult_compat (real_mult D eps')
                                              (real_inv_pos (real_plus D D) HD2)
                                              (real_mult eps' D)
                                              (real_inv_pos (real_plus D D) HD2)).
        * apply real_mult_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _
                 (real_mult eps' (real_mult D (real_inv_pos (real_plus D D) HD2))) _).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (RealSetoid.real_eq_mult_compat eps'
                   (real_mult D (real_inv_pos (real_plus D D) HD2))
                   eps'
                   (real_mult (real_inv_pos (real_plus D D) HD2) D)).
          -- apply real_eq_refl.
          -- apply real_mult_comm. }
  assert (Hkey : real_lt
                   (real_mult D (real_mult eps' (real_inv_pos (real_plus D D) HD2)))
                   eps')
    by exact (RealSetoid.real_lt_id_l _ _ _ HC1 Hlt4).
  destruct (real_rlhf_optimal_eps S real_sum_over_S real_base_loss D D_pos
              Z_align_r Z_align_r_pos real_gibbs_sum_eps real_kl_decomp_full
              pi Hpi Hnormpi
              (real_mult eps' (real_inv_pos (real_plus D D) HD2)) He0pos)
    as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

End RealRLHFLeB.

(* ============================================================ *)
(* Part C: PPO conservativeness in Bishop form (conditional upgrade).         *)
(* The residual weight E := sum pi_old*adv needs an explicit positivity       *)
(* premise: E = 0 and E > 0 are constructively indistinguishable and no       *)
(* internal supply chain exists.  The scalar extraction                        *)
(* [real_sum_over_S_linear] is an honest interface (mirroring its namesake).  *)
(* Without a certificate the eps-form [real_ppo_conservative_eps] stands;     *)
(* see the closing register.                                                  *)
(* ============================================================ *)

Section RealPPOLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
(* Honest interface: scalar extraction (mirroring real_sum_over_S_linear). *)
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.

(* Residual weight: E := sum_s pi_old(s) * adv(s). *)
Definition real_ppo_res_weight : Real :=
  real_sum_over_S (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s)).

(* Residual folding: sum pi_old*(eps*adv) == E*eps (pointwise rewriting, scalar extraction, commutativity). *)
Lemma real_ppo_res_fold : forall eps : Real,
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
    (real_mult real_ppo_res_weight eps).
Proof.
  intro eps.
  apply (real_eq_trans _
           (real_sum_over_S
              (fun s : S => real_mult eps (real_mult (real_pi_old s) (real_advantage_fn s))))
           _).
  - apply (real_sum_over_S_ext _ _).
    intro s.
    apply (real_eq_trans _
             (real_mult (real_mult (real_pi_old s) eps) (real_advantage_fn s)) _).
    + apply real_mult_assoc.
    + apply (real_eq_trans _
               (real_mult (real_mult eps (real_pi_old s)) (real_advantage_fn s)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_mult (real_pi_old s) eps)
                                              (real_advantage_fn s)
                                              (real_mult eps (real_pi_old s))
                                              (real_advantage_fn s)).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
      * apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult eps real_ppo_res_weight) _).
    + exact (real_sum_over_S_linear eps
               (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))).
    + apply real_mult_comm.
Qed.

(* PPO conservativeness in Bishop form (conditional: requires the explicit    *)
(* E > 0 certificate; without it the eps-form statement stands unchanged).    *)
Theorem real_ppo_conservative_B :
  real_lt real_zero real_ppo_res_weight ->
  real_le_b
    (real_sum_over_S
       (fun s : S =>
        real_mult (real_pi_old s)
          (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                               (real_ppo_clip_ epsilon
                                  (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                     (real_advantage_fn s))))
    (real_sum_over_S
       (fun s : S =>
        real_mult (real_pi_old s)
          (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                     (real_advantage_fn s)))).
Proof.
  intros HEpos.
  apply (real_le_closure_b _ _ real_ppo_res_weight HEpos).
  intros eps Heps.
  apply (real_le_trans _
           (real_plus
              (real_sum_over_S
                 (fun s : S =>
                  real_mult (real_pi_old s)
                    (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                               (real_advantage_fn s))))
              (real_sum_over_S
                 (fun s : S =>
                  real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))) _).
  - exact (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
             real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
             real_pi_old_pos real_advantage_fn real_advantage_pos epsilon eps Heps).
  - apply (real_le_plus_compat _ _ _ _ (real_le_refl _)).
    apply (RealSetoid.real_eq_le _ _).
    apply (real_ppo_res_fold eps).
Qed.

End RealPPOLeB.

(* ============================================================ *)
(* Part D: Bishop-form completions for eps-remainder families, all via the    *)
(* Part A completion lemma — the D := 1 specialization and the native D*eps   *)
(* instance; per-lemma certificate chains are noted at each statement.        *)
(* ============================================================ *)

(* D.0 Specialized completion: a plain-eps family (forall eps > 0, x <=       *)
(* y + eps) gives x <=_B y.  Certificate: D := real_one with the existing     *)
(* closed lemma real_lt_zero_one (no new premises); the only rewriting face   *)
(* is 1*eps == eps, via slot-wise compatibility and right-end equality        *)
(* rewriting.                                                                 *)
Lemma real_le_closure_b_one : forall x y : Real,
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y eps)) ->
  real_le_b x y.
Proof.
  intros x y H.
  apply (real_le_closure_b x y real_one real_lt_zero_one).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r x (real_plus y eps)
           (real_plus y (real_mult real_one eps))).
  - apply (RealSetoid.real_eq_plus_compat y eps y (real_mult real_one eps)).
    + apply real_eq_refl.
    + apply (real_eq_trans eps (real_mult eps real_one)
               (real_mult real_one eps)).
      * apply real_eq_sym. apply real_mult_one.
      * apply real_mult_comm.
  - exact (H eps Heps).
Qed.

(* D.1 min a b <=_B a: the positive counterpart of the exact-Or-form          *)
(* underivability verdict — the Or form is underivable while the Bishop form  *)
(* is provable, side by side on this bound.  Certificate: one step of the     *)
(* D := 1 completer plus direct composition with real_min_le_l_eps; no new    *)
(* premises.                                                                  *)
Lemma real_min_le_l_B : forall a b : Real, real_le_b (real_min a b) a.

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_min_le_l_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.2 min a b <=_B b: the twin of D.1 (same chain, real_min_le_r_eps). *)
Lemma real_min_le_r_B : forall a b : Real, real_le_b (real_min a b) b.

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_min_le_r_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.3 Triangle inequality in Bishop form: |a+b| <=_B |a| + |b|.  Certificate: *)
(* D := 1 completer plus real_abs_triangle_le_eps; no new premises.           *)
Lemma real_abs_triangle_le_B : forall a b : Real,
  real_le_b (real_abs (real_plus a b))
            (real_plus (real_abs a) (real_abs b)).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_triangle_le_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.4 Squares are nonnegative in Bishop form: 0 <=_B t*t.  Certificate:      *)
(* D := 1 completer plus real_square_nonneg_eps; no new premises.             *)
Lemma real_square_nonneg_B : forall t : Real,
  real_le_b real_zero (real_mult t t).

Proof.
  intro t.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_square_nonneg_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* D.5 Step-KL contraction in Bishop form: sum kl(p||step) <=_B eta *         *)
(* sum kl(p||r) (the eta factor sits inside the composite right-hand side;    *)
(* plain-eps remainder shape).  Certificate: D := 1 completer plus direct     *)
(* composition with real_step_kl_eta_bound_eps; the premises eta > 0 and      *)
(* eta <= 1 are carried over from the source; no new premises.                *)
Theorem real_step_kl_eta_bound_B :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (real_list_sum nat p (List.seq 0 n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (List.seq 0 n)) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b
    (real_list_sum nat
       (fun i : nat => real_kl_term (p i)
                       (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i))
       (List.seq 0 n))
    (real_mult eta
       (real_list_sum nat
          (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
          (List.seq 0 n))).

Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_step_kl_eta_bound_eps n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* Part E: eighteen further Bishop-form completions.  Two certificate         *)
(* shapes occur: (1) seventeen plain-eps remainder families, each completed   *)
(* by one step of the D := 1 completer plus direct composition with its       *)
(* source lemma (as in D.1-D.4); (2) one literal D*eps remainder              *)
(* (gibbs_core, with D := p and the existing premise Hp as certificate),      *)
(* completed by a direct instance of [real_le_closure_b] (the rlhf pattern).  *)
(* ============================================================ *)

(* E.1 max form: a <=_B max(a,b); plain-eps direct composition. *)
Lemma real_r_max_le_l_B : forall a b : Real, real_le_b a (real_max a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_r_max_le_l_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.2 max form: b <=_B max(a,b); twin of E.1, same chain. *)
Lemma real_r_max_le_r_B : forall a b : Real, real_le_b b (real_max a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_r_max_le_r_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.3 Absolute value is nonnegative in Bishop form: 0 <=_B |a|; plain-eps direct composition. *)
Lemma real_abs_nonneg_le_B : forall a : Real, real_le_b real_zero (real_abs a).

Proof.
  intro a.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_nonneg_le_eps a (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.4 Metric positivity in Bishop form: 0 <=_B metric(a,b) (source is an Or-encoded eps-family in the RealSetoid module). *)
Lemma real_metric_pos_B : forall a b : Real,
  real_le_b real_zero (real_metric a b).

Proof.
  intros a b.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealSetoid.real_metric_pos_eps a b (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.5 Metric triangle inequality in Bishop form: metric(a,c) <=_B metric(a,b) + metric(b,c) — the Bishop counterpart the Or encoding cannot express. *)
Lemma real_metric_triangle_B : forall a b c : Real,
  real_le_b (real_metric a c)
            (real_plus (real_metric a b) (real_metric b c)).

Proof.
  intros a b c.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealSetoid.real_metric_triangle_eps a b c (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.6 Positive part is nonnegative in Bishop form: 0 <=_B pos_part(a) with pos_part := max(a,0); completer step plus source composition (E.2 at b := zero). *)
Lemma real_pos_part_nonneg_B : forall a : Real,
  real_le_b real_zero (real_pos_part a).

Proof.
  intro a.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_pos_part_nonneg_eps a (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.7 Exponential lower bound in Bishop form: 1 + t <=_B e^t; plain-eps direct composition. *)
Lemma real_exp_ge_linear_B : forall t : Real,
  real_le_b (real_plus real_one t) (cauchy_real_exp t).

Proof.
  intro t.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealInterfaceEnhancedMod.real_exp_ge_linear_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.8 Log upper bound in Bishop form: log(x) <=_B x + (-1); premise x > 0 carried over verbatim. *)
Lemma real_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).

Proof.
  intros x Hx.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (RealInterfaceEnhancedMod.real_log_le_linear_eps x (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hx He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.9 log(1+t) upper bound in Bishop form: log(1+t) <=_B t; premise 0 < 1+t carried over. *)
Lemma real_log_one_plus_le_B : forall (t : Real)
  (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (real_log (real_plus real_one t) Hs) t.

Proof.
  intros t Hs.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_log_one_plus_le_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hs He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.10 log(1+t) lower bound in Bishop form: t - t*t <=_B log(1+t); premises 0 < t and 0 < 1+t carried over. *)
Lemma real_log_one_plus_ge_B : forall (t : Real)
  (Ht : real_lt real_zero t) (Hs : real_lt real_zero (real_plus real_one t)),
  real_le_b (real_plus t (real_opp (real_mult t t)))
            (real_log (real_plus real_one t) Hs).

Proof.
  intros t Ht Hs.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_log_one_plus_ge_eps t (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Ht Hs He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.11 Quadratic scaling in Bishop form: t*t/s <=_B 2*t*t; premises 0 < s and 1/2 < s carried over; the certificate remains the existing D := 1 positivity, independent of the premise-side positivity. *)
Lemma real_quad_div_le_two_B : forall (t s : Real)
  (Hs : real_lt real_zero s)
  (Hs12 : real_lt (real_inv_pos (real_plus real_one real_one) real_two_pos_local) s),
  real_le_b (real_mult (real_mult t t) (real_inv_pos s Hs))
            (real_mult (real_mult t t) (real_plus real_one real_one)).

Proof.
  intros t s Hs Hs12.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_quad_div_le_two_eps t s (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) Hs Hs12 He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.12 Gibbs core in Bishop form (second literal D*eps remainder):           *)
(* p - q <=_B p * (-log(q/p)).  Certificate: D := p (independent of eps) with  *)
(* the existing premise Hp as positivity — a direct instance of                *)
(* [real_le_closure_b] (the rlhf supply pattern), not the D := 1 route.       *)
Theorem real_gibbs_core_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_plus p (real_opp q))
            (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                              (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))).
Proof.
  intros p q Hp Hq.
  apply (real_le_closure_b _ _ p Hp). intros eps Heps.
  exact (real_gibbs_core_eps p q Hp Hq eps Heps).
Qed.

(* E.13 Gibbs inequality in Bishop form: 0 <=_B sum_s kl(p s||q s); normalization premises carried over. *)
Theorem real_gibbs_inequality_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).

Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_gibbs_inequality_eps X l p q Hp Hq Hnormp Hnormq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.14 Product bound in Bishop form: |a|*|b| <=_B M*B; premises |a| <= M and |b| <= B carried over; plain-eps direct composition. *)
Lemma real_abs_prod_le_B : forall (a b M B : Real),
  real_le (real_abs a) M -> real_le (real_abs b) B ->
  real_le_b (real_mult (real_abs a) (real_abs b)) (real_mult M B).

Proof.
  intros a b M B HMa HMB.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_abs_prod_le_eps a b M B (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos HMa HMB) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.15 Exponential difference bound in Bishop form: |e^x - 1| <=_B |x| * e^{|x|}; plain-eps direct composition. *)
Lemma real_exp_abs_minus_one_B : forall x : Real,
  real_le_b (real_abs (real_plus (cauchy_real_exp x) (real_opp real_one)))
            (real_mult (real_abs x) (cauchy_real_exp (real_abs x))).

Proof.
  intro x.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_exp_abs_minus_one_eps x (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.16 Two-point convexity in Bishop form: e^{(1-eta)x + eta*y} <=_B (1-eta)*e^x + eta*e^y; premises eta > 0 and eta <= 1 carried over. *)
Lemma real_exp_two_point_cvx_B : forall (x y eta : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
            (real_plus (real_mult (real_plus real_one (real_opp eta))
                                   (cauchy_real_exp x))
                       (real_mult eta (cauchy_real_exp y))).

Proof.
  intros x y eta Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_exp_two_point_cvx_eps x y eta Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.17 Pointwise AM-GM in Bishop form: a^(1-eta) * b^eta <=_B (1-eta)*a + eta*b, with a^alpha := e^(alpha*log a); positivity and eta premises carried over. *)
Lemma real_amgm_pointwise_B : forall (a b eta : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                       (real_pow_pos b eta Hb))
            (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                       (real_mult eta b)).

Proof.
  intros a b eta Ha Hb Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_amgm_pointwise_eps a b eta Ha Hb Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* E.18 Interpolation inequality in Bishop form: sum_i pi_t(i)^(1-eta) * pi*(i)^eta <=_B 1 (summed version; two pointwise-positivity and two normalization premises plus the eta pair, all carried over). *)
Theorem real_interp_Z_le_one_B :
  forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (real_list_sum nat pit (List.seq 0 n)) real_one)
    (Hnormq : real_eq (real_list_sum nat pist (List.seq 0 n)) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_list_sum nat
               (fun i : nat => real_mult
                  (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                  (real_pow_pos (pist i) eta (Hpist i)))
               (List.seq 0 n))
            real_one.

Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le.
  unfold real_le_b. intros eps' Heps'.
  assert (Hdp : real_lt real_zero real_one) by exact real_lt_zero_one.
  assert (Htwo : real_lt real_zero (real_plus real_one real_one))
    by exact (real_plus_positive real_one real_one Hdp Hdp).
  assert (Hinv2pos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) Htwo))
    by exact (real_inv_pos_pos (real_plus real_one real_one) Htwo).
  assert (Htwo_lt : real_lt real_one (real_plus real_one real_one)).
  { apply (RealSetoid.real_lt_id_l real_one (real_plus real_one real_zero) (real_plus real_one real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate real_one real_zero real_one). exact Hdp. }
  assert (Hmono : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) (real_inv_pos real_one Hdp))
    by exact (real_inv_pos_lt_contra real_one (real_plus real_one real_one) Hdp Htwo Htwo_lt).
  assert (Hm0 : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_mult (real_inv_pos real_one Hdp) real_one))
    by exact (real_mult_lt_compat (real_inv_pos (real_plus real_one real_one) Htwo)
                                  (real_inv_pos real_one Hdp) real_one Hmono Hdp).
  assert (Heq1 : real_eq (real_mult (real_inv_pos real_one Hdp) real_one) real_one).
  { apply (real_eq_trans _ (real_mult real_one (real_inv_pos real_one Hdp)) _).
    - apply real_mult_comm.
    - apply real_inv_pos_correct. }
  assert (Hltinv : real_lt (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                           real_one)
    by exact (RealSetoid.real_lt_id_r _ (real_mult (real_inv_pos real_one Hdp) real_one)
                                       real_one Heq1 Hm0).
  assert (Hc2 : real_eq (real_mult (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
                        (real_inv_pos (real_plus real_one real_one) Htwo))
    by apply real_mult_one.
  assert (Hinvlt1 : real_lt (real_inv_pos (real_plus real_one real_one) Htwo) real_one)
    by exact (RealSetoid.real_lt_id_l _ _ _ (real_eq_sym _ _ Hc2) Hltinv).
  assert (He0mid : real_lt real_zero (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
    by exact (real_mult_positive eps' (real_inv_pos (real_plus real_one real_one) Htwo) Heps' Hinv2pos).
  assert (He0pos : real_lt real_zero (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))))
    by exact (real_mult_positive real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) Hdp He0mid).
  assert (Hkey : real_lt (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) eps').
  { assert (Hm : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))
                          (real_mult eps' real_one))
       by exact (real_mult_lt_compat_l (real_inv_pos (real_plus real_one real_one) Htwo) real_one eps' Hinvlt1 Heps').
     assert (Hm2 : real_lt (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) eps')
       by exact (RealSetoid.real_lt_id_r _ (real_mult eps' real_one) eps' (real_mult_one eps') Hm).
     assert (Hc : real_eq (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)))
                          (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))).
     { apply (real_eq_trans _ (real_mult (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo)) real_one) _).
        - apply real_mult_comm.
        - apply real_mult_one. }
     exact (RealSetoid.real_lt_id_l _ _ _ Hc Hm2). }
  destruct (real_interp_Z_le_one_eps n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le (real_mult real_one (real_mult eps' (real_inv_pos (real_plus real_one real_one) Htwo))) He0pos) as [Hlt | Heq].
  - apply (real_lt_trans _ _ _ Hlt).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
  - apply (RealSetoid.real_lt_id_l _ _ _ Heq).
    apply (real_lt_plus_translate _ _ _). exact Hkey.
Qed.

(* ============================================================ *)
(* Closing honest register (per-statement verdicts, condensed).                  *)
(*                                                                               *)
(* (1) [real_le_b] is a Set-level forall; no Prop leakage; it relates to the     *)
(*     Or-encoded [real_le] only through the one-way bridge.                     *)
(* (2) [real_le_to_le_b] is provable and strictly one-way.  The converse is      *)
(*     constructively underivable: assuming it, take (x, y, D) := (min a b, a, 1)*)
(*     with the existing positivity certificate of 1 and the pointwise eps bound *)
(*     [real_min_le_l_eps]; the completion lemma would then yield the exact      *)
(*     Or-witness [min a b <= a], whose two branches require deciding            *)
(*     "b < a" versus "a <= b" — undecidable for constructive reals.  Hence      *)
(*     only the Bishop form is claimed for this library.                         *)
(* (3) [real_le_closure_b]: provable.  Construction e0 := eps' * inv(2D) (the    *)
(*     D > 0 certificate feeds inv); D*e0 == eps'*(inv(2D)*D) < eps'*1 == eps'   *)
(*     since inv(2D)*D < 1 (D < 2D gives inv(2D) < inv(D) by anti-monotonicity   *)
(*     of inv, so inv(2D)*D < inv(D)*D == 1).  lt branch by translation and      *)
(*     transitivity; eq branch by rewriting.  No density used.                   *)
(* (4) [real_rlhf_optimal_B]: full upgrade.  The positivity certificate D_pos    *)
(*     of the residual weight D is an existing interface variable (no new        *)
(*     premises), and the residual eps-form is literally D*eps, so the Bishop    *)
(*     conclusion is a one-step instance of the completion lemma.                *)
(* (5) [real_ppo_conservative_B]: conditional upgrade.  Positivity of the        *)
(*     residual weight E := sum pi_old*adv is not derivable from the interface   *)
(*     (advantages are unbounded; E = 0 and E > 0 are constructively             *)
(*     indistinguishable), so the Bishop statement carries an explicit E > 0     *)
(*     premise (its only addition) plus the honest scalar-extraction interface   *)
(*     [real_sum_over_S_linear].  Without a certificate the eps-form statement   *)
(*     remains the strongest claim, and the exact Or-form is out of reach by     *)
(*     the same argument as in (2).                                              *)
(* (6) [real_le_closure_b_one]: the uniform D := 1 completer for plain-eps       *)
(*     families; the only rewriting face is 1*eps == eps; no new premises.       *)
(*     Every statement whose conclusion is literally real_le x (y + eps) is a    *)
(*     one-step corollary.                                                       *)
(* (7) The four D := 1 instances (min-left, min-right, absolute-value triangle,  *)
(*     square nonnegativity) upgrade fully.  min-left contrasts with (2): the    *)
(*     exact Or-form is underivable while the Bishop form is provable for the    *)
(*     same bound — the two encodings differ in derivability.                    *)
(* (8) [real_step_kl_eta_bound_B] upgrades fully (plain-eps shape; the eta       *)
(*     factor sits inside the composite right-hand side, not as a literal D*eps).*)
(* (9) Deliberate exclusions (shape mismatch, condensed): statements whose       *)
(*     remainder is not of the form y + D*eps — self-referential bounds,         *)
(*     monotone-transpose shapes, Q-level pointwise families, and               *)
(*     different-carrier (req-face) statements — are not upgraded here; two      *)
(*     composite-shape statements would need long certificate chains and are     *)
(*     left as explicit-assumption statements.                                   *)
(* (10) All eighteen Part E upgrades are realized: seventeen plain-eps via the   *)
(*     D := 1 completer plus source-lemma direct composition, and gibbs_core     *)
(*     via the direct D := p instance; premises are carried over verbatim from   *)
(*     the source statements; no new premises anywhere in Part E.                *)
(* ============================================================ *)

Print Assumptions real_le_to_le_b.
Print Assumptions real_le_closure_b.
Print Assumptions real_rlhf_optimal_B.
Print Assumptions real_ppo_conservative_B.
Print Assumptions real_le_closure_b_one.
Print Assumptions real_min_le_l_B.
Print Assumptions real_min_le_r_B.
Print Assumptions real_abs_triangle_le_B.
Print Assumptions real_square_nonneg_B.
Print Assumptions real_step_kl_eta_bound_B.
Print Assumptions real_r_max_le_l_B.
Print Assumptions real_r_max_le_r_B.
Print Assumptions real_abs_nonneg_le_B.
Print Assumptions real_metric_pos_B.
Print Assumptions real_metric_triangle_B.
Print Assumptions real_pos_part_nonneg_B.
Print Assumptions real_exp_ge_linear_B.
Print Assumptions real_log_le_linear_B.
Print Assumptions real_log_one_plus_le_B.
Print Assumptions real_log_one_plus_ge_B.
Print Assumptions real_quad_div_le_two_B.
Print Assumptions real_gibbs_core_B.
Print Assumptions real_gibbs_inequality_B.
Print Assumptions real_abs_prod_le_B.
Print Assumptions real_exp_abs_minus_one_B.
Print Assumptions real_exp_two_point_cvx_B.
Print Assumptions real_amgm_pointwise_B.
Print Assumptions real_interp_Z_le_one_B.

(* Closedness checks for representative statements close the file. *)
Print Assumptions real_le_closure_b_one.
Print Assumptions real_min_le_l_B.
Print Assumptions real_rlhf_optimal_B.
