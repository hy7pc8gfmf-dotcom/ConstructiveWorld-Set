(* ConstructiveWorld-Set -- temperature-energy monotonicity of the Gibbs ensemble in Bishop form. *)

(** * EnergyTempMonoB: expected energy increases monotonically in temperature.

    Mission.  For a finite sample with score [u], the expected energy
      [retm_Eexp] is monotone in the temperature in the Bishop form:
      [etm_energy_temp_mono_b] derives [real_le_b (E t1) (E t2)] from
      [t1 < t2], summing the Gibbs bounds [real_gibbs_inequality_B] over
      the KL pair identity [retm_energy_temp_kl_pair_ident], then
      contracting by [etm_beta_diff_pos] and [etm_le_b_scale_inv_zero].

    Dependencies.  Stdlib [QArith.Qring].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpRealLeB], [UpRealLeB2], [UpRealLeB3],
      [RealEnergyTempMono] of this development.

    References.  This development, EnergyTempMonoB.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" EnergyTempMonoB.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpRealLeB3.
Require Import RealEnergyTempMono.

(* ============================================================ *)
(* Part 0. Algebraic shortcut and the left zero-product form       *)
(* ============================================================ *)

(* Algebraic shortcut: an equality of reals whose two sides differ only in
   the bracketing of plus, mult and opp closes in one step.  The tactic
   reduces the goal to the underlying rational arithmetic: the pointwise
   difference goal is carried by [QeqT], so the tactic first bridges it to
   the propositional equality [Qeq] with [qeq_imp_qeqT] (the equality
   [ring] is registered for), projects each operation with the pointwise
   lemmas through the [qeqT_imp_qeq] conversion, and lets [ring] close the
   remaining rational identity; equality bridges such as
   [real_inv_pos_correct] do not reduce by projection and must travel
   through [real_eq_trans] chains. *)
Ltac etm_alg :=
  apply real_eq_of_zero_diff; intro n; apply qeq_imp_qeqT;
  repeat first [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ _))
               | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _)) ];
  ring.

(* [0 * a == 0]: the library lemma [real_mult_zero] has the shape
   [x * 0 == 0]; commutativity bridges the left-factor form. *)
Lemma etm_mult_zero_l : forall a : Real, real_eq (real_mult real_zero a) real_zero.
Proof.
  intro a. exact (real_eq_trans (real_mult real_zero a) (real_mult a real_zero) real_zero (real_mult_comm real_zero a) (real_mult_zero a)).
Qed.

(* ============================================================ *)
(* Part 1. Beta-difference positivity and negative-coefficient     *)
(* contravariance closers                                          *)
(* ============================================================ *)

(* [t1 < t2] implies [0 < b1 - b2] for the inverse temperatures
   [b := 1/t].  The strict order reversal under inversion
   [real_inv_lt_contra] gives [1/t2 < 1/t1], and the difference-positivity
   bridge [real_lt_opp_plus] gives [0 < b1 + (-b2)]. *)
Lemma etm_beta_diff_pos : forall (t1 t2 : Real)
  (Ht1 : real_lt real_zero t1) (Ht2 : real_lt real_zero t2),
  real_lt t1 t2 ->
  real_lt real_zero
    (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2 Ht12.
  exact (real_lt_opp_plus (real_inv_pos t2 Ht2) (real_inv_pos t1 Ht1)
             (real_inv_lt_contra t1 t2 Ht1 Ht2 Ht12)).
Qed.

(* Division by a positive coefficient closes the contravariance step:
   [0 < c] and [0 <=_B c * D] imply [0 <=_B D].  Scaling the positive
   multiple by [inv c] through the right-factor form
   [leb3_le_b_pos_scale] gives [(0 * inv c) <=_B ((c * D) * inv c)]; both
   endpoints transport along [real_eq] -- the left one because
   [0 * inv c == 0], the right one through the five-step
   [real_eq_trans] chain [(c * D) * inv c == c * (D * inv c) ==
   c * (inv c * D) == (c * inv c) * D == 1 * D == D] (the inverse step
   cannot take the projection shortcut). *)
Lemma etm_le_b_scale_inv_zero : forall (c D : Real),
  real_lt real_zero c -> real_le_b real_zero (real_mult c D) ->
  real_le_b real_zero D.
Proof.
  intros c D Hc H.
  assert (Hiv : real_lt real_zero (real_inv_pos c Hc))
    by exact (real_inv_pos_pos c Hc).
  apply (leb3_le_b_eq_l (real_mult real_zero (real_inv_pos c Hc)) real_zero D).
  - exact (etm_mult_zero_l (real_inv_pos c Hc)).
  - apply (leb3_le_b_eq_r _ (real_mult (real_mult c D) (real_inv_pos c Hc)) D).
    + exact (leb3_le_b_pos_scale real_zero (real_mult c D)
               (real_inv_pos c Hc) H Hiv).
    + apply (real_eq_trans (real_mult (real_mult c D) (real_inv_pos c Hc))
                           (real_mult c (real_mult D (real_inv_pos c Hc))) _).
      * exact (real_eq_sym _ _ (real_mult_assoc c D (real_inv_pos c Hc))).
      * apply (real_eq_trans (real_mult c (real_mult D (real_inv_pos c Hc)))
                             (real_mult c (real_mult (real_inv_pos c Hc) D)) _).
        -- exact (RealSetoid.real_eq_mult_compat c (real_mult D (real_inv_pos c Hc))
                    c (real_mult (real_inv_pos c Hc) D)
                    (real_eq_refl c) (real_mult_comm D (real_inv_pos c Hc))).
        -- apply (real_eq_trans (real_mult c (real_mult (real_inv_pos c Hc) D))
                                (real_mult (real_mult c (real_inv_pos c Hc)) D) _).
           ++ exact (real_mult_assoc c (real_inv_pos c Hc) D).
           ++ apply (real_eq_trans (real_mult (real_mult c (real_inv_pos c Hc)) D)
                                   (real_mult real_one D) _).
              ** exact (RealSetoid.real_eq_mult_compat
                          (real_mult c (real_inv_pos c Hc)) D real_one D
                          (real_inv_pos_correct c Hc) (real_eq_refl D)).
              ** apply (real_eq_trans (real_mult real_one D)
                                      (real_mult D real_one) _).
                 --- exact (real_mult_comm real_one D).
                 --- exact (real_mult_one D).
Qed.

(* ============================================================ *)
(* Part 2. The KL pair sum and the scaled identity are             *)
(* nonnegative in the Bishop order, unconditionally                *)
(* ============================================================ *)

(* [0 <=_B KL(p_{t2}||p_{t1}) + KL(p_{t1}||p_{t2})] holds
   unconditionally.  The two conjunct premises of the Bishop-form Gibbs
   bound [real_gibbs_inequality_B] are supplied by [retm_pB_norm]
   (normalization) and [retm_pB_pos] (pointwise positivity);
   [real_le_b_plus_compat] adds the two bounds, and the left endpoint
   transports along [0 + 0 == 0]. *)
Lemma etm_kl_pair_nonneg_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1) (retm_KL X u s0 l t1 Ht1 t2 Ht2)).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  assert (Hkl21 : real_le_b real_zero (retm_KL X u s0 l t2 Ht2 t1 Ht1)).
  { exact (real_gibbs_inequality_B X (s0 :: l)
             (retm_pB X u s0 l t2 Ht2) (retm_pB X u s0 l t1 Ht1)
             (retm_pB_pos X u s0 l t2 Ht2) (retm_pB_pos X u s0 l t1 Ht1)
             (retm_pB_norm X u s0 l t2 Ht2) (retm_pB_norm X u s0 l t1 Ht1)). }
  assert (Hkl12 : real_le_b real_zero (retm_KL X u s0 l t1 Ht1 t2 Ht2)).
  { exact (real_gibbs_inequality_B X (s0 :: l)
             (retm_pB X u s0 l t1 Ht1) (retm_pB X u s0 l t2 Ht2)
             (retm_pB_pos X u s0 l t1 Ht1) (retm_pB_pos X u s0 l t2 Ht2)
             (retm_pB_norm X u s0 l t1 Ht1) (retm_pB_norm X u s0 l t2 Ht2)). }
  apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero
           (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                      (retm_KL X u s0 l t1 Ht1 t2 Ht2))).
  - exact (real_plus_zero real_zero).
  - exact (real_le_b_plus_compat real_zero (retm_KL X u s0 l t2 Ht2 t1 Ht1)
             real_zero (retm_KL X u s0 l t1 Ht1 t2 Ht2) Hkl21 Hkl12).
Qed.

(* [0 <=_B (b1 - b2) * (E2 - E1)] holds unconditionally, composing the KL
   pair nonnegativity with the identity
   [retm_energy_temp_kl_pair_ident]; [leb3_le_b_eq_r] transports the
   bound to the scaled right-hand side of that identity. *)
Lemma etm_energy_scaled_nonneg_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_mult (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
               (real_plus (retm_Eexp X u s0 l t2 Ht2)
                          (real_opp (retm_Eexp X u s0 l t1 Ht1)))).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2.
  apply (leb3_le_b_eq_r real_zero
           (real_plus (retm_KL X u s0 l t2 Ht2 t1 Ht1)
                      (retm_KL X u s0 l t1 Ht1 t2 Ht2))).
  - exact (etm_kl_pair_nonneg_b X u s0 l t1 Ht1 t2 Ht2).
  - exact (retm_energy_temp_kl_pair_ident X u s0 l t1 Ht1 t2 Ht2).
Qed.

(* ============================================================ *)
(* Part 3. Main theorem: temperature-energy monotonicity in        *)
(* Bishop form                                                     *)
(* ============================================================ *)

(* [t1 < t2] implies [E(t1) <=_B E(t2)].  The final bridge from
   [0 <=_B E2 - E1] to [E1 <=_B E2] unfolds along [eps]: given
   [eps > 0], positivity of [(E2 - E1) + eps] transports by right
   addition of [E1] (the right-additive form of
   [real_lt_plus_compat_lt_le]) to [0 + E1 < (E2 - E1) + eps + E1];
   both endpoints then change form, the left one because
   [0 + E1 == E1] (commutativity plus zero), the right one because
   [(E2 - E1) + eps + E1 == E2 + eps] closes in one [etm_alg] step;
   the left endpoint finally transports along [E1 + 0 == E1]. *)
Theorem etm_energy_temp_mono_b :
  forall (X : Type) (u : X -> Real) (s0 : X) (l : list X)
    (t1 : Real) (Ht1 : real_lt real_zero t1) (t2 : Real) (Ht2 : real_lt real_zero t2),
  real_lt t1 t2 ->
  real_le_b (retm_Eexp X u s0 l t1 Ht1) (retm_Eexp X u s0 l t2 Ht2).
Proof.
  intros X u s0 l t1 Ht1 t2 Ht2 Ht12.
  pose proof (etm_beta_diff_pos t1 t2 Ht1 Ht2 Ht12) as Hdb.
  pose proof (etm_energy_scaled_nonneg_b X u s0 l t1 Ht1 t2 Ht2) as Hscaled.
  pose proof (etm_le_b_scale_inv_zero
                (real_plus (real_inv_pos t1 Ht1) (real_opp (real_inv_pos t2 Ht2)))
                (real_plus (retm_Eexp X u s0 l t2 Ht2)
                           (real_opp (retm_Eexp X u s0 l t1 Ht1)))
                Hdb Hscaled) as Hediff.
  unfold real_le_b. intros eps Heps.
  pose proof (Hediff eps Heps) as H0.
  apply (RealSetoid.real_lt_id_l (retm_Eexp X u s0 l t1 Ht1)
           (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
           (real_plus (retm_Eexp X u s0 l t2 Ht2) eps)).
  - (* [E1 == 0 + E1]: transitivity through the zero and commutativity
       branches; [real_eq_sym] takes both [Real] arguments explicitly. *)
    exact (real_eq_trans (retm_Eexp X u s0 l t1 Ht1)
             (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
             (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
             (real_eq_sym (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
                          (retm_Eexp X u s0 l t1 Ht1)
                          (real_plus_zero (retm_Eexp X u s0 l t1 Ht1)))
             (real_eq_sym (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
                          (real_plus (retm_Eexp X u s0 l t1 Ht1) real_zero)
                          (real_plus_comm real_zero (retm_Eexp X u s0 l t1 Ht1)))).
  - apply (RealSetoid.real_lt_id_r
             (real_plus real_zero (retm_Eexp X u s0 l t1 Ht1))
             (real_plus (real_plus (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                               (real_opp (retm_Eexp X u s0 l t1 Ht1)))
                                    eps)
                        (retm_Eexp X u s0 l t1 Ht1))
             (real_plus (retm_Eexp X u s0 l t2 Ht2) eps)).
    + (* [(E2 - E1) + eps + E1 == E2 + eps]: pure plus/minus algebra
         closing in one [etm_alg] step. *)
      etm_alg.
    + apply (real_lt_plus_compat_lt_le real_zero
               (real_plus (real_plus (retm_Eexp X u s0 l t2 Ht2)
                                     (real_opp (retm_Eexp X u s0 l t1 Ht1))) eps)
               (retm_Eexp X u s0 l t1 Ht1) (retm_Eexp X u s0 l t1 Ht1)).
      * exact H0.
      * apply real_le_refl.
Qed.

(* ============================================================ *)
(* Audit: every named statement is closed under the global context *)
(* ============================================================ *)
Print Assumptions etm_mult_zero_l.
Print Assumptions etm_beta_diff_pos.
Print Assumptions etm_le_b_scale_inv_zero.
Print Assumptions etm_kl_pair_nonneg_b.
Print Assumptions etm_energy_scaled_nonneg_b.
Print Assumptions etm_energy_temp_mono_b.
