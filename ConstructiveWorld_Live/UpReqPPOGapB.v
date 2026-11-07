(* ConstructiveWorld-Set -- the <=_B dual-face file of [ppo_gap_exact]. *)
(** * UpReqPPOGapB: the dual <=_B face of the PPO conservative family.

    Mission.  Builds the Real-layer dual second layer of the B-form
      exact-identity line: the [gapb_gap] identity ([gapb_gap_exact]),
      the floor piece [gapb_gap_exact_res_nonneg_B], the inner machines
      ([gapb_plus_mid_opp], [gapb_plus_opp_swap],
      [gapb_res_weight_nonneg]), the main piece [gapb_gap_nonneg_B]
      ([0 <=_B (IS - PPO)], zero new premises), and the connectors
      [gapb_le_b_of_gap_nonneg_b]/[gapb_conservative_B] (the conclusion
      of [G06_BForm.real_ppo_conservative_B_full] verbatim).

    Dependencies.  [UpRealLeB], [UpRealLeB2], [UpRealLeB3];
      [S01_BaseRing]..[S15_TailFEPUp]; Stdlib [QArith.Qring]; consumers read-only.

    References.  This development ([UpReqPPO] [rppo_ppo_gap_exact], the
      req-layer identity whose Real-layer replica is built here;
      [UpRealLeB]/[UpRealLeB2]/[UpRealLeB3] Part C argument positions;
      [G06_BForm] [RealPPOLeBFull]); the same-name
      ConstructiveWorld-Main baseline.

    Constructivity.  [real_le_b] is a Set-valued forall form and
      [real_lt] is a [sigT]-witness form; zero Prop leakage; pure
      term-mode explicit assembly ([real_eq], not [Id], so no rewriting
      -- the whole chain is [real_eq_trans]/compat); all [Qed]; zero
      axioms.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpReqPPOGapB.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)

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

(* ================= Section GapBPPOLeB: the section-argument face matches [RealPPOMain] / [UpRealLeB] Part C / [G06_BForm] [RealPPOLeBFull] (the four positions [ext]/[le]/[add]/[linear] plus data arguments), minus the [sum_pos] position (the [E >= 0] route does not need it) ================= *)
Section GapBPPOLeB.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

Variable real_pi_star_ : S -> Real.
Variable real_pi_old : S -> Real.
Variable real_pi_old_pos : forall s : S, real_lt real_zero (real_pi_old s).
Variable real_advantage_fn : S -> Real.
Variable real_advantage_pos : forall s : S, real_lt real_zero (real_advantage_fn s).
Variable epsilon : Real.

(* ---- In-section definitions (delta-transparent, same positions as [RealPPOMain]) ---- *)
Definition gapb_ratio (s : S) : Real :=
  real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s.
Definition gapb_clip (r : Real) : Real := real_ppo_clip_ epsilon r.
Definition gapb_min_ratio (s : S) : Real :=
  real_min (gapb_ratio s) (gapb_clip (gapb_ratio s)).
(* The clipped PPO objective (same shape as the left side of the [B_full] conclusion) *)
Definition gapb_ppo_objective : Real :=
  real_sum_over_S (fun s : S =>
    real_mult (real_pi_old s)
              (real_mult (gapb_min_ratio s) (real_advantage_fn s))).
(* The IS objective (same shape as the right side of the [B_full] conclusion) *)
Definition gapb_is_objective : Real :=
  real_sum_over_S (fun s : S =>
    real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s))).
(* The gap: IS - PPO (the Real-layer minus shape [real_plus] + [real_opp]; there is no [real_minus]) *)
Definition gapb_gap : Real :=
  real_plus gapb_is_objective (real_opp gapb_ppo_objective).
(* The pointwise term/sum on the identity's right side (the [rppo_ppo_gap_exact] expansion shape: [r - min(r, clip r)]) *)
Definition gapb_gap_pointwise (s : S) : Real :=
  real_mult (real_pi_old s)
            (real_mult (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s)))
                       (real_advantage_fn s)).
Definition gapb_gap_sum : Real := real_sum_over_S gapb_gap_pointwise.
(* The residual weight [E := Sum pi_old * adv] (same position as [real_ppo_res_weight], delta-transparent; matched directly by [res_fold]) *)
Definition gapb_res_weight : Real :=
  real_ppo_res_weight S real_sum_over_S real_pi_old real_advantage_fn.

(* ============ Scalar inner machines ============ *)

(* Inner machine 1: the middle-flip degeneration [a + (b + -a) == b] (shared by the flip bridge and the identity's pointwise step) *)
Lemma gapb_plus_mid_opp : forall a b : Real,
  real_eq (real_plus a (real_plus b (real_opp a))) b.
Proof.
  intros a b.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp a) b)) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_plus b (real_opp a))
                                          a (real_plus (real_opp a) b)).
    + apply real_eq_refl.
    + apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus a (real_opp a)) b) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero b) _).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a (real_opp a))
                 b real_zero b).
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply (real_eq_trans _ (real_plus b real_zero) _).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
Qed.

(* Inner machine 2: the swap degeneration [(y + x) + -y == x] (the identity's finishing position) *)
Lemma gapb_plus_opp_swap : forall x y : Real,
  real_eq (real_plus (real_plus y x) (real_opp y)) x.
Proof.
  intros x y.
  apply (real_eq_trans _ (real_plus y (real_plus x (real_opp y))) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - exact (gapb_plus_mid_opp y x).
Qed.

(* ============ Inner machine: nonnegativity of [E] (derivable inside the interface; no strict-positivity claim) ============ *)
Lemma gapb_res_weight_nonneg : real_le real_zero gapb_res_weight.
Proof.
  (* [Sum of constant zero == 0] (pointwise [ext] + [linear] scalar extraction + [mult_zero]) *)
  assert (Hzero : real_eq (real_sum_over_S (fun _ : S => real_zero)) real_zero).
  { apply (real_eq_trans _
             (real_sum_over_S (fun s : S =>
                real_mult real_zero (real_mult (real_pi_old s) (real_advantage_fn s)))) _).
    - apply (real_sum_over_S_ext (fun _ : S => real_zero)).
      intro s.
      apply (real_eq_trans _
               (real_mult (real_mult (real_pi_old s) (real_advantage_fn s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_eq_sym. apply real_mult_comm.
    - apply (real_eq_trans _
               (real_mult real_zero
                  (real_sum_over_S (fun s : S =>
                     real_mult (real_pi_old s) (real_advantage_fn s)))) _).
      + apply (real_sum_over_S_linear real_zero
                 (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))).
      + apply (real_eq_trans _
                 (real_mult (real_sum_over_S (fun s : S =>
                     real_mult (real_pi_old s) (real_advantage_fn s))) real_zero) _).
        * apply real_eq_sym. apply real_mult_comm.
        * apply real_mult_zero. }
  exact (RealSetoid.real_le_id_l real_zero
           (real_sum_over_S (fun _ : S => real_zero))
           gapb_res_weight
           (real_eq_sym _ _ Hzero)
           (real_sum_over_S_le (fun _ : S => real_zero)
              (fun s : S => real_mult (real_pi_old s) (real_advantage_fn s))
              (fun s : S => real_le_from_lt_aux real_zero
                 (real_mult (real_pi_old s) (real_advantage_fn s))
                 (real_mult_positive (real_pi_old s) (real_advantage_fn s)
                    (real_pi_old_pos s) (real_advantage_pos s))))).
Qed.

(* ============ Machine-chain replica: the identity (the Real layer of [rppo_ppo_gap_exact]) ============ *)
(* Pointwise split [pi*(r*A) == pi*(m*A) + pi*((r + -m)*A)]: two-level distributivity via [distrib]/[distrib_r], *)
(* with no negation-sum machine (no [Sum opp] needed -- the split shape goes through [sum_add] first, then the swap degeneration). *)
Lemma gapb_gap_exact : real_eq gapb_gap gapb_gap_sum.
Proof.
  assert (Hpt : forall s : S,
    real_eq (real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s)))
            (real_plus (real_mult (real_pi_old s)
                                  (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
                       (gapb_gap_pointwise s))).
  { intro s.
    apply (real_eq_trans _
             (real_mult (real_pi_old s)
                        (real_mult (real_plus (gapb_min_ratio s)
                                              (real_plus (gapb_ratio s)
                                                         (real_opp (gapb_min_ratio s))))
                                   (real_advantage_fn s))) _).
    - apply (RealSetoid.real_eq_mult_compat (real_pi_old s)
               (real_mult (gapb_ratio s) (real_advantage_fn s))
               (real_pi_old s)
               (real_mult (real_plus (gapb_min_ratio s)
                                     (real_plus (gapb_ratio s)
                                                (real_opp (gapb_min_ratio s))))
                          (real_advantage_fn s))).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_mult_compat (gapb_ratio s) (real_advantage_fn s)
                 (real_plus (gapb_min_ratio s)
                            (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s))))
                 (real_advantage_fn s)).
        * exact (real_eq_sym _ _
                   (gapb_plus_mid_opp (gapb_min_ratio s) (gapb_ratio s))).
        * apply real_eq_refl.
    - apply (real_eq_trans _
               (real_mult (real_pi_old s)
                          (real_plus (real_mult (gapb_min_ratio s) (real_advantage_fn s))
                                     (real_mult (real_plus (gapb_ratio s)
                                                           (real_opp (gapb_min_ratio s)))
                                                (real_advantage_fn s)))) _).
      + apply (RealSetoid.real_eq_mult_compat (real_pi_old s)
                 (real_mult (real_plus (gapb_min_ratio s)
                                       (real_plus (gapb_ratio s)
                                                  (real_opp (gapb_min_ratio s))))
                            (real_advantage_fn s))
                 (real_pi_old s)
                 (real_plus (real_mult (gapb_min_ratio s) (real_advantage_fn s))
                            (real_mult (real_plus (gapb_ratio s)
                                                  (real_opp (gapb_min_ratio s)))
                                       (real_advantage_fn s)))).
        * apply real_eq_refl.
        * apply real_eq_sym.
          exact (real_distrib_r (gapb_min_ratio s)
                  (real_plus (gapb_ratio s) (real_opp (gapb_min_ratio s)))
                  (real_advantage_fn s)).
      + apply real_distrib. }
  assert (Hsplit : real_eq gapb_is_objective
                     (real_plus gapb_ppo_objective gapb_gap_sum)).
  { apply (real_eq_trans _
             (real_sum_over_S (fun s : S =>
                real_plus (real_mult (real_pi_old s)
                                     (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
                          (gapb_gap_pointwise s))) _).
    - apply (real_sum_over_S_ext (fun s : S =>
         real_mult (real_pi_old s) (real_mult (gapb_ratio s) (real_advantage_fn s)))).
      intro s. exact (Hpt s).
    - exact (real_sum_over_S_add (fun s : S =>
         real_mult (real_pi_old s) (real_mult (gapb_min_ratio s) (real_advantage_fn s)))
         gapb_gap_pointwise). }
  unfold gapb_gap.
  apply (real_eq_trans _
           (real_plus (real_plus gapb_ppo_objective gapb_gap_sum)
                      (real_opp gapb_ppo_objective)) _).
  - apply (RealSetoid.real_eq_plus_compat gapb_is_objective
             (real_opp gapb_ppo_objective)
             (real_plus gapb_ppo_objective gapb_gap_sum)
             (real_opp gapb_ppo_objective)).
    + exact Hsplit.
    + apply real_eq_refl.
  - exact (gapb_plus_opp_swap gapb_gap_sum gapb_ppo_objective).
Qed.

(* ============ Floor piece: the per-eps nonnegativity layer of the difference of the identity's two sides ============ *)
(* [0 <=_B (gapb_gap - gapb_gap_sum)]: the difference of the two sides equals the endpoints' self-difference, which is [0]. *)
Lemma gapb_gap_exact_res_nonneg_B :
  real_le_b real_zero (real_plus gapb_gap (real_opp gapb_gap_sum)).
Proof.
  apply (leb3_le_b_eq_r real_zero real_zero
           (real_plus gapb_gap (real_opp gapb_gap_sum))).
  - apply leb3_le_b_refl.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus gapb_gap_sum (real_opp gapb_gap_sum)) _).
    + apply (RealSetoid.real_eq_plus_compat gapb_gap (real_opp gapb_gap_sum)
               gapb_gap_sum (real_opp gapb_gap_sum)).
      * exact gapb_gap_exact.
      * apply real_eq_refl.
    + apply real_plus_opp.
Qed.

(* ============ Main piece: the complete dual statement -- [0 <=_B (IS - PPO)], zero new premises ============ *)
(* Completion route: [real_le_closure_b_nonneg] (F.1, with [C := E] only needing nonnegativity) + the per-eps body = *)
(* [conservative_eps] (its thirteen arguments resolved) + [real_le_minus_nonneg_aux] (the Or-form difference *)
(* nonnegativity, at the top) + the residual-folding rewrite via [res_fold]. *)
Lemma gapb_gap_nonneg_B : real_le_b real_zero gapb_gap.
Proof.
  apply (real_le_closure_b_nonneg real_zero gapb_gap gapb_res_weight
           gapb_res_weight_nonneg).
  intros eps Heps.
  pose proof (real_ppo_conservative_eps S real_sum_over_S real_sum_over_S_ext
                real_sum_over_S_le real_sum_over_S_add real_pi_star_ real_pi_old
                real_pi_old_pos real_advantage_fn real_advantage_pos
                epsilon eps Heps) as Hce.
  apply (RealSetoid.real_le_id_r real_zero
           (real_plus (real_plus gapb_is_objective
                        (real_sum_over_S (fun s : S =>
                           real_mult (real_pi_old s)
                                     (real_mult eps (real_advantage_fn s)))))
                      (real_opp gapb_ppo_objective))
           (real_plus gapb_gap (real_mult gapb_res_weight eps))).
  - (* Rewrite: [((IS + R) + -PPO) == gapb_gap + E * eps] (three [assoc]/[comm] steps + [res_fold]) *)
    apply (real_eq_trans _
             (real_plus gapb_is_objective
                        (real_plus (real_sum_over_S (fun s : S =>
                           real_mult (real_pi_old s)
                                     (real_mult eps (real_advantage_fn s))))
                                   (real_opp gapb_ppo_objective))) _).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans _
               (real_plus gapb_is_objective
                          (real_plus (real_opp gapb_ppo_objective)
                                     (real_sum_over_S (fun s : S =>
                                        real_mult (real_pi_old s)
                                                  (real_mult eps (real_advantage_fn s)))))) _).
      * apply (RealSetoid.real_eq_plus_compat gapb_is_objective
                 (real_plus (real_sum_over_S (fun s : S =>
                    real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
                    (real_opp gapb_ppo_objective))
                 gapb_is_objective
                 (real_plus (real_opp gapb_ppo_objective)
                            (real_sum_over_S (fun s : S =>
                               real_mult (real_pi_old s)
                                         (real_mult eps (real_advantage_fn s)))))).
        -- apply real_eq_refl.
        -- apply real_plus_comm.
      * apply (real_eq_trans _
                 (real_plus (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                            (real_sum_over_S (fun s : S =>
                               real_mult (real_pi_old s)
                                         (real_mult eps (real_advantage_fn s))))) _).
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                     (real_sum_over_S (fun s : S =>
                        real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s))))
                     (real_plus gapb_is_objective (real_opp gapb_ppo_objective))
                     (real_mult gapb_res_weight eps)).
          ++ apply real_eq_refl.
          ++ exact (real_ppo_res_fold S real_sum_over_S real_sum_over_S_ext
                      real_sum_over_S_linear real_pi_old real_advantage_fn eps).
  - exact (real_le_minus_nonneg_aux gapb_ppo_objective
             (real_plus gapb_is_objective
                (real_sum_over_S (fun s : S =>
                   real_mult (real_pi_old s) (real_mult eps (real_advantage_fn s)))))
             Hce).
Qed.

(* ============ Connector 1: the flip bridge (pure Bishop algebra, fully generic and reusable) ============ *)
Lemma gapb_le_b_of_gap_nonneg_b :
  forall x y : Real,
    real_le_b real_zero (real_plus x (real_opp y)) -> real_le_b y x.
Proof.
  intros x y H.
  unfold real_le_b in H. unfold real_le_b.
  intros d Hd.
  pose proof (H d Hd) as Hlt.
  pose proof (real_lt_plus_translate y real_zero
                (real_plus (real_plus x (real_opp y)) d) Hlt) as Htr.
  assert (Htr2 : real_lt y (real_plus y (real_plus (real_plus x (real_opp y)) d))).
  { apply (RealSetoid.real_lt_id_l y (real_plus y real_zero)
             (real_plus y (real_plus (real_plus x (real_opp y)) d))).
    - apply real_eq_sym. apply real_plus_zero.
    - exact Htr. }
  assert (Heq : real_eq (real_plus y (real_plus (real_plus x (real_opp y)) d))
                        (real_plus x d)).
  { apply (real_eq_trans _
             (real_plus (real_plus y (real_plus x (real_opp y))) d) _).
    - apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus y (real_plus x (real_opp y))) d x d).
      + exact (gapb_plus_mid_opp y x).
      + apply real_eq_refl. }
  exact (real_lt_eq_lt y (real_plus y (real_plus (real_plus x (real_opp y)) d))
           (real_plus x d) Htr2 Heq).
Qed.

(* ============ Connector 2: the dual statement implies the existing B-form conservative statement (discharged as a corollary relationship) ============ *)
(* Statement face = verbatim the same shape as the conclusion of [G06_BForm.real_ppo_conservative_B_full]; *)
(* proof = the single chain Connector 1 <- Main piece (no [sum_pos] argument position, no [E > 0] certificate premise). *)
Theorem gapb_conservative_B :
  real_le_b
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_min (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                             (real_ppo_clip_ epsilon (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)))
                   (real_advantage_fn s))))
    (real_sum_over_S (fun s : S =>
      real_mult (real_pi_old s)
        (real_mult (real_importance_ratio_ S real_pi_star_ real_pi_old real_pi_old_pos s)
                   (real_advantage_fn s)))).
Proof.
  exact (gapb_le_b_of_gap_nonneg_b gapb_is_objective gapb_ppo_objective           gapb_gap_nonneg_B).
Qed.

End GapBPPOLeB.

(* ============================================================ *)
(* Closing notes (honesty boundaries) *)
(*   [Grading] inner machine 2 (scalar degeneration, structurally the Real replica of the rppo inner machine 6) *)
(*     + inner machine 1 ([E >= 0]: two feeds of [mult_positive] + the [sum_le] argument position + *)
(*     [Sum 0 == 0]) + the identity piece (pointwise two-level distributivity + [sum_ext] transport + *)
(*     [sum_add] + the swap degeneration -- a bit-for-bit Real replica of the machine chain; the split *)
(*     shape goes through [sum_add] first, so no [Sum opp] machine is built) + the floor piece (one-step *)
(*     [leb3] transport) + the main piece (the nonnegativity completer -- [E] only needs [>= 0]; the full *)
(*     upgrade adds no new premises) + connector 1 (the flip bridge, generic) + connector 2 (a verbatim *)
(*     corollary of the [B_full] conclusion face). *)
(*   [Conclusion boundary] the Or-form [real_le zero gapb_gap] is not claimed (the same-source limit *)
(*     is not crossed); the [E > 0] strict-positivity conclusion is not overturned (this file relies only *)
(*     on the interface-derivable nonnegativity [E >= 0]). *)
(*   [Counterpart] the identity piece is the Real-layer replica of [rppo_ppo_gap_exact] (whose req-layer *)
(*     proof is on record) -- the two pieces cross-certify across layers (the req side depends on [UpReqPPO.v]). *)
(*                                                              *)
(*                                                              *)
(*                                                              *)
(* ============================================================ *)

Print Assumptions gapb_res_weight_nonneg.
Print Assumptions gapb_gap_exact.
Print Assumptions gapb_gap_exact_res_nonneg_B.
Print Assumptions gapb_gap_nonneg_B.
Print Assumptions gapb_le_b_of_gap_nonneg_b.
Print Assumptions gapb_conservative_B.
