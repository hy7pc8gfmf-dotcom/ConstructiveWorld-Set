(* Five-field pointer.  Mission. Formalization of the properties stated by this file's theorem/lemma declaration faces.  Dependencies. The library modules listed in the Require face below.  References. The survey/lineage accounts in the header body below (G05_LogSmall :403/:419, WALL-1 via UpReqLpoEquiv, the UpRealLeB certificates, AA15/AA22/AA23).  Constructivity. Zero admission-style statements (machine-checked).  Build. coqc -native-compiler no -q -Q . "". *)
(* UpReqG05WallClass.v -- WALL-2: survey and theoremization of the G05 blocking-slot equivalence class (the G05_LogSmall blocking face x the Bishop converse wall, unified along the rLPO equivalence class).  Main piece: g05w_wall_class_lpo, the full reduction/dissolution account between the G05 order-gap class (the :403 bridge zero-base and full-base forms, the four log-linear station slots, the WALL-1 square wall) and rLPO.  Dependencies: CW_ConstructiveWorld_219, UpReqLpoEquiv, UpRealLeB. *)
(* WALL-1 reuse takes the fallback route: UpReqSquareWallEquiv is not Required (its .vo on disk disagreed in digest with the built UpReqLpoEquiv.vo); instead the UpReqLpoEquiv local inline isomorphic facts are linked directly (the lpn_forward/lpn_backward pair, the square instance, and the free real_square_nonneg_B certificate), semantically the same face as the WALL-1 equivalence class (snw_b_lift is definitionally the same shape as g05w_sq_b_lift).  Remark: zero axioms, zero assumption load; purely constructive Set level, wall statements carried as implication premises; the extraction face is all bare real_* statements (no interface-module alias return positions, zero-artifact design). *)
(* Survey conclusion (the GEO1 cross-file unification check).  The G05 blocking faces split into two classes by statement face.  [Order-gap class] (B form proven, Or form missing; in the rLPO equivalence class): the :403 note "an exact constructive Or-form closure of real_le_b to real_le is unprovable" is given the universal shapes g05w_b_lift (full-base bridge) and g05w_b_lift0 (zero-base bridge), both proven fully two-way equivalent to rLPO (the G2 main piece). *)
(* The four log-linear station slots (UpReqU2:313 / UpReqFEPAttn:90 / UpReqTempEntropy:60 / UpFirewallReq:110; E-GIBBSD-1 judges the four stations verbatim identical): slot shape forall x Hx, le (log x Hx) (req_minus x one), whose Real realization is fixed here as g05w_loglin_slot; the B-side certificate is free on disk (real_log_le_linear_B, UpRealLeB) and the Or side is exactly the :403 gap -- the station slot and its B-form lifter verify each other at zero thickness (g05w_loglin_iff), and the decider dissolves the station slot in one step (g05w_rlpo_to_loglin_slot, the dissolution channel of the :419 fallback station).  The WALL-1 square wall (g05w_sq_b_lift, the same shape as snw_b_lift) is instantiated into the same class (g05w_b_lift_to_sq_b_lift), both limbs linked via lpn_forward/lpn_backward (definitional same-shape reuse of the WALL-1 equivalence class). *)
(* [Composite reconstruction class] (the seven blocked S slots; outside the order-gap class, the AA23 obstacle account): their conclusion faces are all req/real_eq equations or reqRDF derivative records, with no real_le_b/real_le order duality to speak of in the statement face, so the B-lifter reduction chain does not apply -- the survey prediction that the seven slots share the B-Or order-gap class fails; the unifiable face lies on the :403 order-gap axis.  Per-slot obstacle account (source statement faces transcribed; supply chains per the G05:60-70 verdict table): S1. energy_in_log_boltzmann_bridge @UpSigMigrate:74 (section Hyp): forall s, req (base_loss s) (opp (mult D (plus (log (sigm_boltzmann_dist s) pos_s) (log Z Z_pos)))); supply = partition_condition (N argument) + B1 + B2 + sum algebra, composite reconstruction in another module.  S2. free_energy_boltzmann_bridge @UpSigMigrate:79 (Hyp): req (sigm_free_energy boltz pos) (mult (opp D) (log Z Z_pos)); supply as S1. *)
(* S3. rdf_log_diff @UpReqRDF:1713 (Var): forall g Hg, reqRDF (fun z => log (g z) (Hg z)); the interface carries no log-derivative number field, needing a log-derivative req-ization plus a composite-chain differential engine.  S4. real_kl_decomp_full @UpRealLeB:227 (RealRLHFLeB section Var): forall p Hp Hnormp, real_eq (real_free_energy ... p ...) (real_plus (real_free_energy ... boltz ...) (real_mult D (real_sum ... kl_term ...))); supply = B2 + the kl_log_inv precedent + sum algebra.  S5. req_entropy_temp_explicit @UpFirewallReq:131 (Var): forall t Ht, req (fw_h t Ht) (plus (mult (inv_pos t Ht) (fw_et t Ht)) (log (Z_temp t) posZ)).  S6. req_relative_entropy_temp_decomp @UpFirewallReq:137 (Var): forall t2 Ht2 t1 Ht1, req (fw_kl t1 t2 Ht1 Ht2) (plus (plus (opp (fw_h t1 Ht1)) (mult (inv_pos t2 Ht2) (fw_et t1 Ht1))) (log (Z_temp t2) posZ)).  S7. req_temp_strict_ident2 @UpFirewallReq:153 (Var): forall t1 t2 Ht1 Ht2, req (plus (req_relative_entropy (fw_bt t2) (fw_bt t1)) (fw_kl t1 t2 Ht1 Ht2)) (mult (req_minus (inv_pos t1) (inv_pos t2)) (req_minus (fw_et t2) (fw_et t1))); S5-S7 supply = B1 + B2 + sumf algebra, composite reconstruction in another module. *)
(* Two fallback-station deficiencies on record (G05:421-427, the :419 verdict a): the downstream KL term p*(log p - log q) and the real_kl_term normal-form identity need log-inverse cancellation (log(inv p) == -log p, absent from the root library); the Bishop counterpart of the req-level fsum_zero_nonneg needs an In-machinery partial-sum device.  The single N-class slot (expf_agree @UpReqFEPAttn:265) is the spec body of the abstract expf operator and is unprovable (the G05:71-72 verdict). *)
(* New mathematics: g05w_q_lt_sub_r, a Q-level right-subtraction shift helper (direct link through the Qplus_lt_l iff).  g05w_b_lift (full-base B-to-Or bridge): the universal shape of the :403 gap.  g05w_rlpo_to_b_lift (converse reachability, the key new fact): rLPO acts on the difference real t-a with a gap/zero dichotomy; the gap branch joins with the B certificate (eps := real_const c) to rule out the negative branch pointwise (the Qabs_pos/q_abs_neg_eq sign cases), while the zero branch discards the certificate and supplies real_eq directly -- the entire thickness of the B-form-present/Or-form-missing gap is exactly the decider (isomorphic to the WALL-1 square wall, and a full-base generalization: WALL-1's snw_rlpo_to_b_lift is the instance at a:=0, y:=t*t of this piece).  g05w_b_lift0_to_rlpo (forward): zero-base bridge + square instance + the WALL-1 forward limb.  g05w_loglin_iff: station slot iff station-slot lifter (both directions free by certificate composition / certificate discarding).  g05w_rlpo_to_loglin_slot: the decider dissolves the four station slots (the :419 fallback-station dissolution channel).  g05w_wall_class_lpo (main-piece closure): the order-gap class's eight-slot cycle fully closed. *)
(* Lineage: AA15 (the rLPO base) --> AA22/AA23 (the generic-slot / obstacle-account paradigm) --> WALL-1 (snw_b_lift iff rLPO) --> this piece (the G05 order-gap axis survey unification: the order-gap class is confirmed as one class from four sources across G05_LogSmall/UpRealLeB/G09/WALL-1, the GEO1 prediction holding on the order-gap axis; the composite class's seven slots recorded faithfully outside the class).  Discipline: purely constructive Set level, statement faces all Set with the custom And/Or (the S01 product/sum types), zero classical logic, zero Prop leakage; all pieces Qed-closed; zero changes to existing files.  WALL-2: new piece, prefix g05w_ (collision grep clean at start). *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs PeanoNat.
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
Require Import UpReqLpoEquiv.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.
Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1: Q-level shift helpers (top-face chain via Qlt_alt + ring) *)
(* ============================================================ *)

(* Right subtraction shift: x < y implies x - z < y - z (both directions via the Qplus_lt_l iff). *)
Lemma g05w_q_lt_sub_r : forall x y z : Q, QltT x y -> QltT (x - z) (y - z).
Proof.
  intros x y z HxyT.
  assert (Hxy : Qlt x y) by (apply QltT_to_Qlt; exact HxyT).
  apply Qlt_to_QltT.
  rewrite (Qplus_comm x (- z)).
  rewrite (Qplus_comm y (- z)).
  exact (proj2 (Qplus_lt_r x y (- z)) Hxy).
Qed.

(* ============================================================ *)
(* Part 2: the two-face statements of the order-gap class (all Set, zero Prop). *)
(*   Full-base bridge := the universal shape of the :403 note "real_le_b to real_le"; *)
(*   zero-base bridge := its restriction at a:=0 (the parent form of the square wall / WALL-1 lifter). *)
(* ============================================================ *)

(* The full-base B-form to Or-form bridge (the :403 gap itself) *)
Definition g05w_b_lift : Set :=
  forall a t : Real, real_le_b a t -> real_le a t.

(* The zero-base bridge (restriction to the nonnegative case) *)
Definition g05w_b_lift0 : Set :=
  forall t : Real, real_le_b real_zero t -> real_le real_zero t.

(* ============================================================ *)
(* Part 3: forward -- the two bridges imply rLPO (gap thickness = the decider). *)
(*   Method: the zero-base bridge instantiated at squares yields snw_b_lift, then the WALL-1 forward limb gives rLPO; *)
(*   the full-base bridge runs the same chain (instance at a:=0, t:=x*x). *)
(* ============================================================ *)

(* Same-shape face of the WALL-1 equivalence class (local inline; definitionally the same shape as snw_wall/snw_b_lift) *)
Definition g05w_sq_wall : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

Definition g05w_sq_b_lift : Set :=
  forall t : Real,
    real_le_b real_zero (real_mult t t) ->
    real_le real_zero (real_mult t t).

Theorem g05w_b_lift_to_rlpo : g05w_b_lift -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H real_zero (real_mult t t) (real_square_nonneg_B t))).
Qed.

Theorem g05w_b_lift0_to_rlpo : g05w_b_lift0 -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H (real_mult t t) (real_square_nonneg_B t))).
Qed.

(* ============================================================ *)
(* Part 4: converse -- rLPO implies the full-base bridge (the reachability theorem, the key new fact). *)
(*   Method: rLPO acts on the difference real (t + opp a).  Zero branch: pointwise vanishing supplies real_eq directly *)
(*   (top-face conversion via q_abs_congr/Qabs_opp).  Gap branch: the B certificate takes eps := *)
(*   real_const c (real_const_pos free of a case split), pointwise d > -c; joined with the gap bound *)
(*   |d| > c, the two Qabs sign cases (Qabs_pos/q_abs_neg_eq) eliminate the negative branch -- *)
(*   the positive branch yields c < d directly, and the real_lt witness is the gap constant c.  The B certificate *)
(*   is not redundant here but is the very criterion eliminating the negative branch -- the constructive divide *)
(*   between the full-base bridge and the zero decider becomes visible at this point. *)
(* ============================================================ *)

Theorem g05w_rlpo_to_b_lift : rLPO -> g05w_b_lift.
Proof.
  intros Hdec a t Hb.
  destruct (Hdec (real_plus t (real_opp a))) as [[c [Hc [N HN]]] | Hzr].
  - (* gap branch: |(t-a)_n| > c separates uniformly; the B certificate takes real_const c to eliminate the negative branch *)
    apply inl.
    assert (Hinst : real_lt a (real_plus t (real_const c))).
    { exact (Hb (real_const c) (real_const_pos c Hc)). }
    destruct Hinst as [e2 [He2 [N2 HN2]]].
    pose proof (QltT_to_Qlt 0 e2 He2) as He2Q.
    exists c. split.
    + exact Hc.
    + exists (max N N2). intros n Hn.
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (max N N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (HnN2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (max N N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      specialize (HN n HnN). apply QltT_to_Qlt in HN.
      specialize (HN2 n HnN2). apply QltT_to_Qlt in HN2.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj t (real_opp a) n)) in HN.
      rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)) in HN.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj t (real_const c) n)) in HN2.
      rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)) in HN2.
      (* HN : c < Qabs (t_n - a_n); HN2 : e2 < (t_n + c) - a_n *)
      assert (Hlow : Qlt (- c) (projT1 t n - projT1 a n)).
      { assert (Hs1 : Qlt (0 - c) (e2 - c))
          by (apply QltT_to_Qlt; apply g05w_q_lt_sub_r; exact He2).
        assert (Hs2 : Qlt (e2 - c)
                        ((projT1 t n + c) - projT1 a n - c))
          by (apply QltT_to_Qlt; apply g05w_q_lt_sub_r;
              apply Qlt_to_QltT; exact HN2).
        assert (Hr : ((projT1 t n + c) - projT1 a n - c)%Q
                     == (projT1 t n - projT1 a n)%Q) by ring.
        rewrite Hr in Hs2.
        assert (Hr2 : (0 - c)%Q == (- c)%Q) by ring.
        rewrite Hr2 in Hs1.
        apply Qlt_trans with (e2 - c); [exact Hs1 | exact Hs2]. }
      destruct (Qlt_le_dec 0 (projT1 t n - projT1 a n)) as [Hge | Hle0].
      * (* positive branch: Qabs opens directly; c < d is the goal *)
        rewrite (Qabs_pos _ (Qlt_le_weak _ _ Hge)) in HN.
        apply Qlt_to_QltT. exact HN.
      * (* negative branch refutation: |d| = -d > c gives d < -c via Qopp_lt_compat, contradicting -c < d *)
        exfalso.
        rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq _ Hle0)) in HN.
        assert (Hdc0 : Qlt (- (- (projT1 t n - projT1 a n))) (- c))
          by (apply Qopp_lt_compat; exact HN).
        rewrite (Qopp_involutive (projT1 t n - projT1 a n)) in Hdc0.
        apply (Qlt_irrefl (- c)).
        apply Qlt_trans with (projT1 t n - projT1 a n);
          [exact Hlow | exact Hdc0].
  - (* zero branch: t-a vanishing pointwise yields real_eq a t (top-face conversion via opp) *)
    apply inr.
    intros eps Heps.
    destruct (Hzr eps Heps) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj t (real_opp a) n)) in HN.
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj a n)) in HN.
    assert (Hring : (projT1 a n - projT1 t n)%Q
                    == (- (projT1 t n - projT1 a n))%Q) by ring.
    rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hring)).
    rewrite (Qabs_opp (projT1 t n - projT1 a n)).
    exact HN.
Qed.

(* Zero-base bridge converse: an instance position of the full-base theorem *)
Theorem g05w_rlpo_to_b_lift0 : rLPO -> g05w_b_lift0.
Proof.
  exact (fun H => g05w_rlpo_to_b_lift H real_zero).
Qed.

(* ============================================================ *)
(* Part 5: the Real realization and mutual verification of the four G05 log-linear station slots (the :403 attack face). *)
(*   Slot shape (verbatim identical across the four stations, E-GIBBSD-1): forall x Hx, le (log x Hx) *)
(*   (req_minus x one); the interface le field := real_le (Or encoding), and the Real realization is *)
(*   g05w_loglin_slot below.  The B-side certificate is free: real_log_le_linear_B (UpRealLeB). *)
(* ============================================================ *)

Definition g05w_loglin_slot : Set :=
  forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one)).

(* Station-slot B-form lifter: the B certificate is on disk and the Or form is open -- the station-slot instance of the :403 gap *)
Definition g05w_loglin_b_lift : Set :=
  forall (x : Real) (Hx : real_lt real_zero x),
    real_le_b (real_log x Hx) (real_plus x (real_opp real_one)) ->
    real_le (real_log x Hx) (real_plus x (real_opp real_one)).

(* Converse: station-slot closure implies the lifter (the B-certificate premise is redundant and discarded) *)
Theorem g05w_loglin_slot_to_b_lift : g05w_loglin_slot -> g05w_loglin_b_lift.
Proof.
  exact (fun Hs x Hx _HB => Hs x Hx).
Qed.

(* Forward: the lifter + the free universal B certificate imply station-slot closure *)
Theorem g05w_loglin_b_lift_to_slot : g05w_loglin_b_lift -> g05w_loglin_slot.
Proof.
  exact (fun Hl x Hx => Hl x Hx (real_log_le_linear_B x Hx)).
Qed.

(* Zero-thickness mutual verification account (the B/Or gap and the station slot are isomorphic) *)
Definition g05w_loglin_iff :
  And (g05w_loglin_b_lift -> g05w_loglin_slot)
      (g05w_loglin_slot -> g05w_loglin_b_lift) :=
  (g05w_loglin_b_lift_to_slot, g05w_loglin_slot_to_b_lift).

(* ============================================================ *)
(* Part 6: class-unification bridges -- full-base bridge instances covering the WALL-1 square wall and the four G05 station slots *)
(* ============================================================ *)

Theorem g05w_b_lift_to_sq_b_lift : g05w_b_lift -> g05w_sq_b_lift.
Proof.
  exact (fun H t HB => H real_zero (real_mult t t) HB).
Qed.

(* Same shape as the WALL-1 forward chain: square lifter + free certificate imply the bare wall, then lpn_forward *)
Theorem g05w_sq_b_lift_to_rlpo : g05w_sq_b_lift -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H t (real_square_nonneg_B t))).
Qed.

Theorem g05w_b_lift_to_loglin_slot : g05w_b_lift -> g05w_loglin_slot.
Proof.
  exact (fun H x Hx =>
    H (real_log x Hx) (real_plus x (real_opp real_one))
      (real_log_le_linear_B x Hx)).
Qed.

(* The decider dissolves the four station slots (the :419 fallback-station dissolution channel; composed in one step via the full-base converse limb) *)
Theorem g05w_rlpo_to_loglin_slot : rLPO -> g05w_loglin_slot.
Proof.
  exact (fun H x Hx => g05w_b_lift_to_loglin_slot (g05w_rlpo_to_b_lift H) x Hx).
Qed.

(* The decider dissolves the square-wall lifter (same-shape reuse of the WALL-1 converse limb lpn_backward) *)
Theorem g05w_rlpo_to_sq_b_lift : rLPO -> g05w_sq_b_lift.
Proof.
  exact (fun Hdec t _HB => lpn_backward Hdec t).
Qed.

(* ============================================================ *)
(* Part 7: main-piece closure -- g05w_wall_class_lpo (the order-gap class eight-slot cycle record). *)
(*   Both bridges are fully two-way with rLPO; the bridge instances cover the square wall (WALL-1) *)
(*   and the four log-linear station slots (G05 :403); station slots verify each other at zero thickness; *)
(*   the decider dissolves both slot families in one step. *)
(* ============================================================ *)

Definition g05w_wall_class_lpo :
  And (g05w_b_lift -> rLPO)
      (And (rLPO -> g05w_b_lift)
           (And (g05w_b_lift0 -> rLPO)
                (And (rLPO -> g05w_b_lift0)
                     (And (g05w_b_lift -> g05w_sq_b_lift)
                          (And (g05w_sq_b_lift -> rLPO)
                               (And (g05w_b_lift -> g05w_loglin_slot)
                                    (And (g05w_loglin_b_lift -> g05w_loglin_slot)
                                         (And (g05w_loglin_slot -> g05w_loglin_b_lift)
                                              (And (rLPO -> g05w_sq_b_lift)
                                                   (rLPO -> g05w_loglin_slot)))))))))) :=
  (g05w_b_lift_to_rlpo,
  (g05w_rlpo_to_b_lift,
  (g05w_b_lift0_to_rlpo,
  (g05w_rlpo_to_b_lift0,
  (g05w_b_lift_to_sq_b_lift,
  (g05w_sq_b_lift_to_rlpo,
  (g05w_b_lift_to_loglin_slot,
  (g05w_loglin_b_lift_to_slot,
  (g05w_loglin_slot_to_b_lift,
  (g05w_rlpo_to_sq_b_lift, g05w_rlpo_to_loglin_slot)))))))))).

(* ============================================================ *)
(* Part 8 (G3): mechanizing the :419 fallback-station verdict logic -- the three-class verdict table. *)
(*   35 proven slots: the engine-direct class (the representative real_log_le_linear_B closes in one *)
(*   step through the station-slot lifter; g05w_loglin_b_lift_to_slot in this piece is its machine form); *)
(*   the 7 S-blocked slots: the composite reconstruction class (outside the order-gap class; the per-slot *)
(*   obstacle account is in the file header, the AA23 paradigm); the 1 N-class slot: the spec-body class *)
(*   (expf_agree; the unprovability verdict is on record). *)
(*   Fallback-station output when the decider is on disk: the four station slots dissolve in full (the last piece of Part 6). *)
(* ============================================================ *)

Inductive g05w_slot_class : Set :=
| g05w_c_engine : g05w_slot_class
| g05w_c_composite : g05w_slot_class
| g05w_c_spec : g05w_slot_class.

(* The fallback output of the three-class verdict table (decider on disk implies engine-class slot closure) *)
Theorem g05w_verdict_engine_resolves :
  rLPO -> (g05w_loglin_b_lift -> g05w_loglin_slot).
Proof.
  exact (fun _Hdec => g05w_loglin_b_lift_to_slot).
Qed.

(* ============================================================ *)
(* Extraction check and assumption audit face                       *)
(* ============================================================ *)

(* Extraction check: full extraction of the main piece's bare face. Every proof body in this file is
   pure combinator composition plus Q-level verdict chains (Qlt_alt/ring/the two Qabs branches/
   real_*_proj projection bridges); statements and conclusions are all bare real_* forms (zero
   interface-module alias return positions) -- Obj.magic count verified = 0 (preemptive avoidance of
   the WALL-1 iface-alias artifact pit). *)
Extraction "_thv3twall2.ml" g05w_wall_class_lpo
  g05w_b_lift_to_rlpo g05w_rlpo_to_b_lift
  g05w_b_lift0_to_rlpo g05w_rlpo_to_b_lift0
  g05w_loglin_iff g05w_rlpo_to_loglin_slot.

Print Assumptions g05w_q_lt_sub_r.
Print Assumptions g05w_b_lift_to_rlpo.
Print Assumptions g05w_b_lift0_to_rlpo.
Print Assumptions g05w_rlpo_to_b_lift.
Print Assumptions g05w_rlpo_to_b_lift0.
Print Assumptions g05w_loglin_slot_to_b_lift.
Print Assumptions g05w_loglin_b_lift_to_slot.
Print Assumptions g05w_loglin_iff.
Print Assumptions g05w_b_lift_to_sq_b_lift.
Print Assumptions g05w_sq_b_lift_to_rlpo.
Print Assumptions g05w_b_lift_to_loglin_slot.
Print Assumptions g05w_rlpo_to_loglin_slot.
Print Assumptions g05w_rlpo_to_sq_b_lift.
Print Assumptions g05w_wall_class_lpo.
Print Assumptions g05w_verdict_engine_resolves.

(* ======== ToyR slice-two evidence section (body statement faces unchanged; evidence appended only) ======== *)
Print Assumptions g05w_q_lt_sub_r.
Print Assumptions g05w_b_lift_to_rlpo.
Print Assumptions g05w_b_lift0_to_rlpo.
Print Assumptions g05w_rlpo_to_b_lift0.
Print Assumptions g05w_loglin_slot_to_b_lift.
Print Assumptions g05w_loglin_b_lift_to_slot.
Print Assumptions g05w_b_lift_to_sq_b_lift.
Print Assumptions g05w_sq_b_lift_to_rlpo.
Print Assumptions g05w_b_lift_to_loglin_slot.
Print Assumptions g05w_rlpo_to_loglin_slot.
Print Assumptions g05w_rlpo_to_sq_b_lift.
Print Assumptions g05w_verdict_engine_resolves.
