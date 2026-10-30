(* ConstructiveWorld-Set -- GEO1 residual-wall three-part theoremization: the G07 pointwise-
   comparability wall, the S14 pointwise-bound wall, the AlignIdUnclosed argument-order
   pinning, along the "B->Or lifter iff rLPO" equivalence-class paradigm.  Ablation landing
   piece: original text preserved verbatim; the closing-inventory proof body (rwl_s14_pointwise_to_tail, orig L382) was
   rewritten as a substantive toy proof, statement faces, Requires and proof-ending markers unchanged,
   Print Assumptions audit face kept at the end.

   Mission.  Main piece rwl_resid_walls_lpo, the residual-wall closure four-slot account:
   cmp_wall -> rLPO (one-way; the sign class is stronger than the decision base, converse not opened),
   cmp_wall -> rwl_snw_wall_face (WALL-1 linkage: lt sub-branch contradicts q_sq_nonneg pointwise,
   eq sub-branch converts by real_eq_sym), cmp_wall -> rwl_max_split_wall (the GEO1 #8 min/max split
   gap, <= the comparability wall at LLPO level), and the S14 pointwise->tail free direction (M := 0)
   + finite head-segment reconstruction; Part 3 fixes rwl_aiu_swap_slot (pinned, no reduction).

   Dependencies.  Stdlib Extraction, QArith (QArith/Qabs/Qring), Lqa, PeanoNat; S01_BaseRing through
   S15_TailFEPUp; UpReqLpoEquiv linked directly.  On the on-disk digest disagreement the square wall
   is supplied locally: rwl_snw_wall_face, same shape as snw_wall (UpReqSquareWallEquiv:70), CW219/S02 layer.

   References.  G07_KLWall.v:627 (Part-1 verdict 2/3 chain; strict-sum precedent in UpReqKLEnergy);
   S14_B5BatchBlock.v:6849 (deltaB-3 empirical downgrade); AlignIdUnclosed.v:157 (closed swap
   account); G06_BForm:642 (branch-selection witness); S07 real_r_max_l_iff / real_r_max_r_iff;
   S01:67 (Or data sum type); CW_ConstructiveWorld_219 (the CW219 Real layer).

   Constructivity.  Axioms: none, machine-checked by the closing Print Assumptions face.
   Statement faces are all Set-valued (real_le/real_lt/real_eq/Or(sigT)/QleT'/NatLe); walls
   ride as implication premises with zero classical logic; Prop appears only inside proof
   bodies in Q-level refutation asserts exiting through False_rect.

   Build.  rocq c -native-compiler no -q -Q <world> "" UpReqResidWallEquiv.v (Rocq 9.1.0),
   same-world dependency .vo, under the load wrapper. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
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
Import RealInterfaceEnhancedMod.
Local Open Scope Q_scope.

(* On the UpReqLpoEquiv digest disagreement (Require reported inconsistent
   assumptions): other pieces' artifacts stay untouched and their
   .vo files are not recompiled; instead UpReqLpoEquiv is linked directly + a local
   inline isomorphic face: rwl_snw_wall_face is definitionally identical in shape to
   snw_wall (UpReqSquareWallEquiv:70), same CW219/S02 Real layer. *)
Definition rwl_snw_wall_face : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

(* ============================================================ *)
(* Part 1: Q-layer helpers (zero-name self-audit: all rwl_ prefixed)                        *)
(* ============================================================ *)

(* Gap shift: b-a > e and |b-c| < d < e give c-a > e-d.
   Positive branch (a<c): direct triangle chain; negative branch (c<=a): |b-c| = b-c >= b-a > e > d > |b-c|, a contradiction.
   Discipline: Qeq rewriting enters only goal sides and QltT/Id-shaped premises
   (the UpReqLpoEquiv precedent); no rewriting inside Qle/Qlt premises
   (the library delta-unfolding trap, caught in a full first run after a false vos pass). *)
Lemma rwl_q_gap_shift : forall a b c e d : Q,
  QltT 0 d -> QltT d e -> QltT e (b - a) -> QltT (Qabs (b - c)) d ->
  QltT (e - d) (c - a).
Proof.
  intros a b c e d Hd0T HdeT HeaT HbcT.
  assert (Hd0 : Qlt 0 d) by (apply QltT_to_Qlt; exact Hd0T).
  assert (Hde : Qlt d e) by (apply QltT_to_Qlt; exact HdeT).
  assert (Hea : Qlt e (b - a)) by (apply QltT_to_Qlt; exact HeaT).
  assert (Hbc : Qlt (Qabs (b - c)) d) by (apply QltT_to_Qlt; exact HbcT).
  apply Qlt_to_QltT.
  assert (Hba0 : 0 <= b - a).
  { apply Qlt_le_weak.
    apply (Qlt_trans 0 e (b - a)).
    - apply (Qlt_trans 0 d e); [exact Hd0 | exact Hde].
    - exact Hea. }
  assert (Heqba : Qabs (b - a) == (b - a)) by (apply Qabs_pos; exact Hba0).
  destruct (Qlt_le_dec a c) as [Hac | Hca].
  - (* positive branch: |c-a| = c-a, so c-a >= (b-a) - |b-c| > e - d *)
    apply (Qlt_le_trans (e - d) (b - a + (- Qabs (b - c))) (c - a)).
    + assert (Hr1 : (e - d)%Q == (e + (- d))%Q) by ring.
      rewrite Hr1.
      apply Qplus_lt_compat.
      * exact Hea.
      * apply Qopp_lt_compat. exact Hbc.
    + apply (Qle_trans (b - a + (- Qabs (b - c)))
                       ((Qabs (b - c) + (c - a)) + (- Qabs (b - c)))
                       (c - a)).
      * apply Qplus_le_compat;
          [apply (Qle_trans (b - a) (Qabs (b - a))
                            (Qabs (b - c) + (c - a))) | apply Qle_refl].
        -- rewrite Heqba. apply Qle_refl.
        -- apply (Qle_trans (Qabs (b - a)) (Qabs (b - c) + Qabs (c - a))
                            (Qabs (b - c) + (c - a))).
           ++ pose proof (Qabs_triangle (b - c) (c - a)) as Htri2.
              assert (Hr6 : ((b - c) + (c - a))%Q == (b - a)%Q) by ring.
              rewrite <- Hr6.
              exact Htri2.
           ++ assert (Hca0 : Qlt 0 (c - a)).
              { pose proof (proj2 (Qplus_lt_l a c (- a)) Hac) as H1.
                assert (Hr7 : (0%Q) == (a + - a)%Q) by ring.
                assert (Hr8 : (c - a)%Q == (c + - a)%Q) by ring.
                rewrite Hr7. rewrite Hr8.
                exact H1. }
              apply Qplus_le_compat; [apply Qle_refl |
                rewrite (Qabs_pos (c - a) (Qlt_le_weak 0 (c - a) Hca0));
                apply Qle_refl].
      * assert (Hr2 : ((Qabs (b - c) + (c - a)) + (- Qabs (b - c)))%Q
                      == (c - a)%Q) by ring.
        rewrite Hr2. apply Qle_refl.
  - (* negative branch: c <= a -> b-a <= b-c and |b-c| = b-c, so b-c < d < e < b-a <= b-c explodes *)
    exfalso.
    assert (Hbac : b - a <= b - c).
    { pose proof (Qopp_le_compat c a Hca) as Ho.
      pose proof (Qplus_le_compat (- a) (- c) b b Ho (Qle_refl b)) as Hq2.
      assert (Hr4 : (b - a)%Q == (- a + b)%Q) by ring.
      assert (Hr5 : (b - c)%Q == (- c + b)%Q) by ring.
      rewrite Hr4. rewrite Hr5.
      exact Hq2. }
    assert (Hbc0 : 0 <= b - c).
    { apply Qlt_le_weak.
      apply (Qlt_trans 0 e (b - c)).
      - apply (Qlt_trans 0 d e); [exact Hd0 | exact Hde].
      - exact (Qlt_le_trans e (b - a) (b - c) Hea Hbac). }
    apply (Qlt_irrefl (b - c)).
    apply (Qlt_le_trans (b - c) (b - a) (b - c)).
    + apply (Qlt_trans (b - c) e (b - a)).
      * apply (Qlt_trans (b - c) d e).
        -- apply (Qle_lt_trans (b - c) (Qabs (b - c)) d).
           ++ rewrite (Qabs_pos (b - c) Hbc0). apply Qle_refl.
           ++ exact Hbc.
        -- exact Hde.
      * exact Hea.
    + exact Hbac.
Qed.

(* ============================================================ *)
(* Part 2: Real-layer transfer helper (rightward order shift along an isometry)      *)
(* ============================================================ *)

(* real_le x y + real_eq y z -> real_le x z (the real_lt branch supplies the half gap
   via rwl_q_gap_shift; the real_eq branch connects by real_eq_trans directly) *)
Lemma rwl_le_eq_transfer_r : forall x y z : Real,
  real_le x y -> real_eq y z -> real_le x z.
Proof.
  intros x y z H Hq.
  destruct H as [Hlt | Heq].
  - apply inl.
    destruct Hlt as [eps [Heps [N HN]]].
    assert (Hh : QltT 0 (eps / 2)).
    { apply Qlt_to_QltT. apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    destruct (Hq (eps / 2) Hh) as [N2 HN2].
    assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    assert (Hde2 : Qlt (eps / 2) eps).
    { destruct (Qlt_le_dec (eps / 2) eps) as [Hgood | Hbad].
      - exact Hgood.
      - exfalso.
        pose proof (Qmult_le_compat_r eps (eps / 2) 2 Hbad
                      (Qlt_le_weak 0 2 (proj2 (Qlt_alt 0 2) eq_refl))) as Hm.
        assert (Hm2 : (2 * eps <= eps)%Q).
        { assert (Hr1a : (2 * eps)%Q == (eps * 2)%Q) by ring.
          assert (Hr2a : eps%Q == ((eps / 2) * 2)%Q) by field.
          rewrite Hr1a. rewrite Hr2a at 2.
          exact Hm. }
        assert (Hm3 : (eps <= 0)%Q).
        { pose proof (Qplus_le_compat (2 * eps) eps (- eps) (- eps) Hm2
                        (Qle_refl (- eps))) as Hm4.
          assert (Hr6 : eps%Q == (2 * eps + - eps)%Q) by field.
          assert (Hr7 : 0%Q == (eps + - eps)%Q) by ring.
          rewrite Hr6. rewrite Hr7.
          exact Hm4. }
        apply (Qlt_irrefl 0).
        exact (Qlt_le_trans 0 eps 0 HepsQ Hm3). }
    exists (eps / 2). split.
    + exact Hh.
    + exists (Nat.max N N2). intros n Hn.
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (HnN2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      specialize (HN n HnN). specialize (HN2 n HnN2).
      apply Qlt_to_QltT.
      assert (Hring : (eps - eps / 2)%Q == (eps / 2)%Q) by field.
      rewrite <- Hring.
      exact (QltT_to_Qlt _ _
               (rwl_q_gap_shift (projT1 x n) (projT1 y n) (projT1 z n)
                  eps (eps / 2)
                  Hh (Qlt_to_QltT _ _ Hde2) HN HN2)).
  - apply inr. exact (real_eq_trans x y z Heq Hq).
Qed.

(* ============================================================ *)
(* Part 3: Part-1 shape fixing and reduction -- the G07 pointwise comparability wall -> rLPO *)
(* ============================================================ *)

(* Part-1 wall statement (instance core): comparability of arbitrary two reals. The "pointwise comparability premise"
   of the G07 KL strict-sum chain, instantiated with S := unit constant functions, is exactly this shape. *)
Definition rwl_g07_cmp_wall : Set :=
  forall p q : Real, Or (real_le p q) (real_le q p).

(* Reduction theorem: the comparability wall -> restricted LPO. The four Or-in-Or branches, one by one:
   the x<0 branch |x_n| = -x_n > eps; the x==0 branch supplies the zero witness directly; the 0<x branch |x_n| = x_n > eps;
   the 0==x branch reshapes through |0-x_n| = |x_n|. The converse is not opened (the sign is out of the zero-dichotomy's reach). *)
Theorem rwl_g07_cmp_to_rlpo : rwl_g07_cmp_wall -> rLPO.
Proof.
  intros Hcmp x.
  destruct (Hcmp x real_zero) as [H | H].
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      apply inl. exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn). apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz in HN.
        assert (Hr : (0 - projT1 x n)%Q == (- projT1 x n)%Q) by ring.
        rewrite Hr in HN.
        assert (Hneg : (projT1 x n < 0)%Q).
        { assert (Hrn : (projT1 x n)%Q == (- (- projT1 x n))%Q) by ring.
          rewrite Hrn.
          apply (Qopp_lt_compat 0 (- projT1 x n)).
          apply (Qlt_trans 0 eps (- projT1 x n)).
          - exact (QltT_to_Qlt 0 eps Heps).
          - exact HN. }
        assert (Hle0 : (projT1 x n <= 0)%Q) by (apply (Qlt_le_weak _ _ Hneg)).
        rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq (projT1 x n) Hle0)).
        exact HN.
    + apply inr. intros eps Heps.
      destruct (Heq eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      assert (Hr : (projT1 x n - projT1 real_zero n)%Q == (projT1 x n)%Q).
      { assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz. ring. }
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hr)) in HN.
      apply Qlt_to_QltT. exact HN.
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      apply inl. exists eps. split.
      * exact Heps.
      * exists N. intros n Hn.
        specialize (HN n Hn). apply QltT_to_Qlt in HN.
        apply Qlt_to_QltT.
        assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz in HN.
        assert (Hr : (projT1 x n - 0)%Q == (projT1 x n)%Q) by ring.
        rewrite Hr in HN.
        assert (Hxn0 : Qlt 0 (projT1 x n)).
        { apply (Qlt_trans 0 eps (projT1 x n)).
          - exact (QltT_to_Qlt 0 eps Heps).
          - exact HN. }
        rewrite (Qabs_pos (projT1 x n) (Qlt_le_weak _ _ Hxn0)).
        exact HN.
    + apply inr. intros eps Heps.
      destruct (Heq eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn).
      apply QltT_to_Qlt in HN.
      assert (Hr : (projT1 real_zero n - projT1 x n)%Q
                   == (- projT1 x n)%Q).
      { assert (Hz : projT1 real_zero n == 0) by reflexivity.
        rewrite Hz. ring. }
      rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ Hr)) in HN.
      rewrite (Qabs_opp (projT1 x n)) in HN.
      apply Qlt_to_QltT. exact HN.
Qed.

(* Part 1 <-> WALL-1 class linkage: the comparability wall -> the bare square wall.
   The left branch supplies directly; in the right branch (t*t <= 0) the lt sub-branch contradicts
   q_sq_nonneg pointwise (Prop refutation exits the Set goal by False_rect), and the eq sub-branch converts by real_eq_sym directly. *)
Theorem rwl_cmp_to_snw_wall : rwl_g07_cmp_wall -> rwl_snw_wall_face.
Proof.
  intros Hcmp t.
  destruct (Hcmp real_zero (real_mult t t)) as [H | H].
  - exact H.
  - destruct H as [Hlt | Heq].
    + destruct Hlt as [eps [Heps [N HN]]].
      assert (Habs : False).
      { specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
        apply QltT_to_Qlt in HN.
        assert (Hz : projT1 real_zero N == 0) by reflexivity.
        rewrite Hz in HN.
        rewrite (qeqT_imp_qeq _ _ (real_mult_proj t t N)) in HN.
        assert (Hr : (0 - projT1 t N * projT1 t N)%Q
                     == (- (projT1 t N * projT1 t N))%Q) by ring.
        rewrite Hr in HN.
        apply QltT_to_Qlt in Heps.
        assert (Hle0 : (- (projT1 t N * projT1 t N) <= 0)%Q).
        { apply (Qopp_le_compat 0 (projT1 t N * projT1 t N)).
          apply QleT'_to_Qle. apply q_sq_nonneg. }
        apply (Qlt_irrefl 0).
        exact (Qlt_le_trans 0 (- (projT1 t N * projT1 t N)) 0
                 (Qlt_trans 0 eps (- (projT1 t N * projT1 t N)) Heps HN)
                 Hle0). }
      exact (False_rect _ Habs).
    + apply inr. exact (real_eq_sym (real_mult t t) real_zero Heq).
Qed.

(* ============================================================ *)
(* Part 4: G3 extra -- the GEO1 #8 min/max order-split gap (Or-split shape fixing and reduction) *)
(* ============================================================ *)

(* The #8 split-gap body: x <= max(a,b) -> x <= a \/ x <= b.
   The Or-split form has 0 occurrences library-wide; the G06_BForm:642 note "no claim of
   the exact form real_le (real_max a b) c (the branch-selection face)" is its in-library witness. *)
Definition rwl_max_split_wall : Set :=
  forall x a b : Real,
    real_le x (real_max a b) -> Or (real_le x a) (real_le x b).

(* Reduction theorem: the comparability wall -> the split gap. The branch-selection face is supplied by pointwise comparability:
   in the a <= b branch max contracts to b (real_r_max_r_iff), in the b <= a branch to a
   (real_r_max_l_iff), with order shifted rightward along the contraction isometry (rwl_le_eq_transfer_r). *)
Theorem rwl_cmp_to_max_split : rwl_g07_cmp_wall -> rwl_max_split_wall.
Proof.
  intros Hcmp x a b Hx.
  destruct (Hcmp a b) as [Hab | Hba].
  - apply inr. apply (rwl_le_eq_transfer_r x (real_max a b) b Hx).
    exact (real_r_max_r_iff a b Hab).
  - apply inl. apply (rwl_le_eq_transfer_r x (real_max a b) a Hx).
    exact (real_r_max_l_iff a b Hba).
Qed.

(* ============================================================ *)
(* Part 5: Part-2 shape fixing and account -- the tail-form interface of the S14 pointwise-bound wall (the QleT'/NatLe face) *)
(* ============================================================ *)

(* The downgraded Part-2 face: the pointwise all-n bound (deltaB-3 empirically unprovable: the log_seq/approx_root
   pointwise walls). *)
Definition rwl_s14_ptw_wall (Sq : nat -> Q) (ub : Q) : Set :=
  forall n : nat, QleT' (Sq n) ub.

(* The honest Part-2 interface: the tail-form M premise + tail certificate (the statement shape of b5?_S_ub_tail_q). *)
Definition rwl_s14_tail_cert (Sq : nat -> Q) (ub : Q) : Set :=
  sigT (fun M : nat => forall n : nat, NatLe M n -> QleT' (Sq n) ub).

(* Free direction: pointwise -> tail form (M := 0, zero thickness). *)
Theorem rwl_s14_pointwise_to_tail : forall (Sq : nat -> Q) (ub : Q),
  rwl_s14_ptw_wall Sq ub -> rwl_s14_tail_cert Sq ub.
Proof.
  intros Sq ub H.
  exists 0%nat.
  intros n _.
  exact (H n).
Qed.

(* Reconstruction channel: tail form + finite head-segment certificate -> pointwise (the interface account of the
   b5dE tail certificate x S(0)==1 transparent-piece chain; the head branch goes NatLe n M, the tail branch NatLe M n). *)
Theorem rwl_s14_tail_plus_head : forall (Sq : nat -> Q) (ub : Q) (M : nat),
  (forall n : nat, NatLe M n -> QleT' (Sq n) ub) ->
  (forall n : nat, NatLe n M -> QleT' (Sq n) ub) ->
  rwl_s14_ptw_wall Sq ub.
Proof.
  intros Sq ub M Htail Hhead n.
  destruct (Nat.leb n M) eqn:E.
  - apply Hhead. unfold NatLe. rewrite E. apply id_refl.
  - apply Htail. apply NatLe_lift.
    apply Nat.lt_le_incl.
    exact (proj1 (Nat.leb_gt n M) E).
Qed.

(* ============================================================ *)
(* Part 6: Part-3 shape fixing -- the AlignIdUnclosed argument-order face (pinning account, no reduction) *)
(* ============================================================ *)

(* Piece-6 argument-order face (binary general form; the KLE instance of F = the req2_rel_ent argument order).
   Pinning: KL is asymmetric at the number level (KLE p q <> KLE q p in general), so constructively
   the two directions of the swapped argument slots do not imply each other; the corrected-order closure piece
   aiu_backward_kl_exact_uncond (AlignIdUnclosed.v:157) is already on disk. By the AA15 precedent, not proven false -- the shape is only fixed. *)
Definition rwl_aiu_swap_slot (F : Real -> Real -> Real) : Set :=
  forall p q : Real, real_eq (F p q) (F q p).

(* ============================================================ *)
(* Part 7: main-piece closure -- rwl_resid_walls_lpo (the residual-wall closure four-slot account) *)
(* ============================================================ *)

Definition rwl_resid_walls_lpo :
  And (rwl_g07_cmp_wall -> rLPO)
      (And (rwl_g07_cmp_wall -> rwl_snw_wall_face)
           (And (rwl_g07_cmp_wall -> rwl_max_split_wall)
                (And (forall Sq ub, rwl_s14_ptw_wall Sq ub ->
                                    rwl_s14_tail_cert Sq ub)
                     (forall (Sq : nat -> Q) (ub : Q) (M : nat),
                        (forall n : nat, NatLe M n -> QleT' (Sq n) ub) ->
                        (forall n : nat, NatLe n M -> QleT' (Sq n) ub) ->
                        rwl_s14_ptw_wall Sq ub)))) :=
  (rwl_g07_cmp_to_rlpo,
   (rwl_cmp_to_snw_wall,
    (rwl_cmp_to_max_split,
     (rwl_s14_pointwise_to_tail, rwl_s14_tail_plus_head)))).

(* ============================================================ *)
(* Extraction check and assumption audit face                                  *)
(* ============================================================ *)

(* Extraction check: the four bare real_* statement faces are extracted in full (the Part-2 pieces, on the QleT'/NatLe face,
   are likewise Set-valued Id/sigT and enter the face; the Part-3 shape-fixing pieces are not theorems and do not enter).
   All proof bodies are pure combinator compositions + Q-level arithmetic chains, with an observed Obj.magic count = 0. *)
Extraction "_thv3twall3.ml" rwl_g07_cmp_to_rlpo rwl_cmp_to_snw_wall
  rwl_cmp_to_max_split rwl_le_eq_transfer_r
  rwl_s14_pointwise_to_tail rwl_s14_tail_plus_head.

Print Assumptions rwl_q_gap_shift.
Print Assumptions rwl_le_eq_transfer_r.
Print Assumptions rwl_g07_cmp_to_rlpo.
Print Assumptions rwl_cmp_to_snw_wall.
Print Assumptions rwl_cmp_to_max_split.
Print Assumptions rwl_s14_pointwise_to_tail.
Print Assumptions rwl_s14_tail_plus_head.
Print Assumptions rwl_resid_walls_lpo.
