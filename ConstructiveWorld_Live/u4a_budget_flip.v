(* ConstructiveWorld-Set — explicit-modulus variant of the cos zero uniqueness theorem. *)

(** * u4a_budget_flip: an explicit-modulus variant of the cos zero uniqueness theorem.

    Mission.  Under the refined window premise [31/20 < w < 2], the
      Lipschitz inverse bound closes with eps/4 shares (amplification
      factor [120/61 < 2], final bound [60/61 * eps < eps] strictly):
      the eps/8 share of the baseline statement reflects window slack,
      not necessity.  Main statements: [u4a_unique_widened_eps4],
      [u4a_inv_dist_strict], [u4a_inv_dist_wide], [u4a_pi_leibniz_gt_31_10],
      [u4a_pi_unique_eps4].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qround],
      [QArith.Qminmax], [Setoid], [Morphisms], [Lia].  Requires
      [S01_BaseRing]-[S09_EntropyReal], [S10_KVQuantTrig] (the [lp] family,
      the cos zero sequence, the inverse bounds), [S14_B5BatchBlock].

    References.  This development, u4a_budget_flip.v, the baseline
      module in ConstructiveWorld-Main whose statement names are carried
      over here verbatim (statement-face Set-carrier completion); a
      refinement of [S10] [cos_inv_dist_le2]/[cos_pi_half_unique_widened].

    Constructivity.  The main chain is informative at the [Set] layer
      ([real_lt]/[real_eq]/[sigT]); no axioms, no classical logic.  The
      31/10 lower bound is a direct Q-layer computation: the 13-term
      partial sum gives [4 * lp_odd 12 ≈ 3.10315 > 3.101 = 31/10 + 1/1000].

    Build.  [coqc -native-compiler no -q -Q . "" u4a_budget_flip.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

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
Require Import S14_B5BatchBlock.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
Opaque Qred.

(* ============================================================ *)
(* §1 Concrete arithmetic: the explicit value of 4·lp_odd 12 and its comparison against 31/10 + 1/1000 *)
(* ============================================================ *)

(* lp_odd m = Σ_{j=0}^{m} (1/(4j+1) − 1/(4j+3)) (the S10 lp family); *)
(* 4·lp_odd 12 expands to a 13-term sum of 8/((4j+1)(4j+3)).         *)
Lemma u4a_lp_odd12_value :
  QeqT (lp_four * lp_odd 12)
  (8 / (1 * 3) + 8 / (5 * 7) + 8 / (9 * 11) + 8 / (13 * 15) + 8 / (17 * 19)
  + 8 / (21 * 23) + 8 / (25 * 27) + 8 / (29 * 31) + 8 / (33 * 35)
  + 8 / (37 * 39) + 8 / (41 * 43) + 8 / (45 * 47) + 8 / (49 * 51)).
Proof.
  apply qeq_imp_qeqT.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. simpl. lia.
Qed.

(* Concrete comparison: 31/10 + 1/1000 < 4·lp_odd 12 (exact Q-layer decision). *)
Lemma u4a_lp_odd12_margin :
  QltT (31 / 10 + 1 / 1000) (lp_four * lp_odd 12).
Proof.
  apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ u4a_lp_odd12_value).
  unfold Qlt. simpl. lia.
Qed.

(* ============================================================ *)
(* §2 The 31/10 lower bound for the Leibniz π (refined variant of   *)
(*    real_pi_leibniz_gt_three: N := 12, margin := 1/1000, the      *)
(*    monotonicity chain sc_lp_odd_chain).                          *)
(* ============================================================ *)

Lemma u4a_pi_leibniz_gt_31_10 :
  real_lt (real_const (31 / 10)) cauchy_real_pi_leibniz.
Proof.
  unfold real_lt.
  exists (1 / 1000).
  split.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - exists 12%nat.
    intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans _ (lp_four * lp_odd 12 - 31 / 10) _).
    + apply (proj2 (Qlt_minus_iff (1 / 1000) (lp_four * lp_odd 12 - 31 / 10))).
      setoid_replace ((lp_four * lp_odd 12 - 31 / 10) - (1 / 1000))
        with (lp_four * lp_odd 12 - (31 / 10 + 1 / 1000)) by ring.
      apply (proj1 (Qlt_minus_iff (31 / 10 + 1 / 1000) (lp_four * lp_odd 12))).
      exact (QltT_to_Qlt _ _ u4a_lp_odd12_margin).
    + apply Qplus_le_compat.
      * setoid_replace (lp_four * lp_odd 12) with (lp_odd 12 * lp_four) by ring.
        setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
        apply (Qmult_le_compat_r (lp_odd 12) (lp_odd n) lp_four).
        -- apply QleT'_to_Qle. apply sc_lp_odd_chain.
           apply NatLe_drop in Hn. lia.
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
      * apply Qle_refl.
Qed.

(* ============================================================ *)
(* §3 Half-quantity bridge: (1/2)·(31/10) == 31/20 and 31/20 < π_L/2 < 2 *)
(* ============================================================ *)

Lemma u4a_half_const_31_10 :
  real_eq (real_mult (real_const (1 / 2)) (real_const (31 / 10)))
          (real_const (31 / 20)).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _
    (real_mult_proj (real_const (1 / 2)) (real_const (31 / 10)) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 / 2) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (31 / 10) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (31 / 20) n)).
  field.
Qed.

Lemma u4a_pi_leibniz_half_lower :
  real_lt (real_const (31 / 20)) w_leibniz.
Proof.
  unfold w_leibniz.
  apply (real_eq_lt_lt (real_const (31 / 20))
                       (real_mult (real_const (1 / 2)) (real_const (31 / 10))) _).
  - apply real_eq_sym. exact u4a_half_const_31_10.
  - apply (real_lt_eq_lt _ (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz) _).
    + apply (real_lt_mult_compat (real_const (31 / 10)) cauchy_real_pi_leibniz
                                 (real_const (1 / 2))).
      * exact real_half_pos.
      * exact u4a_pi_leibniz_gt_31_10.
    + exact real_half_pi_leibniz_comm.
Qed.

Lemma u4a_pi_leibniz_half_upper_two :
  real_lt w_leibniz (real_const 2).
Proof.
  apply (real_lt_trans _ (real_const (5 / 3)) _).
  - exact real_pi_leibniz_half_upper.
  - apply real_const_lt. apply Qlt_to_QltT. compute. reflexivity.
Qed.

(* ============================================================ *)
(* §4 The inverse-bound family: sum premise u+v >= s implies        *)
(*    v−u < (6/s)·(du+dv), in two tiers.  The core estimate         *)
(*    cos_inv_pt: (v²−u²)/6 < du+dv (S10).                          *)
(* ============================================================ *)

(* Tier 31/10: u+v >= 31/10 implies v−u < (60/31)·(du+dv), and 60/31 < 2. *)
Lemma u4a_inv_dist_strict : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qle (31 / 10) (u + v) ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  QltT (v - u) (60 / 31 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hsum Hdu Hdv.
  apply Qlt_to_QltT.
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { exact (QltT_to_Qlt _ _ (cos_inv_pt u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv)). }
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (HvuS : Qle ((v - u) * (31 / 10)) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) (31 / 10) (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split.
      + change (Qle 0 (31 / 10)). unfold Qle, Qdiv. simpl. lia.
      + rewrite (Qplus_comm v u). exact Hsum. }
  assert (Hle1 : Qle (v - u) ((v * v - u * u) * (10 / 31))).
  { apply (Qle_trans _ (((v - u) * (31 / 10)) * (10 / 31)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hr : ((v - u) * (31 / 10)) * (10 / 31) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr.
    - apply (Qmult_le_compat_r ((v - u) * (31 / 10)) (v * v - u * u) (10 / 31)).
      + apply (Qle_trans _ ((v - u) * (v + u)) _).
        * exact HvuS.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hprod.
      + apply (Qlt_le_weak 0 (10 / 31)).
        change (Qlt 0 (10 / 31)). unfold Qdiv. compute. reflexivity. }
  assert (Hm : (v * v - u * u) * (10 / 31) == ((v * v - u * u) * (1 / 6)) * (60 / 31))
    by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  assert (Hm2 : (du + dv) * (60 / 31) == (60 / 31) * (du + dv)) by ring.
  apply (Qlt_le_trans (v - u) ((du + dv) * (60 / 31)) (60 / 31 * (du + dv))).
  - apply (Qle_lt_trans (v - u) ((v * v - u * u) * (10 / 31)) ((du + dv) * (60 / 31))).
    + exact Hle1.
    + apply (Qle_lt_trans ((v * v - u * u) * (10 / 31))
                         (((v * v - u * u) * (1 / 6)) * (60 / 31))
                         ((du + dv) * (60 / 31))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) (60 / 31)).
        -- change (Qlt 0 (60 / 31)). unfold Qdiv. compute. reflexivity.
        -- exact Hq.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm2.
Qed.

(* Tier 61/20: u+v >= 61/20 (= 3/2 + 31/20) implies                 *)
(* v−u < (120/61)·(du+dv), and 120/61 < 2.  The z-side sequence     *)
(* has only the lower bound 3/2, so this tier is the application    *)
(* form of the uniqueness theorem.                                  *)
Lemma u4a_inv_dist_wide : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qle (61 / 20) (u + v) ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const u)) k - projT1 real_zero k)) du ->
  Qlt (Qabs (projT1 (cauchy_real_cos (real_const v)) k - projT1 real_zero k)) dv ->
  QltT (v - u) (120 / 61 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu0 Huv Hv2 Hsum Hdu Hdv.
  apply Qlt_to_QltT.
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { exact (QltT_to_Qlt _ _ (cos_inv_pt u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv)). }
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (HvuW : Qle ((v - u) * (61 / 20)) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) (61 / 20) (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split.
      + change (Qle 0 (61 / 20)). unfold Qle, Qdiv. simpl. lia.
      + rewrite (Qplus_comm v u). exact Hsum. }
  assert (Hle1 : Qle (v - u) ((v * v - u * u) * (20 / 61))).
  { apply (Qle_trans _ (((v - u) * (61 / 20)) * (20 / 61)) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      assert (Hr : ((v - u) * (61 / 20)) * (20 / 61) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr.
    - apply (Qmult_le_compat_r ((v - u) * (61 / 20)) (v * v - u * u) (20 / 61)).
      + apply (Qle_trans _ ((v - u) * (v + u)) _).
        * exact HvuW.
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hprod.
      + apply (Qlt_le_weak 0 (20 / 61)).
        change (Qlt 0 (20 / 61)). unfold Qdiv. compute. reflexivity. }
  assert (Hm : (v * v - u * u) * (20 / 61) == ((v * v - u * u) * (1 / 6)) * (120 / 61))
    by (unfold Qdiv; field; unfold Qeq; simpl; lia).
  assert (Hm2 : (du + dv) * (120 / 61) == (120 / 61) * (du + dv)) by ring.
  apply (Qlt_le_trans (v - u) ((du + dv) * (120 / 61)) (120 / 61 * (du + dv))).
  - apply (Qle_lt_trans (v - u) ((v * v - u * u) * (20 / 61)) ((du + dv) * (120 / 61))).
    + exact Hle1.
    + apply (Qle_lt_trans ((v * v - u * u) * (20 / 61))
                         (((v * v - u * u) * (1 / 6)) * (120 / 61))
                         ((du + dv) * (120 / 61))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) (120 / 61)).
        -- change (Qlt 0 (120 / 61)). unfold Qdiv. compute. reflexivity.
        -- exact Hq.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm2.
Qed.

(* ============================================================ *)
(* §5 Main theorem: uniqueness of the zero under the refined window, *)
(*    eps/4 shares.  Window premise 31/20 < w < 2; the two diagonal  *)
(*    bounds, the Cauchy indices, and the inverse-bound pair all     *)
(*    take eps/4; final bound (120/61)·(eps/4+eps/4) = 60/61·eps < eps. *)
(* ============================================================ *)

Lemma u4a_unique_widened_eps4 : forall (w : Real),
  real_lt (real_const (31 / 20)) w -> real_lt w (real_const 2) ->
  real_eq (cauchy_real_cos w) real_zero ->
  real_eq w cos_pi_half.
Proof.
  intros w Hlow Hup Hw0.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps4 : Qlt 0 (eps / 4)).
  { apply (Qlt_shift_div_l 0 eps 4).
    - change (Qlt 0 4). compute. reflexivity.
    - simpl. exact HepsQ. }
  (* Sources of the pointwise bounds: w side (endpoints + the cos w == 0 diagonal), z side (cos_zero_lower/upper + the cos z == 0 diagonal) *)
  destruct (real_lt_lower_pt (31 / 20) w Hlow) as [Nlo HNlo].
  destruct (real_lt_upper_pt 2 w Hup) as [Nup HNup].
  destruct (cos_eq_zero_diag_bound w Hw0 (eps / 4) Heps4) as [Nwd Hwd].
  destruct (cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero (eps / 4) Heps4) as [Nzd Hzd].
  destruct (q_pow_arch 1 (eps / 4) (qltT_leT' 0 1 qltT_0_1)
             (Qlt_to_QltT _ _ Heps4)) as [t Ht].
  set (A := Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))).
  exists (Nat.max 2 (Nat.max A (Datatypes.S t))).
  intros n Hn.
  apply Qlt_to_QltT.
  assert (Hn2 : (2 <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]).
  assert (HnAt : (Nat.max A (Datatypes.S t) <= n)%nat) by (apply (Nat.le_trans _ (Nat.max 2 (Nat.max A (Datatypes.S t))) _); [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]).
  assert (HnA : (A <= n)%nat) by (apply (Nat.le_trans _ (Nat.max A (Datatypes.S t)) _); [apply Nat.le_max_l | exact HnAt]).
  assert (Hnlo : (Nlo <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nlo (Nat.max Nup (Nat.max Nwd Nzd))) _); [apply Nat.le_max_l | ].
    unfold A in HnA. exact HnA. }
  assert (Hnup : (Nup <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnwd : (Nwd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_l | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  assert (Hnzd : (Nzd <= n)%nat).
  { apply (Nat.le_trans _ (Nat.max Nwd Nzd) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ (Nat.max Nup (Nat.max Nwd Nzd)) _); [apply Nat.le_max_r | ].
    apply (Nat.le_trans _ A _); [apply Nat.le_max_r | exact HnA]. }
  (* w_n ∈ (31/20, 2) and z_n ∈ (3/2, 5/3) (Q layer) *)
  assert (Hwlo : Qle (31 / 20) (projT1 w n)) by (apply Qlt_le_weak; apply (HNlo n); exact Hnlo).
  assert (Hwup : Qle (projT1 w n) 2) by (apply Qlt_le_weak; apply (HNup n); exact Hnup).
  assert (Hzlo : Qle (3 / 2) (cos_zero_seq n)) by (apply Qlt_le_weak; apply QltT_to_Qlt; apply cos_zero_lower).
  assert (Hzup : Qle (cos_zero_seq n) (5 / 3)) by (apply Qlt_le_weak; apply QltT_to_Qlt; apply cos_zero_upper).
  (* z-side v <= 2 (by transitivity from 5/3 <= 2; premise of cos_inv_pt) *)
  assert (Hzup2 : Qle (cos_zero_seq n) 2).
  { apply (Qle_trans _ (5 / 3) _); [exact Hzup | change (Qle (5 / 3) 2); unfold Qle, Qdiv; simpl; lia]. }
  (* Two forms of the sum premise: 3/2 + 31/20 == 61/20 *)
  assert (HsumB1 : Qle (61 / 20) (cos_zero_seq n + projT1 w n)).
  { apply (Qle_trans _ (3 / 2 + 31 / 20) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
    - apply (Qplus_le_compat (3 / 2) (cos_zero_seq n) (31 / 20) (projT1 w n)).
      + apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lower.
      + apply Qlt_le_weak. apply (HNlo n). exact Hnlo. }
  assert (HsumB2 : Qle (61 / 20) (projT1 w n + cos_zero_seq n)).
  { apply (Qle_trans _ (31 / 20 + 3 / 2) _).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qdiv. field.
    - apply (Qplus_le_compat (31 / 20) (projT1 w n) (3 / 2) (cos_zero_seq n)).
      + apply Qlt_le_weak. apply (HNlo n). exact Hnlo.
      + apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lower. }
  (* Diagonal bounds |cos w_n| and |cos z_n| < eps/4 *)
  assert (Hwpt : Qlt (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n)) (eps / 4)).
  { exact (QltT_to_Qlt _ _ (Hwd n Hnwd)). }
  assert (Hzpt : Qlt (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n)) (eps / 4)).
  { exact (QltT_to_Qlt _ _ (Hzd n Hnzd)). }
  (* Branch: |w_n − z_n| <= (120/61)·(eps/2) = 60/61·eps < eps (inverse bound, u := the smaller) *)
  destruct (Qlt_le_dec (cos_zero_seq n) (projT1 w n)) as [Hzw | Hwz].
  - (* z_n < w_n: u := z_n, v := w_n *)
    assert (Hd : Qlt (projT1 w n - cos_zero_seq n) (120 / 61 * (eps / 4 + eps / 4))).
    { apply QltT_to_Qlt.
      apply (u4a_inv_dist_wide (cos_zero_seq n) (projT1 w n)
                               (eps / 4) (eps / 4) n).
      - exact Hn2.
      - apply (Qle_trans _ (3 / 2) _).
        + change (Qle 0 (3 / 2)). unfold Qle, Qdiv. simpl. lia.
        + apply Qlt_le_weak. apply QltT_to_Qlt. apply cos_zero_lower.
      - apply Qlt_le_weak. exact Hzw.
      - exact Hwup.
      - exact HsumB1.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 4)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt.
      - assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 4)).
        { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                              (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                              (eps / 4)).
          - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
            assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
            { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
            rewrite Hq. reflexivity.
          - exact Hwpt. }
        exact Hwpt'.
    }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (projT1 w n - cos_zero_seq n) eps).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (cos_zero_seq n) (projT1 w n))). apply Qlt_le_weak. exact Hzw.
    + apply (Qle_lt_trans _ (120 / 61 * (eps / 4 + eps / 4)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 120 / 61 * (eps / 4 + eps / 4) == 60 / 61 * eps) by (unfold Qdiv; field).
        apply (Qle_lt_trans (120 / 61 * (eps / 4 + eps / 4)) (60 / 61 * eps) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (60 / 61 * eps) eps)).
           apply (Qlt_le_trans 0 (eps / 61) (eps - 60 / 61 * eps)).
           ++ apply (Qlt_shift_div_l 0 eps 61).
              ** change (Qlt 0 61). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
  - (* w_n <= z_n: u := w_n, v := z_n (symmetric) *)
    assert (Hwpt' : Qlt (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n)) (eps / 4)).
    { apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (projT1 w n))) n - projT1 real_zero n))
                          (Qabs (projT1 (cauchy_real_cos w) n - projT1 real_zero n))
                          (eps / 4)).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
        assert (Hq : projT1 (cauchy_real_cos (real_const (projT1 w n))) n == projT1 (cauchy_real_cos w) n).
        { rewrite (qeqT_imp_qeq _ _ (real_cos_proj (real_const (projT1 w n)) n)). rewrite (qeqT_imp_qeq _ _ (real_cos_proj w n)). reflexivity. }
        rewrite Hq. reflexivity.
      - exact Hwpt. }
    assert (Hd : Qlt (cos_zero_seq n - projT1 w n) (120 / 61 * (eps / 4 + eps / 4))).
    { apply QltT_to_Qlt.
      apply (u4a_inv_dist_wide (projT1 w n) (cos_zero_seq n)
                               (eps / 4) (eps / 4) n).
      - exact Hn2.
      - apply (Qle_trans _ (31 / 20) _).
        + change (Qle 0 (31 / 20)). unfold Qle, Qdiv. simpl. lia.
        + apply Qlt_le_weak. apply (HNlo n). exact Hnlo.
      - exact Hwz.
      - exact Hzup2.
      - exact HsumB2.
      - exact Hwpt'.
      - apply (Qle_lt_trans (Qabs (projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n - projT1 real_zero n))
                            (Qabs (projT1 (cauchy_real_cos cos_pi_half) n - projT1 real_zero n))
                            (eps / 4)).
        + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_wd.
          assert (Hp : projT1 (cauchy_real_cos (real_const (cos_zero_seq n))) n ==
                       projT1 (cauchy_real_cos cos_pi_half) n).
          { cbn [projT1 cauchy_real_cos cos_pi_half real_const]. reflexivity. }
          rewrite Hp. reflexivity.
        + exact Hzpt. }
    apply (Qle_lt_trans (Qabs (projT1 w n - cos_zero_seq n)) (cos_zero_seq n - projT1 w n) eps).
    + rewrite (Qabs_Qminus (projT1 w n) (cos_zero_seq n)).
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qabs_pos. apply (proj1 (Qle_minus_iff (projT1 w n) (cos_zero_seq n))). exact Hwz.
    + apply (Qle_lt_trans _ (120 / 61 * (eps / 4 + eps / 4)) _).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hm : 120 / 61 * (eps / 4 + eps / 4) == 60 / 61 * eps) by (unfold Qdiv; field).
        apply (Qle_lt_trans (120 / 61 * (eps / 4 + eps / 4)) (60 / 61 * eps) eps).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hm.
        -- apply (proj2 (Qlt_minus_iff (60 / 61 * eps) eps)).
           apply (Qlt_le_trans 0 (eps / 61) (eps - 60 / 61 * eps)).
           ++ apply (Qlt_shift_div_l 0 eps 61).
              ** change (Qlt 0 61). compute. reflexivity.
              ** simpl. exact HepsQ.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. unfold Qminus. field.
Qed.

(* ============================================================ *)
(* §6 Application form: the π_L/2 vertex (w_leibniz) still satisfies *)
(*    the three premises inside the refined window; the eps/4-form   *)
(*    theorem gives w_leibniz == cos_pi_half.                        *)
(* ============================================================ *)

Lemma u4a_pi_unique_eps4 : real_eq w_leibniz cos_pi_half.
Proof.
  apply (u4a_unique_widened_eps4 w_leibniz).
  - exact u4a_pi_leibniz_half_lower.
  - exact u4a_pi_leibniz_half_upper_two.
  - exact b5dU_cos_piL_half_zero.
Qed.
