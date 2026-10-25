(* ConstructiveWorld-Set — explicit two-sided rational envelopes with explicit
   tails, applied to ln 2, e, and the Leibniz series for pi. *)

(** * UpReqConstEnvelope: two-sided rational envelopes with explicit tails.

    Mission.  Formalizes the envelope assembly lemma [c3e_env_mother] (a tail
    bound on partial sums yields a two-sided Bishop envelope together with the
    width identity), the paired alternating-series machinery [c3e_l2_*], the
    Cauchy real [c3e_ln2_real] of ln 2, the envelope theorems
    [c3e_env_ln2]/[c3e_env_e]/[c3e_env_pi], and the rate moduli
    [c3e_env_rate]/[c3e_env_rate_ln2].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.PeanoNat],
    [Lia].  Requires [S01_BaseRing] through [S15_TailFEPUp] and [UpRealLeB]
    of this development.

    References.  This development, the ConstructiveWorld-Main baseline module
    [UpReqConstEnvelope.v], whose statement names are carried over here
    verbatim; comparison and equality faces are carried by the [Set] carriers
    [QltT]/[QleT']/[QeqT] and the [Set]-valued [And]/[Or].

    Constructivity.  All named statements and fields are carried by [Set]
    ([QltT]/[QleT']/[QeqT], [And]/[Or] over [Set] carriers); existence
    statements are packaged as [sigT] witnesses; statements extract with
    [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqConstEnvelope.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact are
    [436f7121 00015ff4]. *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat Lia.

(* ============================================================ *)
(* S0. Small rational-layer facts                                   *)
(* ============================================================ *)

(* Trichotomy: 0 < z or z <= 0 (case analysis on Qcompare 0 z, via
   Qlt_alt/Qeq_alt/Qgt_alt). *)
Lemma c3e_ztri : forall z : Q, Or (QltT 0 z) (QleT' z 0).
Proof.
  intro z.
  destruct (Qcompare 0 z) eqn:E.
  - right. apply Qle_to_QleT'. apply QleT'_to_Qle. apply qeq_le.
    apply qeq_imp_qeqT. apply (Qeq_sym 0 z).
    apply (proj2 (Qeq_alt 0 z)). exact E.
  - left. apply Qlt_to_QltT. apply (proj2 (Qlt_alt 0 z)). exact E.
  - right. apply Qle_to_QleT'. apply (Qlt_le_weak z 0).
    apply (proj2 (Qgt_alt 0 z)). exact E.
Qed.

(* z <= |z| (rational layer). *)
Lemma c3e_qle_abs : forall z : Q, QleT' z (Qabs z).
Proof.
  intro z.
  apply Qle_to_QleT'.
  destruct (c3e_ztri z) as [Hz | Hz].
  - apply QltT_to_Qlt in Hz.
    rewrite (Qabs_pos z (Qlt_le_weak 0 z Hz)). apply Qle_refl.
  - apply QleT'_to_Qle in Hz.
    rewrite (Qabs_neg z Hz).
    apply (proj2 (Qle_minus_iff z (- z))).
    setoid_replace (- z - z) with (-(z + z)) by ring.
    apply (Qle_trans _ (- (0 + 0))).
    + setoid_replace (- (0 + 0)) with 0 by ring. apply Qle_refl.
    + apply (Qopp_le_compat (z + z) (0 + 0)).
      apply (Qplus_le_compat z 0 z 0); [ exact Hz | exact Hz ].
Qed.

(* -|z| <= z (rational layer). *)
Lemma c3e_neg_abs_le : forall z : Q, QleT' (- Qabs z) z.
Proof.
  intro z.
  apply Qle_to_QleT'.
  destruct (c3e_ztri z) as [Hz | Hz].
  - apply QltT_to_Qlt in Hz.
    rewrite (Qabs_pos z (Qlt_le_weak 0 z Hz)).
    apply (Qle_trans (- z) 0 z).
    + apply (Qle_trans (- z) (- 0) 0).
      * apply (Qopp_le_compat 0 z). exact (Qlt_le_weak 0 z Hz).
      * setoid_replace (- 0) with 0 by ring. apply Qle_refl.
    + exact (Qlt_le_weak 0 z Hz).
  - apply QleT'_to_Qle in Hz.
    rewrite (Qabs_neg z Hz).
    setoid_replace (- (- z)) with z by ring.
    apply Qle_refl.
Qed.

(* |z| <= w entails 0 <= z + w and 0 <= w - z (the rational core of the
   envelope assembly certificate). *)
Lemma c3e_abs_two : forall (z w : Q), Qle (Qabs z) w ->
  And (QleT' 0 (z + w)) (QleT' 0 (w - z)).
Proof.
  intros z w H. split.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ ((- Qabs z) + Qabs z)).
    + setoid_replace ((- Qabs z) + Qabs z) with 0 by ring. apply Qle_refl.
    + apply (Qle_trans _ (z + Qabs z)).
      * apply (Qplus_le_compat (- Qabs z) z (Qabs z) (Qabs z)).
        -- apply QleT'_to_Qle. apply c3e_neg_abs_le.
        -- apply Qle_refl.
      * apply (Qplus_le_compat z z (Qabs z) w).
        -- apply Qle_refl.
        -- exact H.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (w - Qabs z)).
    + exact (proj1 (Qle_minus_iff (Qabs z) w) H).
    + setoid_replace (w - Qabs z) with (w + (- Qabs z)) by ring.
      setoid_replace (w - z) with (w + (- z)) by ring.
      apply (Qplus_le_compat w w (- Qabs z) (- z)).
      * apply Qle_refl.
      * apply (Qopp_le_compat z (Qabs z)).
        apply QleT'_to_Qle. apply c3e_qle_abs.
Qed.

(* U - V <= U for V >= 0 (closing step for stretched tail bounds). *)
Lemma c3e_sub_le_self : forall (U V : Q), Qle 0 V -> QleT' (U - V) U.
Proof.
  intros U V Hv.
  apply Qle_to_QleT'.
  setoid_replace (U - V) with (U + (- V)) by ring.
  apply (Qle_trans _ (U + 0)).
  - apply (Qplus_le_compat U U (- V) 0).
    + apply Qle_refl.
    + setoid_replace 0 with (- 0) by ring.
      apply (Qopp_le_compat 0 V). exact Hv.
  - setoid_replace (U + 0) with U by ring. apply Qle_refl.
Qed.

(* Reciprocal comparison: b <= a entails 1/(a+2) <= 1/(b+2) (a direct
   consequence of q_le_div_le). *)
Lemma c3e_inv_le_inv : forall a b : nat, (b <= a)%nat ->
  QleT' (1 / (Z.of_nat (a + 2) # 1)) (1 / (Z.of_nat (b + 2) # 1)).
Proof.
  intros a b Hab.
  apply (q_le_div_le 1 (Z.of_nat (a + 2) # 1) 1 (Z.of_nat (b + 2) # 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qle_to_QleT'. setoid_replace (1 * (Z.of_nat (b + 2) # 1))
      with (Z.of_nat (b + 2) # 1) by (apply Qmult_1_l).
    setoid_replace (1 * (Z.of_nat (a + 2) # 1))
      with (Z.of_nat (a + 2) # 1) by (apply Qmult_1_l).
    unfold Qle; simpl; lia.
Qed.

(* projT1 real_zero k == 0 (by definitional reduction of real_zero). *)
Lemma c3e_real_zero_proj : forall k : nat, QeqT (projT1 real_zero k) 0.
Proof.
  intro k. apply qeq_imp_qeqT. exact (Qeq_refl (projT1 real_zero k)).
Qed.

(* ============================================================ *)
(* S1. Assembly theorem: two-sided rational envelope with explicit tail
   (c3e_env_mother)                                                  *)
(* ============================================================ *)

(* Given x : Real, partial sums s0, an explicit tail bound t0 (one-sided
   width certificate) and an index n: if s0 - t0 <= projT1 x k <= s0 + t0
   holds for all k >= n, then lo := s0 - t0 and hi := s0 + t0 form a
   Bishop-style two-sided rational envelope of x, lo <=_B x <=_B hi, with
   the width identity hi - lo == 2 * t0. *)
Theorem c3e_env_mother : forall (x : Real) (s0 t0 : Q) (n : nat),
  (forall k : nat, (n <= k)%nat ->
    And (QleT' (s0 - t0) (projT1 x k))
        (QleT' (projT1 x k) (s0 + t0))) ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) x)
        (And (real_le_b x (real_const hi))
             (QeqT (hi - lo) (2 * t0))))).
Proof.
  intros x s0 t0 n Hptw.
  exists (s0 - t0). exists (s0 + t0).
  split.
  - (* Lower side: real_const (s0 - t0) <=_B x *)
    unfold real_le_b. intros eps Heps.
    unfold real_lt in Heps. unfold real_lt.
    destruct Heps as [d [Hd [N0 HN0]]].
    exists d. split.
    + exact Hd.
    + exists (Nat.max N0 n). intros k HkN.
      apply Qlt_to_QltT.
      assert (HkLe : (n <= k)%nat).
      { apply (Nat.le_trans n (Nat.max N0 n) k).
        - apply Nat.le_max_r.
        - apply (NatLe_drop _ _ HkN). }
      assert (HkN0 : NatLe N0 k).
      { apply NatLe_lift. apply (Nat.le_trans N0 (Nat.max N0 n) k).
        - apply Nat.le_max_l.
        - apply (NatLe_drop _ _ HkN). }
      destruct (Hptw k HkLe) as [Hlo Hhi].
      apply QleT'_to_Qle in Hlo. apply QleT'_to_Qle in Hhi.
      specialize (HN0 k HkN0). apply QltT_to_Qlt in HN0.
      rewrite (qeqT_imp_qeq _ _ (c3e_real_zero_proj k)) in HN0.
      assert (Hz0 : projT1 eps k - 0 == projT1 eps k) by ring.
      rewrite Hz0 in HN0.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj x eps k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (s0 - t0) k)).
      assert (Hshift : Qle (projT1 eps k)
                           (projT1 x k + projT1 eps k - (s0 - t0))).
      { apply (proj2 (Qle_minus_iff (projT1 eps k)
                        (projT1 x k + projT1 eps k - (s0 - t0)))).
        setoid_replace (projT1 x k + projT1 eps k - (s0 - t0) - projT1 eps k)
          with (projT1 x k - (s0 - t0)) by ring.
        exact (proj1 (Qle_minus_iff (s0 - t0) (projT1 x k)) Hlo). }
      exact (Qlt_le_trans d (projT1 eps k) _ HN0 Hshift).
  - (* Upper side: x <=_B real_const (s0 + t0) *)
    split.
    unfold real_le_b. intros eps Heps.
    unfold real_lt in Heps. unfold real_lt.
    destruct Heps as [d [Hd [N0 HN0]]].
    exists d. split.
    + exact Hd.
    + exists (Nat.max N0 n). intros k HkN.
      apply Qlt_to_QltT.
      assert (HkLe : (n <= k)%nat).
      { apply (Nat.le_trans n (Nat.max N0 n) k).
        - apply Nat.le_max_r.
        - apply (NatLe_drop _ _ HkN). }
      assert (HkN0 : NatLe N0 k).
      { apply NatLe_lift. apply (Nat.le_trans N0 (Nat.max N0 n) k).
        - apply Nat.le_max_l.
        - apply (NatLe_drop _ _ HkN). }
      destruct (Hptw k HkLe) as [Hlo Hhi].
      apply QleT'_to_Qle in Hlo. apply QleT'_to_Qle in Hhi.
      specialize (HN0 k HkN0). apply QltT_to_Qlt in HN0.
      rewrite (qeqT_imp_qeq _ _ (c3e_real_zero_proj k)) in HN0.
      assert (Hz0 : projT1 eps k - 0 == projT1 eps k) by ring.
      rewrite Hz0 in HN0.
      rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_const (s0 + t0)) eps k)).
      rewrite (qeqT_imp_qeq _ _ (real_const_proj (s0 + t0) k)).
      assert (Hshift : Qle (projT1 eps k)
                           (s0 + t0 + projT1 eps k - projT1 x k)).
      { apply (proj2 (Qle_minus_iff (projT1 eps k)
                        (s0 + t0 + projT1 eps k - projT1 x k))).
        setoid_replace (s0 + t0 + projT1 eps k - projT1 x k - projT1 eps k)
          with (s0 + t0 - projT1 x k) by ring.
        exact (proj1 (Qle_minus_iff (projT1 x k) (s0 + t0)) Hhi). }
      exact (Qlt_le_trans d (projT1 eps k) _ HN0 Hshift).
    + (* Width: hi - lo == 2 * t0 *)
      apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* S2. ln 2 component: paired positive-term alternating harmonic series
   (fully constructive, self-contained single-jump argument)          *)
(* ============================================================ *)

(* Paired alternating harmonic term: 1/(2j+1) - 1/(2j+2) (positive and
   decreasing). *)
Definition c3e_l2_term (j : nat) : Q :=
  1 / (Z.of_nat (2 * j + 1) # 1) - 1 / (Z.of_nat (2 * j + 2) # 1).

Fixpoint c3e_l2_sum (m : nat) : Q :=
  match m with
  | Datatypes.O => c3e_l2_term 0
  | Datatypes.S p => c3e_l2_sum p + c3e_l2_term (Datatypes.S p)
  end.

(* Stretched term bound: term (Datatypes.S p) <= 1/(2p+2) - 1/(2p+4). *)
Lemma c3e_l2_term_le : forall p : nat,
  QleT' (c3e_l2_term (Datatypes.S p))
      (1 / (Z.of_nat (2 * p + 2) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1)).
Proof.
  intro p.
  apply Qle_to_QleT'.
  unfold c3e_l2_term.
  replace (Z.of_nat (2 * Datatypes.S p + 1)) with (Z.of_nat (2 * p + 3)) by lia.
  replace (Z.of_nat (2 * Datatypes.S p + 2)) with (Z.of_nat (2 * p + 4)) by lia.
  setoid_replace (1 / (Z.of_nat (2 * p + 3) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1))
    with (- (1 / (Z.of_nat (2 * p + 4) # 1)) + 1 / (Z.of_nat (2 * p + 3) # 1)) by ring.
  setoid_replace (1 / (Z.of_nat (2 * p + 2) # 1) - 1 / (Z.of_nat (2 * p + 4) # 1))
    with (- (1 / (Z.of_nat (2 * p + 4) # 1)) + 1 / (Z.of_nat (2 * p + 2) # 1)) by ring.
  apply (Qplus_le_compat (- (1 / (Z.of_nat (2 * p + 4) # 1)))
                         (- (1 / (Z.of_nat (2 * p + 4) # 1)))
                         (1 / (Z.of_nat (2 * p + 3) # 1))
                         (1 / (Z.of_nat (2 * p + 2) # 1))).
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply (q_le_div_le 1 (Z.of_nat (2 * p + 3) # 1) 1 (Z.of_nat (2 * p + 2) # 1)).
    + apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    + apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    + apply Qle_to_QleT'. setoid_replace (1 * (Z.of_nat (2 * p + 2) # 1))
        with (Z.of_nat (2 * p + 2) # 1) by (apply Qmult_1_l).
      setoid_replace (1 * (Z.of_nat (2 * p + 3) # 1))
        with (Z.of_nat (2 * p + 3) # 1) by (apply Qmult_1_l).
      unfold Qle; simpl; lia.
Qed.

(* Term positivity: term (Datatypes.S p) >= 0. *)
Lemma c3e_l2_term_pos : forall p : nat, QleT' 0 (c3e_l2_term (Datatypes.S p)).
Proof.
  intro p.
  apply Qle_to_QleT'.
  unfold c3e_l2_term.
  replace (Z.of_nat (2 * Datatypes.S p + 1)) with (Z.of_nat (2 * p + 3)) by lia.
  replace (Z.of_nat (2 * Datatypes.S p + 2)) with (Z.of_nat (2 * p + 4)) by lia.
  apply (proj1 (Qle_minus_iff (1 / (Z.of_nat (2 * p + 4) # 1))
                              (1 / (Z.of_nat (2 * p + 3) # 1)))).
  apply QleT'_to_Qle. apply (q_le_div_le 1 (Z.of_nat (2 * p + 4) # 1) 1 (Z.of_nat (2 * p + 3) # 1)).
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qlt_to_QltT. unfold Qlt; simpl; lia.
  - apply Qle_to_QleT'. setoid_replace (1 * (Z.of_nat (2 * p + 3) # 1))
      with (Z.of_nat (2 * p + 3) # 1) by (apply Qmult_1_l).
    setoid_replace (1 * (Z.of_nat (2 * p + 4) # 1))
      with (Z.of_nat (2 * p + 4) # 1) by (apply Qmult_1_l).
    unfold Qle; simpl; lia.
Qed.

(* Partial-sum monotonicity: one step plus chaining. *)
Lemma c3e_l2_sum_step : forall m : nat, QleT' (c3e_l2_sum m) (c3e_l2_sum (Datatypes.S m)).
Proof.
  intro m.
  apply Qle_to_QleT'.
  setoid_replace (c3e_l2_sum (Datatypes.S m)) with (c3e_l2_sum m + c3e_l2_term (Datatypes.S m))
    by reflexivity.
  apply Qle_plus_nonneg_r.
  apply QleT'_to_Qle. apply c3e_l2_term_pos.
Qed.

Lemma c3e_l2_mono : forall m n : nat, (m <= n)%nat -> QleT' (c3e_l2_sum m) (c3e_l2_sum n).
Proof.
  intros m n.
  induction n as [| n IH]; intro Hmn.
  - apply Qle_to_QleT'.
    assert (Hm0 : (m = 0)%nat) by lia. subst m. apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n)) as [He | Hne].
    + subst m. apply Qle_to_QleT'. apply Qle_refl.
    + assert (Hmn' : (m <= n)%nat) by lia.
      apply Qle_to_QleT'.
      apply (Qle_trans _ (c3e_l2_sum n)).
      * apply QleT'_to_Qle. apply IH. exact Hmn'.
      * apply QleT'_to_Qle. apply c3e_l2_sum_step.
Qed.

(* Stretched tail bound (core single-jump step): n <= m entails
   s m - s n <= 1/(2n+2) - 1/(2m+2). *)
Lemma c3e_l2_inv : forall m n : nat, (n <= m)%nat ->
  QleT' (c3e_l2_sum m - c3e_l2_sum n)
      (1 / (Z.of_nat (2 * n + 2) # 1) - 1 / (Z.of_nat (2 * m + 2) # 1)).
Proof.
  intros m n.
  induction m as [| m IH]; intro Hnm.
  - apply Qle_to_QleT'.
    assert (Hn0 : (n = 0)%nat) by lia. subst n.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [He | Hne].
    + apply Qle_to_QleT'.
      subst n.
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply Qle_to_QleT'.
      assert (Hnm' : (n <= m)%nat) by lia.
      specialize (IH Hnm').
      assert (Hstep : c3e_l2_sum (Datatypes.S m)
                      == c3e_l2_sum m + c3e_l2_term (Datatypes.S m)) by reflexivity.
      rewrite Hstep.
      setoid_replace ((c3e_l2_sum m + c3e_l2_term (Datatypes.S m)) - c3e_l2_sum n)
        with ((c3e_l2_sum m - c3e_l2_sum n) + c3e_l2_term (Datatypes.S m)) by ring.
      apply (Qle_trans _ ((1 / (Z.of_nat (2 * n + 2) # 1)
                           - 1 / (Z.of_nat (2 * m + 2) # 1))
                          + (1 / (Z.of_nat (2 * m + 2) # 1)
                             - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)))).
      * apply (Qplus_le_compat (c3e_l2_sum m - c3e_l2_sum n)
                               (1 / (Z.of_nat (2 * n + 2) # 1)
                                - 1 / (Z.of_nat (2 * m + 2) # 1))
                               (c3e_l2_term (Datatypes.S m))
                               (1 / (Z.of_nat (2 * m + 2) # 1)
                                - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1))).
        -- apply QleT'_to_Qle. exact IH.
        -- replace (Z.of_nat (2 * Datatypes.S m + 2)) with (Z.of_nat (2 * m + 4)) by lia.
           apply QleT'_to_Qle. apply c3e_l2_term_le.
      * setoid_replace ((1 / (Z.of_nat (2 * n + 2) # 1)
                         - 1 / (Z.of_nat (2 * m + 2) # 1))
                        + (1 / (Z.of_nat (2 * m + 2) # 1)
                           - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)))
          with (1 / (Z.of_nat (2 * n + 2) # 1)
                - 1 / (Z.of_nat (2 * Datatypes.S m + 2) # 1)) by ring.
        apply Qle_refl.
Qed.

(* One-sided width certificate (input to the assembly theorem): for
   n <= k, s n - U <= s k <= s n + U with U := 1/(2n+2). *)
Lemma c3e_l2_cert : forall n k : nat, (n <= k)%nat ->
  And (QleT' (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1)) (c3e_l2_sum k))
      (QleT' (c3e_l2_sum k) (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1))).
Proof.
  intros n k Hnk. split.
  - (* s n − U ≤ s n ≤ s k *)
    apply Qle_to_QleT'.
    apply (Qle_trans _ (c3e_l2_sum n)).
    + apply (proj2 (Qle_minus_iff (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1))
                                  (c3e_l2_sum n))).
      setoid_replace (c3e_l2_sum n - (c3e_l2_sum n - 1 / (Z.of_nat (2 * n + 2) # 1)))
        with (1 / (Z.of_nat (2 * n + 2) # 1)) by ring.
      apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * n + 2) # 1))).
      exact (QltT_to_Qlt _ _ (q_arch_inv_pos (2 * n))).
    + apply QleT'_to_Qle. apply c3e_l2_mono. exact Hnk.
  - (* s k <= s n + U: s k - s n <= U - V <= U. *)
    apply Qle_to_QleT'.
    apply (proj2 (Qle_minus_iff (c3e_l2_sum k)
                                (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1)))).
    setoid_replace (c3e_l2_sum n + 1 / (Z.of_nat (2 * n + 2) # 1) - c3e_l2_sum k)
      with (1 / (Z.of_nat (2 * n + 2) # 1) - (c3e_l2_sum k - c3e_l2_sum n)) by ring.
    apply (Qle_trans _ (1 / (Z.of_nat (2 * k + 2) # 1))).
    + apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * k + 2) # 1))).
      exact (QltT_to_Qlt _ _ (q_arch_inv_pos (2 * k))).
    + apply (proj2 (Qle_minus_iff (1 / (Z.of_nat (2 * k + 2) # 1))
                                  (1 / (Z.of_nat (2 * n + 2) # 1)
                                   - (c3e_l2_sum k - c3e_l2_sum n)))).
      setoid_replace (1 / (Z.of_nat (2 * n + 2) # 1)
                      - (c3e_l2_sum k - c3e_l2_sum n)
                      - 1 / (Z.of_nat (2 * k + 2) # 1))
        with ((1 / (Z.of_nat (2 * n + 2) # 1)
               - 1 / (Z.of_nat (2 * k + 2) # 1))
              - (c3e_l2_sum k - c3e_l2_sum n)) by ring.
      exact (proj1 (Qle_minus_iff (c3e_l2_sum k - c3e_l2_sum n)
                                  (1 / (Z.of_nat (2 * n + 2) # 1)
                                   - 1 / (Z.of_nat (2 * k + 2) # 1)))
                   (QleT'_to_Qle _ _ (c3e_l2_inv k n Hnk))).
Qed.


(* ============================================================ *)
(* S2 continued: the Cauchy real of ln 2 (limit of the paired alternating
   harmonic series, built from scratch)                              *)
(* ============================================================ *)

(* The Cauchy real of ln 2 (limit of the paired alternating harmonic
   series). *)
Definition c3e_ln2_real : Real.
Proof.
  exists (c3e_l2_sum).
  intros eps Heps.
  destruct (q_arch_inv eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    (* m <= n: |s m - s n| = s n - s m <= 1/(2m+2) <= 1/(N+2) < eps. *)
    rewrite (qeqT_imp_qeq _ _ (sc_lp_abs_sym (c3e_l2_sum m) (c3e_l2_sum n))).
    assert (Hpos : Qle 0 (c3e_l2_sum n - c3e_l2_sum m)).
    { apply (proj1 (Qle_minus_iff (c3e_l2_sum m) (c3e_l2_sum n))).
      apply QleT'_to_Qle. apply c3e_l2_mono. exact E. }
    rewrite (Qabs_pos (c3e_l2_sum n - c3e_l2_sum m) Hpos).
    apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1))).
    + apply (Qle_trans _ (1 / (Z.of_nat (2 * m + 2) # 1))).
      * apply (Qle_trans _ (1 / (Z.of_nat (2 * m + 2) # 1)
                            - 1 / (Z.of_nat (2 * n + 2) # 1))).
        -- apply QleT'_to_Qle. exact (c3e_l2_inv n m E).
        -- apply QleT'_to_Qle. apply c3e_sub_le_self.
           apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * n + 2) # 1))).
           exact (QltT_to_Qlt _ _ (q_arch_inv_pos (2 * n))).
      * apply QleT'_to_Qle. apply c3e_inv_le_inv.
        assert (Hm' : (N <= m)%nat) by (apply (NatLe_drop _ _ Hm)).
        lia.
    + exact (QltT_to_Qlt _ _ HN).
  - apply Nat.leb_gt in E.
    assert (Hnm : (n <= m)%nat) by lia.
    assert (Hn' : (N <= n)%nat) by (apply (NatLe_drop _ _ Hn)).
    (* n < m: |s m - s n| = s m - s n <= 1/(2n+2) <= 1/(N+2) < eps. *)
    assert (Hpos : Qle 0 (c3e_l2_sum m - c3e_l2_sum n)).
    { apply (proj1 (Qle_minus_iff (c3e_l2_sum n) (c3e_l2_sum m))).
      apply QleT'_to_Qle. apply c3e_l2_mono. exact Hnm. }
    rewrite (Qabs_pos (c3e_l2_sum m - c3e_l2_sum n) Hpos).
    apply (Qle_lt_trans _ (1 / (Z.of_nat (N + 2) # 1))).
    + apply (Qle_trans _ (1 / (Z.of_nat (2 * n + 2) # 1))).
      * apply (Qle_trans _ (1 / (Z.of_nat (2 * n + 2) # 1)
                            - 1 / (Z.of_nat (2 * m + 2) # 1))).
        -- apply QleT'_to_Qle. exact (c3e_l2_inv m n Hnm).
        -- apply QleT'_to_Qle. apply c3e_sub_le_self.
           apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * m + 2) # 1))).
           exact (QltT_to_Qlt _ _ (q_arch_inv_pos (2 * m))).
      * apply QleT'_to_Qle. apply c3e_inv_le_inv. lia.
    + exact (QltT_to_Qlt _ _ HN).
Defined.

(* Projection of the ln 2 Cauchy real (definitional). *)
Lemma c3e_ln2_proj : forall k : nat, QeqT (projT1 c3e_ln2_real k) (c3e_l2_sum k).
Proof.
  intro k. apply qeq_imp_qeqT. exact (Qeq_refl (projT1 c3e_ln2_real k)).
Qed.

(* ln 2 envelope theorem: derived from the assembly theorem (the proof is
   literally the instance [c3e_env_mother ...], not a parallel copy). *)
Theorem c3e_env_ln2 : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) c3e_ln2_real)
        (And (real_le_b c3e_ln2_real (real_const hi))
             (QeqT (hi - lo) (2 * (1 / (Z.of_nat (2 * n + 2) # 1))))))).
Proof.
  intro n.
  exact (c3e_env_mother c3e_ln2_real (c3e_l2_sum n)
           (1 / (Z.of_nat (2 * n + 2) # 1)) n
           (fun k Hk => c3e_l2_cert n k Hk)).
Qed.

(* ============================================================ *)
(* S3. e component: lifted to the Real layer via the exp_tail_abs_geom2
   chain                                                              *)
(* ============================================================ *)

(* The e component: x := e^1 as a Cauchy real with s n := exp_partial n 1
   and t n := (1^n/n!) * 2 (exp_tail_abs_geom2 instantiated at A = 1;
   requires n >= 1).  Dependency chain: exp_tail_abs_le (|tail| <=
   tail_abs), then exp_tail_abs_geom2, then the Real-layer assembly
   theorem. *)
Theorem c3e_env_e : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) (cauchy_real_exp (real_const 1)))
        (And (real_le_b (cauchy_real_exp (real_const 1)) (real_const hi))
             (QeqT (hi - lo) (2 * ((q_pow 1 n / q_fact n) * (1 + 1)%Q)))))).
Proof.
  intros n Hn.
  apply (c3e_env_mother (cauchy_real_exp (real_const 1)) (exp_partial n 1)
                        ((q_pow 1 n / q_fact n) * (1 + 1)%Q) n).
  intros k Hk.
  assert (Hz : exp_partial k 1 - exp_partial n 1 == exp_tail n k 1)
    by (apply (qeqT_imp_qeq _ _ (exp_partial_diff_tail n k 1 Hk))).
  assert (Habs : Qle (Qabs (exp_tail n k 1))
                     ((q_pow 1 n / q_fact n) * (1 + 1)%Q)).
  { apply (Qle_trans _ (exp_tail_abs n k (Qabs 1))).
    - apply QleT'_to_Qle. apply exp_tail_abs_le.
    - apply (Qle_trans _ (exp_tail_abs n k 1)).
      + apply QleT'_to_Qle. apply qeq_le.
        apply (exp_tail_abs_wd n k (Qabs 1) 1). reflexivity.
      + apply QleT'_to_Qle. apply (exp_tail_abs_geom2 1 n k).
        * reflexivity.
        * intros t Ht.
          assert (Ht' : (n <= t)%nat) by (apply (NatLe_drop _ _ Ht)).
          apply Qle_to_QleT'. unfold Qle; simpl; lia.
        * exact Hk. }
  destruct (c3e_abs_two (exp_tail n k 1)
                        ((q_pow 1 n / q_fact n) * (1 + 1)%Q) Habs)
    as [Hzlo Hzhi].
  split.
  - (* exp_partial n 1 − t ≤ exp_partial k 1 ⟸ 0 ≤ z + t *)
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (exp_const_proj 1 k)).
    apply (proj2 (Qle_minus_iff (exp_partial n 1 - (q_pow 1 n / q_fact n) * (1 + 1)%Q)
                                (exp_partial k 1))).
    setoid_replace (exp_partial k 1
                    - (exp_partial n 1 - (q_pow 1 n / q_fact n) * (1 + 1)%Q))
      with (exp_tail n k 1 + (q_pow 1 n / q_fact n) * (1 + 1)%Q).
    + apply QleT'_to_Qle. exact Hzlo.
    + rewrite <- Hz. ring.
  - (* exp_partial k 1 ≤ exp_partial n 1 + t ⟸ 0 ≤ t − z *)
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (exp_const_proj 1 k)).
    apply (proj2 (Qle_minus_iff (exp_partial k 1)
                                (exp_partial n 1
                                 + (q_pow 1 n / q_fact n) * (1 + 1)%Q))).
    setoid_replace (exp_partial n 1 + (q_pow 1 n / q_fact n) * (1 + 1)%Q
                    - exp_partial k 1)
      with ((q_pow 1 n / q_fact n) * (1 + 1)%Q - exp_tail n k 1).
    + apply QleT'_to_Qle. exact Hzhi.
    + rewrite <- Hz. ring.
Qed.

(* ============================================================ *)
(* S4. pi component: lifted to the Real layer via the series tail bound
   sc_lp_odd_diff_bound                                               *)
(* ============================================================ *)

(* The pi component: x := pi_L = Cauchy(4 * lp_odd) with s n := 4 * lp_odd n
   (the pointwise projection of pi_L itself, by real_pi_leibniz_proj) and
   t n := 4 * lp_a(2n+2) = 4/(4n+5) (the series tail of
   sc_lp_odd_diff_bound, scaled by 4). *)
Theorem c3e_env_pi : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) cauchy_real_pi_leibniz)
        (And (real_le_b cauchy_real_pi_leibniz (real_const hi))
             (QeqT (hi - lo) (2 * (lp_four * lp_a (2 * n + 2))))))).
Proof.
  intro n.
  apply (c3e_env_mother cauchy_real_pi_leibniz (lp_four * lp_odd n)
                        (lp_four * lp_a (2 * n + 2)) n).
  intros k Hk.
  split.
  - (* 4·lp_odd n − 4·tail ≤ 4·lp_odd k *)
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (real_pi_leibniz_proj k)).
    apply (Qle_trans _ (lp_four * lp_odd n)).
    + apply (proj2 (Qle_minus_iff (lp_four * lp_odd n - lp_four * lp_a (2 * n + 2))
                                  (lp_four * lp_odd n))).
      setoid_replace (lp_four * lp_odd n
                      - (lp_four * lp_odd n - lp_four * lp_a (2 * n + 2)))
        with (lp_four * lp_a (2 * n + 2)) by ring.
      apply (Qle_trans _ (0 * lp_a (2 * n + 2))).
      * setoid_replace (0 * lp_a (2 * n + 2)) with 0 by ring. apply Qle_refl.
      * apply (Qmult_le_compat_r 0 lp_four (lp_a (2 * n + 2))).
        -- apply QleT'_to_Qle. apply sc_lp_four_nonneg.
        -- apply QleT'_to_Qle. apply sc_lpa_nonneg.
    + setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four) by ring.
      setoid_replace (lp_four * lp_odd k) with (lp_odd k * lp_four) by ring.
      apply (Qmult_le_compat_r (lp_odd n) (lp_odd k) lp_four).
      * apply QleT'_to_Qle. apply sc_lp_odd_chain. exact Hk.
      * apply QleT'_to_Qle. apply sc_lp_four_nonneg.
  - (* 4·lp_odd k ≤ 4·lp_odd n + 4·tail *)
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (real_pi_leibniz_proj k)).
    setoid_replace (lp_four * lp_odd k) with (lp_odd k * lp_four) by ring.
    setoid_replace (lp_four * lp_odd n + lp_four * lp_a (2 * n + 2))
      with ((lp_odd n + lp_a (2 * n + 2)) * lp_four) by ring.
    apply (Qmult_le_compat_r (lp_odd k) (lp_odd n + lp_a (2 * n + 2)) lp_four).
    + apply (proj2 (Qle_minus_iff (lp_odd k) (lp_odd n + lp_a (2 * n + 2)))).
      setoid_replace (lp_odd n + lp_a (2 * n + 2) - lp_odd k)
        with (lp_a (2 * n + 2) - (lp_odd k - lp_odd n)) by ring.
      exact (proj1 (Qle_minus_iff (lp_odd k - lp_odd n) (lp_a (2 * n + 2)))
                   (QleT'_to_Qle _ _ (sc_lp_odd_diff_bound n k Hk))).
    + apply QleT'_to_Qle. apply sc_lp_four_nonneg.
Qed.

(* ============================================================ *)
(* S5. Convergence rate: the linear modulus family N_c(eps) shape.     *)
(* ============================================================ *)

(* General rate: tail n <= c/(n+1) with c > 0 yields, for every eps > 0, a
   modulus N of the shape ceiling(c/eps) + 1 with 2 * tail n < eps for all
   n >= N (the witness N of q_arch_inv is the explicit ceiling
   construction). *)
Theorem c3e_env_rate : forall (tail : nat -> Q) (c : Q),
  Qlt 0 c ->
  (forall n : nat, Qle (2 * tail n) (c / (Z.of_nat (n + 1) # 1))) ->
  forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> QltT (2 * tail n) eps).
Proof.
  intros tail c Hc Hrate eps Heps.
  assert (Hec : Qlt 0 (eps / c)).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv c)).
    - exact Heps.
    - apply Qinv_lt_0_compat. exact Hc. }
  destruct (q_arch_inv (eps / c) (Qlt_to_QltT _ _ Hec)) as [N HN].
  exists (Datatypes.S N). intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (c / (Z.of_nat (N + 2) # 1))).
  - apply (Qle_trans _ (c / (Z.of_nat (n + 1) # 1))).
    + apply Hrate.
    + apply QleT'_to_Qle. apply (q_le_div_le c (Z.of_nat (n + 1) # 1) c (Z.of_nat (N + 2) # 1)).
      * apply Qlt_to_QltT. unfold Qlt; simpl; lia.
      * apply Qlt_to_QltT. unfold Qlt; simpl; lia.
      * apply Qle_to_QleT'. setoid_replace (c * (Z.of_nat (N + 2) # 1))
          with ((Z.of_nat (N + 2) # 1) * c) by ring.
        setoid_replace (c * (Z.of_nat (n + 1) # 1))
          with ((Z.of_nat (n + 1) # 1) * c) by ring.
        apply (Qmult_le_compat_r (Z.of_nat (N + 2) # 1) (Z.of_nat (n + 1) # 1) c).
        -- unfold Qle; simpl; lia.
        -- apply (Qlt_le_weak 0 c). exact Hc.
  - (* c/(N+2) < eps: 1/(N+2) < eps/c multiplied by c > 0 *)
    assert (Hw : c / (Z.of_nat (N + 2) # 1) == (1 / (Z.of_nat (N + 2) # 1)) * c).
    { field. intro Hz.
      apply (Qlt_not_eq 0 (Z.of_nat (N + 2) # 1)).
      - unfold Qlt; simpl; lia.
      - apply Qeq_sym. exact Hz. }
    assert (He : eps == (eps / c) * c).
    { field. intro Hz. apply (Qlt_not_eq 0 c Hc). exact (Qeq_sym _ _ Hz). }
    rewrite Hw. rewrite He.
    apply (Qmult_lt_compat_r (1 / (Z.of_nat (N + 2) # 1)) (eps / c) c Hc
                             (QltT_to_Qlt _ _ HN)).
Qed.

(* a * (1/X) == a / X (one Qdiv unfolding step). *)
Lemma c3e_mul_inv_div : forall (a X : Q), QeqT (a * (1 / X)) (a / X).
Proof.
  intros a X.
  apply qeq_imp_qeqT.
  unfold Qdiv. rewrite Qmult_1_l. reflexivity.
Qed.

(* ln 2 rate instance: the width 2 * tail n == 1/(n+1) shape (the linear
   family at c := 2; the injected bound 2 * (1/(2n+2)) <= 2/(n+1) is a
   direct consequence of q_le_div_le). *)
Theorem c3e_env_rate_ln2 : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    QltT (2 * (1 / (Z.of_nat (2 * n + 2) # 1))) eps).
Proof.
  intros eps Heps.
  apply (c3e_env_rate (fun v => 1 / (Z.of_nat (2 * v + 2) # 1)) 2).
  - unfold Qlt; simpl; lia.
  - intro n.
    setoid_replace (2 * (1 / (Z.of_nat (2 * n + 2) # 1)))
      with (2 / (Z.of_nat (2 * n + 2) # 1))
      by (apply qeqT_imp_qeq; apply c3e_mul_inv_div).
    apply QleT'_to_Qle. apply (q_le_div_le 2 (Z.of_nat (2 * n + 2) # 1) 2 (Z.of_nat (n + 1) # 1)).
    * apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    * apply Qlt_to_QltT. unfold Qlt; simpl; lia.
    * apply Qle_to_QleT'. setoid_replace (2 * (Z.of_nat (n + 1) # 1))
        with ((Z.of_nat (n + 1) # 1) * 2) by ring.
      setoid_replace (2 * (Z.of_nat (2 * n + 2) # 1))
        with ((Z.of_nat (2 * n + 2) # 1) * 2) by ring.
      apply (Qmult_le_compat_r (Z.of_nat (n + 1) # 1) (Z.of_nat (2 * n + 2) # 1) 2).
      -- unfold Qle; simpl; lia.
      -- unfold Qle; simpl; lia.
  - exact Heps.
Qed.

(* ============================================================ *)
(* Assumption audit                                                   *)
(* ============================================================ *)

Print Assumptions c3e_env_mother.
Print Assumptions c3e_env_ln2.
Print Assumptions c3e_env_e.
Print Assumptions c3e_env_pi.
Print Assumptions c3e_env_rate.
Print Assumptions c3e_env_rate_ln2.
