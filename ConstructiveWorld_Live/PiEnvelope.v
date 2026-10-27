(** * PiEnvelope: rational two-sided envelope for the Leibniz series of pi

    Mission. Two-sided rational bounds for the Leibniz series
    4·Σ_{k≥0} (−1)^k/(2k+1): every even partial sum times 4 is dominated by
    every odd partial sum times 4, with an explicit tail bound 4/(2m+1), an
    explicit Cauchy modulus N = S(ceil(4/eps)), the rational envelope
    [pi_rational_envelope] in [real_lt]/[sigT]/[And] form, and the numerical
    witnesses 3 < [cauchy_real_pi_leibniz] < 10/3.

    Dependencies. [S01_BaseRing] [S02_CauchyComplete] [S03_QExp]
    [S04_RealExpLogConv] [S05_AlignmentGRPO] [S06_DiffSamplingGibbs]
    [S07_RealSetoidExpLog] [S08_RealMainlineDPO] [S09_EntropyReal]
    [S10_KVQuantTrig] [S11_TP3B5] [S12_B5RecycleSF] [S13_NLiveAudit]
    [S14_B5BatchBlock] [S15_TailFEPUp]; Stdlib [QArith] [ZArith] [Arith]
    [Bool] [List] [Setoid] [Morphisms] [Lia].

    References. ConstructiveWorld-Main [PiEnvelope] (statement names carried
    over verbatim); template [LogTwoEnvelope] (four-stage scheme: terms,
    modulus order, pair identities, two-sided squeeze, tail bound).

    Constructivity. All named statements are Set-carried ([QltT], [QleT'],
    [QeqT], [Not], [sigT], [And]); extraction is free of [Obj.magic]; a
    [coqchk] run reports a closed global context.

    Build. rocq c -native-compiler no -q -Q . "" PiEnvelope.v
*)

(* ========================================================================= *)
(* Section 0. Exit carriers (Qlt_bool reflection, Id-of-bool)                *)
(* ========================================================================= *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> QltT x y.
Proof. intros x y H. exact H. Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  apply Qle_to_QleT'.
  apply (Qle_trans a b c H).
  apply (QleT'_to_Qle b c). apply qeq_le. apply qeq_imp_qeqT.
  exact Hbc.
Qed.

(* ========================================================================= *)
(* Section 1. Definitions                                                    *)
(* ========================================================================= *)

(* ---- term t_k := (−1)^k/(2k+1) (Leibniz term, without the factor 4) ---- *)
Definition pie_term (k : nat) : Q :=
  q_pow (-1) k / (Z.of_nat (2 * k + 1) # 1).

(* ---- partial sum S_n := Σ_{k<n} t_k (n terms) ---- *)
Fixpoint pie_partial (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => pie_partial m + pie_term m
  end.

(* ---- term modulus m_k := 1/(2k+1) (closed form of |t_k|) ---- *)
Definition pie_mag (k : nat) : Q := 1 / (Z.of_nat (2 * k + 1) # 1).

(* ---- one-step and two-step differences (subtraction forms) ---- *)
Lemma pie_gap1 : forall n : nat,
  QeqT (pie_partial (Datatypes.S n) - pie_partial n) (pie_term n).
Proof. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

Lemma pie_gap2 : forall n : nat,
  QeqT (pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n)
       (pie_term n + pie_term (Datatypes.S n)).
Proof. intro n. apply qeq_imp_qeqT. simpl. ring. Qed.

(* ---- addition form of the two-step difference (bridge use) ---- *)
Lemma pie_gap2_plus : forall n : nat,
  QeqT (pie_partial n + (pie_term n + pie_term (Datatypes.S n)))
       (pie_partial (Datatypes.S (Datatypes.S n))).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  pose proof (pie_gap2 n) as Hg.
  apply (Qeq_trans _ (pie_partial n
                      + (pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n)) _).
  - setoid_replace (pie_partial n + (pie_partial (Datatypes.S (Datatypes.S n)) - pie_partial n))
      with (pie_partial n + (pie_term n + pie_term (Datatypes.S n)))
      by (rewrite (qeqT_imp_qeq _ _ Hg); reflexivity).
    reflexivity.
  - ring.
Qed.

(* ---- 0 ≤ 4 ---- *)
Lemma pie_four_nonneg : QleT' 0 4.
Proof. apply Qle_to_QleT'. unfold Qle. simpl. lia. Qed.

(* ---- multiplication by 4 is monotone: x ≤ y implies 4x ≤ 4y ---- *)
Lemma pie_mult4_le : forall x y : Q, Qle x y -> QleT' (4 * x) (4 * y).
Proof.
  intros x y H.
  apply Qle_to_QleT'.
  setoid_replace (4 * x) with (x * 4) by ring.
  setoid_replace (4 * y) with (y * 4) by ring.
  apply (Qmult_le_compat_r x y 4).
  - exact H.
  - apply (QleT'_to_Qle _ _ pie_four_nonneg).
Qed.

(* ---- a positive rational is nonzero ---- *)
Lemma pie_neq_of_pos : forall z : Q, Qlt 0 z -> Not (QeqT z 0).
Proof. intros z Hz. apply q_neq_of_lt. apply Qlt_to_QltT. exact Hz. Qed.

(* ---- x/2 < x（x > 0） ---- *)
Lemma pie_q_half_lt : forall x : Q, Qlt 0 x -> QltT (x / 2) x.
Proof.
  intros x Hx.
  apply Qlt_to_QltT.
  assert (Hz2 : Qlt 0 (2 # 1)) by (unfold Qlt; simpl; lia).
  assert (Hi : Qlt 0 (/ (2 # 1))) by (apply Qinv_lt_0_compat; exact Hz2).
  assert (Hlt2 : Qlt x (x * 2)).
  { apply (proj2 (Qlt_minus_iff x (x * 2))).
    setoid_replace (x * 2 - x) with x by ring. exact Hx. }
  assert (Hmul : Qlt (x * / (2 # 1)) (x * 2 * / (2 # 1))).
  { apply (Qmult_lt_compat_r x (x * 2) (/ (2 # 1)) Hi Hlt2). }
  assert (Heq : x * 2 * / (2 # 1) == x).
  { field. }
  rewrite Heq in Hmul.
  unfold Qdiv. exact Hmul.
Qed.

(* ---- z + x < z + y（x < y） ---- *)
Lemma pie_qplus_lt_r : forall z x y : Q, Qlt x y -> QltT (z + x) (z + y).
Proof.
  intros z x y H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff (z + x) (z + y))).
  apply (proj1 (Qlt_minus_iff x y)) in H.
  setoid_replace ((z + y) - (z + x)) with (y - x) by ring.
  exact H.
Qed.

(* ========================================================================= *)
(* Section 2. Modulus order                                                  *)
(* ========================================================================= *)

Lemma pie_den_pos : forall k : nat, QltT 0 (Z.of_nat (2 * k + 1) # 1).
Proof. intro k. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

Lemma pie_den_neq : forall k : nat, Not (QeqT (Z.of_nat (2 * k + 1) # 1) 0).
Proof. intro k. apply q_neq_of_lt. exact (pie_den_pos k). Qed.

Lemma pie_mag_inv : forall k : nat,
  QeqT (pie_mag k) (/ (Z.of_nat (2 * k + 1) # 1)).
Proof. intro k. apply qeq_imp_qeqT. unfold pie_mag, Qdiv. apply Qmult_1_l. Qed.

Lemma pie_mag_pos : forall k : nat, QltT 0 (pie_mag k).
Proof.
  intro k.
  apply Qlt_to_QltT.
  setoid_replace (pie_mag k) with (/ (Z.of_nat (2 * k + 1) # 1))
    by (apply (qeqT_imp_qeq _ _ (pie_mag_inv k))).
  apply Qinv_lt_0_compat.
  exact (QltT_to_Qlt _ _ (pie_den_pos k)).
Qed.

Lemma pie_mag_nonneg : forall k : nat, QleT' 0 (pie_mag k).
Proof. intro k. apply Qle_to_QleT'. apply (Qlt_le_weak 0 (pie_mag k)).
  exact (QltT_to_Qlt _ _ (pie_mag_pos k)). Qed.

(* ---- paired-term monotonicity: 1/(2k+3) < 1/(2k+1) (support lemma 1) ---- *)
Lemma pie_mag_lt : forall k : nat, QltT (pie_mag (Datatypes.S k)) (pie_mag k).
Proof.
  intro k.
  apply Qlt_to_QltT.
  setoid_replace (pie_mag (Datatypes.S k))
    with (/ (Z.of_nat (2 * Datatypes.S k + 1) # 1))
    by (apply (qeqT_imp_qeq _ _ (pie_mag_inv (Datatypes.S k)))).
  setoid_replace (pie_mag k) with (/ (Z.of_nat (2 * k + 1) # 1))
    by (apply (qeqT_imp_qeq _ _ (pie_mag_inv k))).
  apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * k + 1) # 1)
                                  (Z.of_nat (2 * Datatypes.S k + 1) # 1)
                                  (QltT_to_Qlt _ _ (pie_den_pos k))
                                  (QltT_to_Qlt _ _ (pie_den_pos (Datatypes.S k))))).
  unfold Qlt. simpl. lia.
Qed.

Lemma pie_pair_diff_pos : forall k : nat,
  QltT 0 (pie_mag k - pie_mag (Datatypes.S k)).
Proof.
  intro k.
  apply Qlt_to_QltT.
  apply (proj1 (Qlt_minus_iff (pie_mag (Datatypes.S k)) (pie_mag k))).
  exact (QltT_to_Qlt _ _ (pie_mag_lt k)).
Qed.

(* ---- modulus antitone: a ≤ b implies m_b ≤ m_a ---- *)
Lemma pie_mag_antitone : forall a b : nat, (a <= b)%nat -> QleT' (pie_mag b) (pie_mag a).
Proof.
  intros a b Hab.
  apply Qle_to_QleT'.
  destruct (Nat.eq_dec a b) as [Heq | Hne].
  - subst b. apply Qle_refl.
  - assert (Hlt : (a < b)%nat) by lia.
    apply (Qle_trans _ (/ (Z.of_nat (2 * b + 1) # 1)) _).
    + apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
      exact (qeqT_imp_qeq _ _ (pie_mag_inv b)).
    + apply Qlt_le_weak.
      setoid_replace (pie_mag a) with (/ (Z.of_nat (2 * a + 1) # 1))
        by (apply (qeqT_imp_qeq _ _ (pie_mag_inv a))).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (2 * a + 1) # 1)
                                      (Z.of_nat (2 * b + 1) # 1)
                                      (QltT_to_Qlt _ _ (pie_den_pos a))
                                      (QltT_to_Qlt _ _ (pie_den_pos b)))).
      unfold Qlt. simpl. lia.
Qed.

Lemma pie_mag_decr : forall k : nat, QleT' (pie_mag (Datatypes.S k)) (pie_mag k).
Proof. intro k. apply pie_mag_antitone. lia. Qed.

Lemma pie_mag_decr_pos_step : forall n : nat,
  QleT' 0 (pie_mag n - pie_mag (Datatypes.S n)).
Proof.
  intro n.
  apply Qle_to_QleT'.
  apply (proj1 (Qle_minus_iff (pie_mag (Datatypes.S n)) (pie_mag n))).
  exact (QleT'_to_Qle _ _ (pie_mag_decr n)).
Qed.

(* ========================================================================= *)
(* Section 3. Term identities                                                *)
(* ========================================================================= *)

Lemma pie_term_abs : forall k : nat, QeqT (Qabs (pie_term k)) (pie_mag k).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  unfold pie_term, Qdiv.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite (qeqT_imp_qeq _ _ (sc_abs_sign k)).
  setoid_rewrite Qabs_Qinv.
  assert (Hd : Qabs (Z.of_nat (2 * k + 1) # 1) == (Z.of_nat (2 * k + 1) # 1)).
  { apply Qabs_pos. unfold Qle. simpl. lia. }
  setoid_rewrite Hd.
  unfold pie_mag, Qdiv.
  ring.
Qed.

Lemma pie_pair_factor : forall k : nat,
  QeqT (pie_term k + pie_term (Datatypes.S k))
       (q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k))).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  unfold pie_term, pie_mag, Qdiv.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) k)).
  ring.
Qed.

Lemma pie_pair_abs : forall k : nat,
  QeqT (Qabs (pie_term k + pie_term (Datatypes.S k)))
       (pie_mag k - pie_mag (Datatypes.S k)).
Proof.
  intro k.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k)))) _).
  - apply (Qabs_wd (pie_term k + pie_term (Datatypes.S k))
                   (q_pow (-1) k * (pie_mag k - pie_mag (Datatypes.S k)))).
    exact (qeqT_imp_qeq _ _ (pie_pair_factor k)).
  - setoid_rewrite Qabs_Qmult.
    setoid_rewrite (qeqT_imp_qeq _ _ (sc_abs_sign k)).
    assert (Hd : Qabs (pie_mag k - pie_mag (Datatypes.S k)) ==
                 pie_mag k - pie_mag (Datatypes.S k)).
    { apply Qabs_pos.
      apply (Qlt_le_weak 0 (pie_mag k - pie_mag (Datatypes.S k))).
      exact (QltT_to_Qlt _ _ (pie_pair_diff_pos k)). }
    setoid_rewrite Hd.
    ring.
Qed.

(* ========================================================================= *)
(* Section 4. Two-sided squeeze                                              *)
(* ========================================================================= *)

(* ---- boundary step: S_{2j} ≤ S_{2j+1} (difference t_{2j} = m_{2j} > 0) ---- *)
Lemma pie_boundary : forall j : nat,
  QleT' (pie_partial (2 * j)) (pie_partial (2 * j + 1)).
Proof.
  intro j.
  apply Qle_to_QleT'.
  assert (H1 : (2 * j + 1)%nat = Datatypes.S (2 * j)) by lia.
  rewrite H1.
  assert (Hpos : Qle 0 (pie_partial (Datatypes.S (2 * j)) - pie_partial (2 * j))).
  { rewrite (qeqT_imp_qeq _ _ (pie_gap1 (2 * j))).
    apply (Qle_trans _ (pie_mag (2 * j)) _).
    - apply (Qlt_le_weak 0 (pie_mag (2 * j))).
      exact (QltT_to_Qlt _ _ (pie_mag_pos (2 * j))).
    - apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
      unfold pie_term.
      rewrite (qeqT_imp_qeq _ _ (atan_sign_even j)).
      unfold pie_mag, Qdiv.
      ring. }
  apply (proj2 (Qle_minus_iff (pie_partial (2 * j))
                              (pie_partial (Datatypes.S (2 * j))))).
  exact Hpos.
Qed.

(* ---- reverse boundary step: S_{2j} ≤ S_{2j−1} (trivial truncation at j = 0) ---- *)
Lemma pie_boundary_rev : forall j : nat,
  QleT' (pie_partial (2 * j)) (pie_partial (2 * j - 1)).
Proof.
  intro j. apply Qle_to_QleT'. destruct j as [| j'].
  - apply Qle_refl.
  - replace (2 * Datatypes.S j')%nat with (2 * j' + 2)%nat by lia.
    replace (2 * j' + 2 - 1)%nat with (2 * j' + 1)%nat by lia.
    replace (2 * j' + 2)%nat with (Datatypes.S (2 * j' + 1)) by lia.
    assert (Hpos : Qle 0 (pie_partial (2 * j' + 1) -
                          pie_partial (Datatypes.S (2 * j' + 1)))).
    { assert (Hd : pie_partial (2 * j' + 1) -
                   pie_partial (Datatypes.S (2 * j' + 1)) ==
                   pie_mag (2 * j' + 1)).
      { apply (Qeq_trans _ (- (pie_term (2 * j' + 1))) _).
        - pose proof (pie_gap1 (2 * j' + 1)) as Hg.
          rewrite <- (qeqT_imp_qeq _ _ Hg). ring.
        - unfold pie_term.
          rewrite (qeqT_imp_qeq _ _ (atan_sign_odd j')).
          unfold pie_mag, Qdiv.
          ring. }
      rewrite Hd. apply (QleT'_to_Qle _ _). apply pie_mag_nonneg. }
  apply (proj2 (Qle_minus_iff (pie_partial (Datatypes.S (2 * j' + 1)))
                              (pie_partial (2 * j' + 1)))).
  exact Hpos.
Qed.

(* ---- even-pair identity (pure algebra): m_{2j}−m_{2j+1} == t_{2j}+t_{2j+1} ---- *)
Lemma pie_even_pair_factor : forall j : nat,
  QeqT (pie_mag (2 * j) - pie_mag (Datatypes.S (2 * j)))
       (pie_term (2 * j) + pie_term (Datatypes.S (2 * j))).
Proof.
  intro j.
  apply qeq_imp_qeqT.
  unfold pie_term, pie_mag, Qdiv.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (2 * j))).
  rewrite (qeqT_imp_qeq _ _ (atan_sign_even j)).
  ring.
Qed.

(* ---- even step: S_{2j} ≤ S_{2j+2} ---- *)
Lemma pie_even_step : forall j : nat,
  QleT' (pie_partial (2 * j)) (pie_partial (2 * j + 2)).
Proof.
  intro j.
  apply Qle_to_QleT'.
  assert (H2 : (2 * j + 2)%nat = Datatypes.S (Datatypes.S (2 * j))) by lia.
  rewrite H2.
  assert (Hpos : Qle 0 (pie_partial (Datatypes.S (Datatypes.S (2 * j))) -
                        pie_partial (2 * j))).
  { rewrite (qeqT_imp_qeq _ _ (pie_gap2 (2 * j))).
    apply (Qle_trans _ (pie_mag (2 * j) - pie_mag (Datatypes.S (2 * j))) _).
    - exact (QleT'_to_Qle _ _ (pie_mag_decr_pos_step (2 * j))).
    - apply (QleT'_to_Qle _ _). apply qeq_le.
      exact (pie_even_pair_factor j). }
  apply (proj2 (Qle_minus_iff (pie_partial (2 * j))
                              (pie_partial (Datatypes.S (Datatypes.S (2 * j)))))).
  exact Hpos.
Qed.

(* ---- odd step: S_{2j+3} ≤ S_{2j+1} ---- *)
Lemma pie_odd_step : forall j : nat,
  QleT' (pie_partial (2 * j + 3)) (pie_partial (2 * j + 1)).
Proof.
  intro j.
  apply Qle_to_QleT'.
  assert (H3 : (2 * j + 3)%nat = Datatypes.S (Datatypes.S (2 * j + 1))) by lia.
  rewrite H3.
  assert (Hpos : Qle 0 (pie_partial (2 * j + 1) -
                        pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))))).
  { assert (Hg : pie_partial (2 * j + 1) -
                 pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))) ==
                 pie_mag (2 * j + 1) - pie_mag (Datatypes.S (2 * j + 1))).
    { pose proof (pie_gap2 (2 * j + 1)) as Hfwd.
      assert (Hpf : pie_term (2 * j + 1) + pie_term (Datatypes.S (2 * j + 1)) ==
                    - (pie_mag (2 * j + 1) - pie_mag (Datatypes.S (2 * j + 1)))).
      { unfold pie_term, pie_mag, Qdiv.
        rewrite (qeqT_imp_qeq _ _ (q_pow_succ (-1) (2 * j + 1))).
        rewrite (qeqT_imp_qeq _ _ (atan_sign_odd j)).
        ring. }
      apply (Qeq_trans _ (- (pie_term (2 * j + 1) + pie_term (Datatypes.S (2 * j + 1)))) _).
      - rewrite <- (qeqT_imp_qeq _ _ (pie_gap2 (2 * j + 1))). ring.
      - rewrite Hpf. ring. }
    rewrite Hg.
    exact (QleT'_to_Qle _ _ (pie_mag_decr_pos_step (2 * j + 1))). }
  apply (proj2 (Qle_minus_iff (pie_partial (Datatypes.S (Datatypes.S (2 * j + 1))))
                              (pie_partial (2 * j + 1)))).
  exact Hpos.
Qed.

(* ---- even subsequence is monotone ---- *)
Lemma pie_even_mono : forall d j : nat,
  QleT' (pie_partial (2 * j)) (pie_partial (2 * (j + d))).
Proof.
  intros d j. induction d as [| d IH].
  - replace (2 * (j + 0))%nat with (2 * j)%nat by ring.
    apply Qle_to_QleT'. apply Qle_refl.
  - replace (2 * (j + Datatypes.S d))%nat with (2 * (j + d) + 2)%nat by lia.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (pie_partial (2 * (j + d))) _).
    + exact (QleT'_to_Qle _ _ IH).
    + exact (QleT'_to_Qle _ _ (pie_even_step (j + d))).
Qed.

(* ---- odd subsequence is non-increasing ---- *)
Lemma pie_odd_mono : forall d k : nat,
  QleT' (pie_partial (2 * (k + d) + 1)) (pie_partial (2 * k + 1)).
Proof.
  intros d k. induction d as [| d IH].
  - replace (2 * (k + 0) + 1)%nat with (2 * k + 1)%nat by ring.
    apply Qle_to_QleT'. apply Qle_refl.
  - replace (2 * (k + Datatypes.S d) + 1)%nat with (2 * (k + d) + 3)%nat by lia.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (pie_partial (2 * (k + d) + 1)) _).
    + exact (QleT'_to_Qle _ _ (pie_odd_step (k + d))).
    + exact (QleT'_to_Qle _ _ IH).
Qed.

(* ---- squeeze core: every even partial sum is ≤ every odd partial sum ---- *)
Lemma pie_even_le_odd : forall j k : nat,
  QleT' (pie_partial (2 * j)) (pie_partial (2 * k + 1)).
Proof.
  intros j k.
  apply Qle_to_QleT'.
  destruct (le_lt_dec j k) as [Hjk | Hkj].
  - replace (2 * k + 1)%nat with (2 * (j + (k - j)) + 1)%nat by lia.
    apply (Qle_trans _ (pie_partial (2 * (j + (k - j)))) _).
    + exact (QleT'_to_Qle _ _ (pie_even_mono (k - j) j)).
    + exact (QleT'_to_Qle _ _ (pie_boundary (j + (k - j)))).
  - apply (Qle_trans _ (pie_partial (2 * j - 1)) _).
    + exact (QleT'_to_Qle _ _ (pie_boundary_rev j)).
    + replace (2 * j - 1)%nat with (2 * (k + (j - k - 1)) + 1)%nat by lia.
      exact (QleT'_to_Qle _ _ (pie_odd_mono (j - k - 1) k)).
Qed.

(* ---- explicit gap width: S_{2m+1} − S_{2m} == 1/(4m+1) (support lemma 2) ---- *)
Lemma pie_parity_gap : forall m : nat,
  QeqT (pie_partial (2 * m + 1) - pie_partial (2 * m)) (pie_mag (2 * m)).
Proof.
  intro m.
  apply qeq_imp_qeqT.
  assert (H1 : (2 * m + 1)%nat = Datatypes.S (2 * m)) by lia.
  rewrite H1.
  rewrite (qeqT_imp_qeq _ _ (pie_gap1 (2 * m))).
  unfold pie_term.
  rewrite (qeqT_imp_qeq _ _ (atan_sign_even m)).
  unfold pie_mag, Qdiv.
  ring.
Qed.

(* ========================================================================= *)
(* Section 5. Tail bounds (Leibniz remainder)                                *)
(* ========================================================================= *)

Lemma pie_tail_bound : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (pie_partial n - pie_partial m)) (pie_mag m).
Proof.
  assert (Hgen : forall (d m n : nat), (m <= n)%nat -> (n - m)%nat = d ->
    Qle (Qabs (pie_partial n - pie_partial m)) (pie_mag m)).
  { induction d as [d IH] using lt_wf_ind.
    intros m n Hmn Hd.
    destruct (Nat.leb (Datatypes.S (Datatypes.S m)) n) eqn:E2.
    - (* m + 2 <= n: triangle split, paired term, induction *)
      apply Nat.leb_le in E2.
      apply (Qle_trans _ (Qabs ((pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                                (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m))) _).
      + apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
        apply (Qabs_wd (pie_partial n - pie_partial m)
                       ((pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                        (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m))).
        ring.
      + apply (Qle_trans _ (Qabs (pie_partial n - pie_partial (Datatypes.S (Datatypes.S m))) +
                            Qabs (pie_partial (Datatypes.S (Datatypes.S m)) - pie_partial m)) _).
        * apply Qabs_triangle.
        * apply (Qle_trans _ (pie_mag (Datatypes.S (Datatypes.S m)) +
                              (pie_mag m - pie_mag (Datatypes.S m))) _).
          -- apply Qplus_le_compat.
             ++ apply (IH (n - Datatypes.S (Datatypes.S m))%nat).
                ** lia.
                ** lia.
                ** reflexivity.
             ++ apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
                apply (Qeq_trans _ (Qabs (pie_term m + pie_term (Datatypes.S m))) _).
                ** apply (Qabs_wd (pie_partial (Datatypes.S (Datatypes.S m)) -
                                   pie_partial m)
                                  (pie_term m + pie_term (Datatypes.S m))).
                   exact (qeqT_imp_qeq _ _ (pie_gap2 m)).
                ** exact (qeqT_imp_qeq _ _ (pie_pair_abs m)).
          -- apply (Qle_trans _ (pie_mag (Datatypes.S m) +
                                 (pie_mag m - pie_mag (Datatypes.S m))) _).
             ++ apply Qplus_le_compat.
                ** exact (QleT'_to_Qle _ _ (pie_mag_decr (Datatypes.S m))).
                ** apply Qle_refl.
             ++ apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Nat.leb_gt in E2.
      destruct (Nat.eq_dec m n) as [Heq | Hne].
      + subst n.
        apply (Qle_trans _ 0 _).
        * apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
          apply (Qabs_wd (pie_partial m - pie_partial m) 0).
          ring.
        * apply (QleT'_to_Qle _ _). apply pie_mag_nonneg.
      + assert (Hn : n = Datatypes.S m) by lia.
        subst n.
        apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
        apply (Qeq_trans _ (Qabs (pie_term m)) _).
        * apply (Qabs_wd (pie_partial (Datatypes.S m) - pie_partial m) (pie_term m)).
          exact (qeqT_imp_qeq _ _ (pie_gap1 m)).
        * exact (qeqT_imp_qeq _ _ (pie_term_abs m)).
  }
  intros m n Hmn.
  apply Qle_to_QleT'.
  apply (Hgen (n - m)%nat m n Hmn). reflexivity.
Qed.

(* ---- tail bound times 4 (Q layer): m ≤ n implies |L_n − L_m| ≤ 4/(2m+1) ---- *)
Lemma pie_tail4 : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (4 * pie_partial n - 4 * pie_partial m)) (4 * pie_mag m).
Proof.
  intros m n Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (4 * Qabs (pie_partial n - pie_partial m)) _).
  - apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT.
    apply (Qeq_trans _ (Qabs (4 * (pie_partial n - pie_partial m))) _).
    + apply (Qabs_wd (4 * pie_partial n - 4 * pie_partial m)
                     (4 * (pie_partial n - pie_partial m))).
      ring.
    + apply (Qeq_trans _ (Qabs 4 * Qabs (pie_partial n - pie_partial m)) _).
      * apply Qabs_Qmult.
      * setoid_replace (Qabs 4) with 4
          by (apply Qabs_pos; apply (QleT'_to_Qle _ _ pie_four_nonneg)).
        reflexivity.
  - apply (QleT'_to_Qle _ _). apply pie_mult4_le.
    exact (QleT'_to_Qle _ _ (pie_tail_bound m n Hmn)).
Qed.

(* ========================================================================= *)
(* Section 6. Two-sided envelope theorem: L_n := 4·S_n, even L ≤ odd L       *)
(* ========================================================================= *)

Theorem pie_leibniz_two_sided : forall j k : nat,
  QleT' (4 * pie_partial (2 * j)) (4 * pie_partial (2 * k + 1)).
Proof.
  intros j k.
  apply pie_mult4_le.
  exact (QleT'_to_Qle _ _ (pie_even_le_odd j k)).
Qed.

(* ---- exit form: tail bound in QleT' ---- *)
Theorem pie_leibniz_tail : forall m n : nat, (m <= n)%nat ->
  QleT' (Qabs (4 * pie_partial n - 4 * pie_partial m)) (4 * pie_mag m).
Proof.
  intros m n Hmn.
  apply (qleT'_weaken _ (4 * pie_mag m) _).
  - exact (QleT'_to_Qle _ _ (pie_tail4 m n Hmn)).
  - reflexivity.
Qed.

(* ---- explicit gap width times 4: L_{2m+1} − L_{2m} == 4/(4m+1) ---- *)
Lemma pie_parity_gap4 : forall m : nat,
  QeqT (4 * pie_partial (2 * m + 1) - 4 * pie_partial (2 * m))
       (4 * pie_mag (2 * m)).
Proof.
  intro m.
  apply qeq_imp_qeqT.
  assert (Hgap := pie_parity_gap m).
  apply (Qeq_trans _ (4 * (pie_partial (2 * m + 1) - pie_partial (2 * m))) _).
  - ring.
  - rewrite (qeqT_imp_qeq _ _ Hgap). ring.
Qed.

(* ========================================================================= *)
(* Section 7. Cauchy modulus N := S(ceil(4/eps)) (explicit Qceiling)         *)
(* ========================================================================= *)

Definition pie_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling (4 / eps))).

Lemma pie_modulus_bound : forall eps : Q, Qlt 0 eps ->
  QltT (4 * pie_mag (pie_modulus eps)) eps.
Proof.
  intros eps Heps.
  apply Qlt_to_QltT.
  assert (Hx0 : Qlt 0 (4 / eps)).
  { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv eps)).
    - unfold Qlt; simpl; lia.
    - apply Qinv_lt_0_compat. exact Heps. }
  assert (Hcq : Qle 0 (Qceiling (4 / eps) # 1)).
  { apply (Qle_trans 0 (4 / eps) (Qceiling (4 / eps) # 1)).
    - apply (Qlt_le_weak 0 (4 / eps)). exact Hx0.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (4 / eps))%Z).
  { unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hstep : Qlt (4 / eps) ((Z.succ (Qceiling (4 / eps))) # 1)).
  { apply (Qle_lt_trans (4 / eps) (Qceiling (4 / eps) # 1)
                        ((Z.succ (Qceiling (4 / eps))) # 1)).
    - apply Qle_ceiling.
    - unfold Qlt, Qle. simpl. lia. }
  assert (Hz : (Z.succ (Qceiling (4 / eps)) = Z.of_nat (pie_modulus eps))%Z)
    by (unfold pie_modulus; lia).
  assert (Hmul : Qlt (4 / eps * eps) ((Z.of_nat (pie_modulus eps) # 1) * eps)).
  { apply (Qmult_lt_compat_r (4 / eps) (Z.of_nat (pie_modulus eps) # 1) eps Heps).
    rewrite <- Hz. exact Hstep. }
  setoid_replace (4 / eps * eps) with 4%Q in Hmul.
  2: { unfold Qdiv. field.
       intro Hzz. apply (Qlt_not_eq 0 eps Heps). exact (Qeq_sym _ _ Hzz). }
  assert (Hn1 : (1 <= pie_modulus eps)%nat) by (unfold pie_modulus; lia).
  assert (HzN1 : (0 < Z.of_nat (pie_modulus eps))%Z)
    by (unfold pie_modulus; lia).  (* Nat2Z.inj_lt is an iff and cannot be applied directly; lia proves the Z goal through zify. *)
  assert (Hzd1 : (0 < Z.of_nat (2 * pie_modulus eps + 1))%Z)
    by lia.  (* as above: Nat2Z.inj_lt is an iff, proved by lia via zify. *)
  assert (Hzlt : (Z.of_nat (pie_modulus eps) < Z.of_nat (2 * pie_modulus eps + 1))%Z)
    by (apply Nat2Z.inj_lt; lia).
  setoid_replace (pie_mag (pie_modulus eps))
    with (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
    by (apply (qeqT_imp_qeq _ _ (pie_mag_inv (pie_modulus eps)))).
  assert (Hinvlt : Qlt (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                       (/ (Z.of_nat (pie_modulus eps) # 1))).
  { apply (proj1 (Qinv_lt_contravar (Z.of_nat (pie_modulus eps) # 1)
                                    (Z.of_nat (2 * pie_modulus eps + 1) # 1)
                                    HzN1 Hzd1)).
    unfold Qlt. simpl. lia. }  (* Qlt(z#1,w#1) and Zlt(z,w) differ by one Qnum/Qden layer; lia bridges it. *)
  assert (Hstep1 : Qlt (4 * / (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                       (4 * / (Z.of_nat (pie_modulus eps) # 1))).
  { setoid_replace (4 * / (Z.of_nat (2 * pie_modulus eps + 1) # 1))
      with (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1) * 4) by ring.
    setoid_replace (4 * / (Z.of_nat (pie_modulus eps) # 1))
      with (/ (Z.of_nat (pie_modulus eps) # 1) * 4) by ring.
    apply (Qmult_lt_compat_r (/ (Z.of_nat (2 * pie_modulus eps + 1) # 1))
                             (/ (Z.of_nat (pie_modulus eps) # 1)) 4).
    - unfold Qlt; simpl; lia.
    - exact Hinvlt. }
  assert (Hfinv : Qlt 0 (/ (Z.of_nat (pie_modulus eps) # 1)))
    by (apply Qinv_lt_0_compat; unfold Qlt; simpl; lia).  (* the subgoal is a Qlt face and needs the Z unfolding bridge. *)
  assert (Hs2 : Qlt (4 * / (Z.of_nat (pie_modulus eps) # 1))
                    (((Z.of_nat (pie_modulus eps) # 1) * eps)
                     * / (Z.of_nat (pie_modulus eps) # 1))).  (* # and * bind at the same level, so the unparenthesized z#1*eps parses as z#(1*eps) in the positive slot. *)
  { apply (Qmult_lt_compat_r 4 ((Z.of_nat (pie_modulus eps) # 1) * eps)
                               (/ (Z.of_nat (pie_modulus eps) # 1)) Hfinv Hmul). }
  assert (Heq : ((Z.of_nat (pie_modulus eps) # 1) * eps)
                * / (Z.of_nat (pie_modulus eps) # 1) == eps).
  { field. intro Hzz.
    (* from Hzz alone, 0 == z#1 does not imply 0 == eps; derive the contradiction from Hmul : 4 < (z#1)*eps instead. *)
    rewrite Hzz in Hmul.
    assert (Hz00 : (0 * eps)%Q == 0) by ring.
    rewrite Hz00 in Hmul.
    unfold Qlt in Hmul. simpl in Hmul. discriminate. }
  rewrite Heq in Hs2.
  exact (Qlt_trans _ _ _ Hstep1 Hs2).
Qed.

(* ---- exit: sigT Cauchy modulus (N = S(ceil(4/eps)) explicit, extractable) ---- *)
Theorem pie_modulus_cauchy : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (4 * pie_partial n - 4 * pie_partial m)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT_to_Qlt 0 eps Heps)).
  exists (pie_modulus eps).
  intros m n HNm HNn.
  apply Qlt_to_QltT'.
  destruct (Nat.leb m n) eqn:E.
  - apply Nat.leb_le in E.
    apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus eps)) _).
    + apply (Qle_trans _ (4 * pie_mag m) _).
      * exact (QleT'_to_Qle _ _ (pie_tail4 m n E)).
      * rewrite (Qmult_comm 4 (pie_mag m)), (Qmult_comm 4 (pie_mag (pie_modulus eps))).
        apply Qmult_le_compat_r; [apply (QleT'_to_Qle _ _); apply pie_mag_antitone; apply NatLe_drop in HNm; exact HNm | unfold Qle; simpl; discriminate].
        (* Rocq 9.1 has no _l variant; commute to the right-multiplication form for _r. *)
    + exact (QltT_to_Qlt _ _ (pie_modulus_bound eps Hlt)).
  - apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus eps)) _).
    + apply (Qle_trans _ (4 * pie_mag n) _).
      * rewrite Qabs_Qminus. assert (Hnm : (n <= m)%nat) by lia.
        exact (QleT'_to_Qle _ _ (pie_tail4 n m Hnm)).
      * rewrite (Qmult_comm 4 (pie_mag n)), (Qmult_comm 4 (pie_mag (pie_modulus eps))).
        apply Qmult_le_compat_r; [apply (QleT'_to_Qle _ _); apply pie_mag_antitone; apply NatLe_drop in HNn; lia | unfold Qle; simpl; discriminate].
    + exact (QltT_to_Qlt _ _ (pie_modulus_bound eps Hlt)).
Qed.

(* ========================================================================= *)
(* Section 8. Real-layer bridge: lp_odd m == S_{2m+2} (even subsequence)     *)
(* ========================================================================= *)

(* ---- lp_pair (S m) == t_{2m+2} + t_{2m+3} (pair split) ---- *)
Lemma pie_pair_split : forall m : nat,
  QeqT (lp_pair (Datatypes.S m))
       (pie_term (2 * m + 2) + pie_term (Datatypes.S (2 * m + 2))).
Proof.
  intro m.
  apply qeq_imp_qeqT.
  assert (Hev : q_pow (-1) (2 * m + 2) == 1).
  { replace (2 * m + 2)%nat with (2 * (m + 1))%nat by lia.
    exact (qeqT_imp_qeq _ _ (atan_sign_even (m + 1))). }
  assert (Hod : q_pow (-1) (2 * m + 3) == -1).
  { replace (2 * m + 3)%nat with (2 * (m + 1) + 1)%nat by lia.
    exact (qeqT_imp_qeq _ _ (atan_sign_odd (m + 1))). }
  unfold lp_pair, lp_a, pie_term, Qdiv.
  replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat by lia.
  replace (2 * Datatypes.S m + 1)%nat with (2 * m + 3)%nat by lia.
  replace (Datatypes.S (2 * m + 2))%nat with (2 * m + 3)%nat by lia.
  replace (2 * m + 2 + 1)%nat with (2 * m + 3)%nat by lia.
  rewrite Hev, Hod. ring.
Qed.

(* ---- bridge core: lp_odd m == S_{2m+2} ---- *)
Lemma pie_lp_bridge : forall m : nat, QeqT (lp_odd m) (pie_partial (2 * m + 2)).
Proof.
  induction m as [| m IH].
  - apply qeq_imp_qeqT.
    unfold lp_odd, lp_pair, lp_a, pie_partial, pie_term, Qdiv.
    simpl. ring.
  - apply qeq_imp_qeqT.
    change (lp_odd (Datatypes.S m)) with (lp_odd m + lp_pair (Datatypes.S m)).
    rewrite (qeqT_imp_qeq _ _ IH).
    assert (Hidx : (2 * Datatypes.S m + 2)%nat = Datatypes.S (Datatypes.S (2 * m + 2)))
      by lia.
    rewrite Hidx.
    rewrite <- (qeqT_imp_qeq _ _ (pie_gap2_plus (2 * m + 2))).
    rewrite (qeqT_imp_qeq _ _ (pie_pair_split m)).
    ring.
Qed.

(* ---- bridge projection: v n == 4·S_{2n+2} ---- *)
Lemma pie_v_eq : forall n : nat,
  QeqT (lp_four * lp_odd n) (4 * pie_partial (2 * n + 2)).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (pie_lp_bridge n)).
  unfold lp_four. ring.
Qed.

(* ---- lower-wing generator: v n ≥ lo for n ≥ N, with lo ≤ 4·S_{2N+2} and slack c ---- *)
Lemma pie_real_lower_gen : forall (N : nat) (c lo : Q),
  Qlt 0 c -> Qle (lo + c) (4 * pie_partial (2 * N + 2)) ->
  real_lt (real_const lo) cauchy_real_pi_leibniz.
  (* The slack c in the premise is needed: for lo := 4·S_{2N+2} the premise
     without c holds while the conclusion would demand 1/2 < 0. The proof of
     Hlo uses lo + c <= 4·S_{2N+2}; the dual upper-wing generator
     [pie_real_upper_gen] carries the same slack, and every call site
     instantiates lo + c == v N. *)

Proof.
  intros N c lo Hc Hlo.
  unfold real_lt.
  exists (c / 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt in Hc; simpl in Hc. unfold Qlt. simpl. lia.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    simpl.
    apply Qlt_to_QltT.
    setoid_replace (lp_four * lp_odd n) with (4 * pie_partial (2 * n + 2))
      by (apply (qeqT_imp_qeq _ _ (pie_v_eq n))).
    setoid_replace (4 * pie_partial (2 * n + 2) - lo)
      with ((4 * pie_partial (2 * n + 2) - 4 * pie_partial (2 * N + 2))
            + (4 * pie_partial (2 * N + 2) - lo)) by ring.
    apply (Qlt_le_trans (c / 2) c _).
    + exact (QltT_to_Qlt _ _ (pie_q_half_lt c Hc)).
    + apply (Qle_trans c ((4 * pie_partial (2 * N + 2) - lo)
                           + (4 * pie_partial (2 * n + 2) - 4 * pie_partial (2 * N + 2))) _).
      * apply (Qle_trans c ((4 * pie_partial (2 * N + 2) - lo) + 0) _).
        -- apply (Qle_trans c (4 * pie_partial (2 * N + 2) - lo) _).
           ++ apply (proj2 (Qle_minus_iff c (4 * pie_partial (2 * N + 2) - lo))).
              setoid_replace (4 * pie_partial (2 * N + 2) - lo - c)
                with (4 * pie_partial (2 * N + 2) - (lo + c)) by ring.
              apply (proj1 (Qle_minus_iff (lo + c) (4 * pie_partial (2 * N + 2)))).
              exact Hlo.
           ++ apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * N + 2))
                                          (4 * pie_partial (2 * n + 2)))).
              apply (QleT'_to_Qle _ _). apply pie_mult4_le.
              replace (2 * N + 2)%nat with (2 * (N + 1))%nat by lia.
              replace (2 * n + 2)%nat with (2 * ((N + 1) + (n - N)))%nat by lia.
              exact (QleT'_to_Qle _ _ (pie_even_mono (n - N) (N + 1))).
      * apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ---- upper-wing generator: v n ≤ hi for n ≥ 0, with hi ≥ 4·S_{2N+1} + c ---- *)
Lemma pie_real_upper_gen : forall (N : nat) (c hi : Q),
  Qlt 0 c -> Qle (4 * pie_partial (2 * N + 1) + c) hi ->
  real_lt cauchy_real_pi_leibniz (real_const hi).
Proof.
  intros N c hi Hc Hhi.
  unfold real_lt.
  exists (c / 2).
  split.
  - apply Qlt_to_QltT. unfold Qlt in Hc; simpl in Hc. unfold Qlt. simpl. lia.
  - exists 0%nat. intros n Hn.
    simpl.
    apply Qlt_to_QltT.
    setoid_replace (lp_four * lp_odd n) with (4 * pie_partial (2 * n + 2))
      by (apply (qeqT_imp_qeq _ _ (pie_v_eq n))).
    setoid_replace (hi - 4 * pie_partial (2 * n + 2))
      with ((hi - 4 * pie_partial (2 * N + 1))
            + (4 * pie_partial (2 * N + 1) - 4 * pie_partial (2 * n + 2))) by ring.
    apply (Qlt_le_trans (c / 2) c _).
    + exact (QltT_to_Qlt _ _ (pie_q_half_lt c Hc)).
    + apply (Qle_trans c (c + 0) _).
      * apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply Qplus_le_compat.
        -- (* c ≤ hi − 4·S_{2N+1}, by rearranging Hhi *)
           apply (proj2 (Qle_minus_iff c (hi - 4 * pie_partial (2 * N + 1)))).
           apply (Qle_trans 0 (hi - (4 * pie_partial (2 * N + 1) + c)) _).
           ++ apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * N + 1) + c) hi)).
              exact Hhi.
           ++ apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
        -- (* 0 ≤ 4·S_{2N+1} − 4·S_{2n+2} (even ≤ odd) *)
           apply (proj1 (Qle_minus_iff (4 * pie_partial (2 * n + 2))
                                       (4 * pie_partial (2 * N + 1)))).
           replace (2 * n + 2)%nat with (2 * (n + 1))%nat by lia.
              apply (QleT'_to_Qle _ _). apply pie_mult4_le.
           exact (QleT'_to_Qle _ _ (pie_even_le_odd (n + 1) N)).
Qed.

(* ---- x/4 + x/4 == x/2 ---- *)
Lemma pie_q_add_halves : forall x : Q, QeqT (x / 4 + x / 4) (x / 2).
Proof.
  intro x. apply qeq_imp_qeqT. unfold Qdiv. field.
Qed.

(* ========================================================================= *)
(* Section 9. Rational envelope theorem (Real-layer)                         *)
(* ========================================================================= *)

Theorem pi_rational_envelope : forall eps : Q, QltT' 0 eps ->
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_lt (real_const lo) cauchy_real_pi_leibniz)
        (And (real_lt cauchy_real_pi_leibniz (real_const hi))
             (QltT' (hi - lo) eps)))).
Proof.
  intros eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply (QltT_to_Qlt 0 eps Heps)).
  assert (Hc4 : Qlt 0 (eps / 4)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (4 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hc2 : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (2 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hb : Qlt (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) (eps / 2)).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (eps / 2))) _).
    - apply (QleT'_to_Qle _ _). apply pie_mult4_le.
      apply (QleT'_to_Qle _ _). apply pie_mag_antitone. lia.
    - exact (QltT_to_Qlt _ _ (pie_modulus_bound (eps / 2) Hc2)). }
  exists (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4).
  exists (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4).
  split.
  - apply (pie_real_lower_gen (pie_modulus (eps / 2)) (eps / 4)
            (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4)).
    + exact Hc4.
    + apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
  - split.
    + apply (pie_real_upper_gen (pie_modulus (eps / 2)) (eps / 4)
              (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)).
      * exact Hc4.
      * apply Qle_refl.
    + apply Qlt_to_QltT'.
      replace (2 * pie_modulus (eps / 2) + 2)%nat
        with (Datatypes.S (2 * pie_modulus (eps / 2) + 1))%nat by lia.
      assert (Hgap : 4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                     - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     == 4 * pie_mag (2 * pie_modulus (eps / 2) + 1)).
      { assert (Hg := pie_gap1 (2 * pie_modulus (eps / 2) + 1)).
        assert (Hs : pie_term (2 * pie_modulus (eps / 2) + 1)
                     == - pie_mag (2 * pie_modulus (eps / 2) + 1)).
        { unfold pie_term, pie_mag, Qdiv.
          rewrite (qeqT_imp_qeq _ _ (atan_sign_odd (pie_modulus (eps / 2)))). ring. }
        setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                        - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
          with (- (4 * (pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     - pie_partial (2 * pie_modulus (eps / 2) + 1))))
          by ring.
        rewrite (qeqT_imp_qeq _ _ Hg). rewrite Hs. ring. }
      setoid_replace ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)
                      - (4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                         - eps / 4))
        with ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
               - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
              + (eps / 4 + eps / 4)) by ring.
      setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                      - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
        with (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) by exact Hgap.
      setoid_replace (eps / 4 + eps / 4) with (eps / 2)
        by apply (qeqT_imp_qeq _ _ (pie_q_add_halves eps)).
      apply (proj2 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)
                                   + eps / 2) eps)).
      setoid_replace (eps - (4 * pie_mag (2 * pie_modulus (eps / 2) + 1) + eps / 2))
        with ((eps - eps / 2) - 4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
        by ring.
      setoid_replace (eps - eps / 2) with (eps / 2)
        by (unfold Qdiv; field).
      apply (proj1 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
                                  (eps / 2))).
      exact Hb.
Qed.

(* ========================================================================= *)
(* Section 10. Numerical corollaries: 3 < π_L < 10/3 as envelope instances   *)
(* ========================================================================= *)

(* ---- rational-layer numerical witnesses (decidable by vm_compute) ---- *)
Lemma pie_sp8_over_three : QltT 0 (4 * pie_partial 8 - 3).
Proof. vm_compute. reflexivity. Qed.

Lemma pie_sp8_ge_three : QleT' 3 (4 * pie_partial 8).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma pie_sp9_under_ten3 : QltT 0 (10 / 3 - 4 * pie_partial 9).
Proof. vm_compute. reflexivity. Qed.

(* ---- 3 < π_L (lower wing, m = 3 instance) ---- *)
Theorem pie_real_three : real_lt (real_const 3) cauchy_real_pi_leibniz.
Proof.
  apply (pie_real_lower_gen 3 (4 * pie_partial 8 - 3) 3).
  - exact (QltT_to_Qlt _ _ pie_sp8_over_three).
  - replace (2 * 3 + 2)%nat with 8%nat by lia.
    apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ---- π_L < 10/3 (upper wing, m = 4 instance) ---- *)
Theorem pie_real_ten_thirds : real_lt cauchy_real_pi_leibniz (real_const (10 / 3)).
Proof.
  apply (pie_real_upper_gen 4 (10 / 3 - 4 * pie_partial 9) (10 / 3)).
  - exact (QltT_to_Qlt _ _ pie_sp9_under_ten3).
  - replace (2 * 4 + 1)%nat with 9%nat by lia.
    apply (QleT'_to_Qle _ _). apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ---- merged conjunction: 3 < π_L and π_L < 10/3 ---- *)
Theorem pie_const_bounds_merge :
  And (real_lt (real_const 3) cauchy_real_pi_leibniz)
      (real_lt cauchy_real_pi_leibniz (real_const (10 / 3))).
Proof.
  split.
  - exact pie_real_three.
  - exact pie_real_ten_thirds.
Qed.

(* ========================================================================= *)
(* Section 11. Assumption audit                                              *)
(* ========================================================================= *)

Print Assumptions pie_leibniz_two_sided.
Print Assumptions pie_leibniz_tail.
Print Assumptions pie_modulus_cauchy.
Print Assumptions pi_rational_envelope.
Print Assumptions pie_const_bounds_merge.
