(* ConstructiveWorld-Set -- tvd-layer geometric contraction toward the stationary distribution. *)

(** * abl_tvd_stationary: the tvd-layer stationary contraction chain.

    Mission.  Formalizes the tvd-layer contraction chain toward a stationary
      distribution: the Q-layer toolkit [tvs_qofnat_pos], [tvs_q_budget],
      [tvs_qsum_ge_abs], the geometric budgets [tvs_qgeom], [tvs_omd_pow_budget],
      [tvs_delta_budget], the half-factor-free tv seminorm [tvs_tv] with the
      doubling identity [tvs_doeblin_double], the contraction statement
      [tvs_tv_iter], the uniform base bound [tvs_tv_unif_bound], and the
      pointwise extractor [tvs_pt_of_tv_lt], the closed prefix of the
      coordinate-Cauchy route to the stationary object.

    Dependencies.  Stdlib [List], [Arith.Arith], [QArith.Qring], [QArith.Qabs], [Lia], [micromega.Lqa].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpGeomB], [UpRealLeB],
      [UpReqGeomD], [UpTVDoeblin] of this development.

    References.  This development, abl_tvd_stationary.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_tvd_stationary.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)

From Stdlib Require Import List Arith.Arith.
Import ListNotations.
From Stdlib Require Import QArith.Qring QArith.Qabs Lia micromega.Lqa.
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
Require Import UpTVDoeblin.
Require Import UpGeomB.

(* ################ Part 0: atomic Q-layer tools ################ *)

(* Q positivity of Z.of_nat type (Q.of_nat is absent in this project, so the *)
(* form (Z.of_nat n # 1) is used directly). *)
Lemma tvs_qofnat_pos : forall n : nat, (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof.
  intros [| m] H; [ lia | ].
  unfold Qlt. simpl. lia.
Qed.

(* Budget: 0 < e and 0 < eps give some Nb with 1 < (Z.of_nat Nb # 1)*(e*eps) *)
(* (taken directly from q_arch_inv). *)
Lemma tvs_q_budget : forall e eps : Q,
  Qlt 0 e -> Qlt 0 eps ->
  sigT (fun Nb : nat => Qlt 1 ((Z.of_nat Nb # 1) * (e * eps))).
Proof.
  intros e eps He Heps.
  assert (Hep : Qlt 0 (e * eps)).
  { destruct e as [a b]; destruct eps as [c d]; simpl in *.
    unfold Qlt in *; simpl in *.
    destruct (Qlt_le_dec 0 (a # b)) as [H1 | H1].
    - destruct (Qlt_le_dec 0 (c # d)) as [H2 | H2].
      + unfold Qlt. simpl. lia.
      + lia.
    - lia. }
  destruct (q_arch_inv (e * eps) (Qlt_to_QltT 0 (e * eps) Hep)) as [M HM].
  exists (M + 2)%nat.
  assert (HNbpos : Qlt 0 (Z.of_nat (M + 2) # 1))
    by (apply tvs_qofnat_pos; lia).
  assert (Hmul := Qmult_lt_compat_r (1 / (Z.of_nat (M + 2) # 1))
                     (e * eps) (Z.of_nat (M + 2) # 1) HNbpos
                     (QltT_to_Qlt (1 / (Z.of_nat (M + 2) # 1)) (e * eps) HM)).
  assert (Hone : Qeq ((1 / (Z.of_nat (M + 2) # 1))
                        * (Z.of_nat (M + 2) # 1)) (Qmake 1 1)).
  { field.
    intro Hc. apply (Qlt_not_eq 0 (Z.of_nat (M + 2) # 1) HNbpos).
    apply Qeq_sym. exact Hc. }
  setoid_rewrite Hone in Hmul.
  assert (Hsw : Qeq ((e * eps) * (Z.of_nat (M + 2) # 1))
                     ((Z.of_nat (M + 2) # 1) * (e * eps))) by ring.
  setoid_rewrite Hsw in Hmul. exact Hmul.
Qed.

(* Direct links to the Qabs library statements: |t| >= t and -t <= |t| *)
(* (bridges through Qle_Qabs / Qabs_opp). *)
Lemma tvs_qabs_ge : forall t : Q, Qle t (Qabs t).
Proof. intro t. exact (Qle_Qabs t). Qed.

Lemma tvs_qabs_ge_opp : forall t : Q, Qle (- t) (Qabs t).
Proof.
  intro t. apply (Qle_trans (- t) (Qabs (- t))).
  - exact (Qle_Qabs (- t)).
  - exact (QleT'_to_Qle (Qabs (- t)) (Qabs t)
             (qeq_le (Qabs (- t)) (Qabs t)
                (qeq_imp_qeqT (Qabs (- t)) (Qabs t) (Qabs_opp t)))).
Qed.

(* A Q-sum of pointwise nonnegative terms is nonnegative (the projection *)
(* form of real_list_sum). *)
Lemma tvs_qsum_nonneg : forall (X : Set) (f : X -> Real) (l : list X) (n : nat),
  (forall v : X, Qle 0 (projT1 (f v) n)) ->
  Qle 0 (projT1 (real_list_sum X f l) n).
Proof.
  intros X f l n. induction l as [| a rest IH]; intro H.
  - cbn [real_list_sum].
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz. apply Qle_refl.
  - cbn [real_list_sum].
    setoid_rewrite (qeqT_imp_qeq _ _
                     (real_plus_proj (f a) (real_list_sum X f rest) n)).
    apply (Qle_trans 0 (projT1 (f a) n)).
    + apply H.
    + apply (Qle_plus_nonneg_r (projT1 (f a) n)
               (projT1 (real_list_sum X f rest) n)
               (IH (fun v => H v))).
Qed.

(* For a member of the list, |d w|_n <= sum over v in l of |d v|_n *)
(* (pointwise at the Q layer, by induction on the InT witness). *)
Lemma tvs_qsum_ge_abs : forall (X : Set) (d : X -> Real) (w : X) (l : list X)
                                   (n : nat),
  InT w l ->
  Qle (projT1 (real_abs (d w)) n)
      (projT1 (real_list_sum X (fun v : X => real_abs (d v)) l) n).
Proof.
  intros X d w l n Hin.
  induction Hin as [l0 | y l0 Hin IH].
  - cbn [real_list_sum].
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs (d w))
               (real_list_sum X (fun v : X => real_abs (d v)) l0) n)).
    apply (Qle_plus_nonneg_r (projT1 (real_abs (d w)) n)
             (projT1 (real_list_sum X (fun v : X => real_abs (d v)) l0) n)).
    + apply (tvs_qsum_nonneg X (fun v : X => real_abs (d v)) l0 n).
      intro v. setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (d v) n)).
      apply Qabs_nonneg.
  - cbn [real_list_sum].
    setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_abs (d y))
               (real_list_sum X (fun v : X => real_abs (d v)) l0) n)).
    apply (Qle_trans _ (projT1 (real_list_sum X
                            (fun v : X => real_abs (d v)) l0) n)).
    + exact IH.
    + setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (d y) n)).
      apply (Qle_trans _ (projT1 (real_list_sum X
                            (fun v : X => real_abs (d v)) l0) n
                          + Qabs (projT1 (d y) n))).
      * apply (Qle_plus_nonneg_r (projT1 (real_list_sum X
                                  (fun v : X => real_abs (d v)) l0) n)
                   (Qabs (projT1 (d y) n))
                   (Qabs_nonneg (projT1 (d y) n))).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* ################ Part 2: rpow tools and the geometric budget (the Q-floor *)
(* ################ plus projection saturation route) #### *)

(* The Q projection bridge of real_one. *)
Lemma tvs_one_proj : forall k : nat, Qeq (projT1 real_one k) (Qmake 1 1).
Proof. intro k. unfold real_one.
  exact (qeqT_imp_qeq _ _ (real_const_proj (Qmake 1 1) k)). Qed.

(* The nat power at the Q layer (a transparent Fixpoint). *)
Fixpoint tvs_qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => (1 # 1)%Q
  | Datatypes.S m => q * tvs_qpow q m
  end.

(* The iterated sum carrier: X 0 := 1 and X (S m) := X m + d (the X term of *)
(* the Bernoulli bound; the projection of real_of_nat is opaque, so a *)
(* transparent iterated sum is built here). *)
Fixpoint tvs_xiter (d : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_plus (tvs_xiter d m) d
  end.

(* A Q-layer helper: w < y - z and 0 < w give z < y (decidable signs plus nia). *)
Lemma tvs_qlt_sub_r : forall w y z : Q,
  Qlt 0 w -> Qlt w (y - z) -> Qlt z y.
Proof.
  intros [w1 w2] [y1 y2] [z1 z2] H1 H2.
  unfold Qlt in *; unfold Qminus, Qplus, Qopp, Qinv in H2; simpl in *.
  destruct z1 as [| | z1']; simpl in *; destruct w1 as [| | w1']; simpl in *;
    try (destruct z2 as [| z2']; try (destruct w2 as [| w2'])); try nia.
Qed.

(* The three basic rpow statements. *)

(* rpow positivity: 0 < c gives 0 < c^n. *)
Lemma tvs_rpow_pos : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_lt real_zero (tv_rpow c n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [tv_rpow]. exact (real_mult_positive c (tv_rpow c m) Hc IH).
Qed.

(* rpow stays below 1: 0 < c <= 1 gives c^n <= 1. *)
Lemma tvs_rpow_le_one : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (n : nat),
  real_le (tv_rpow c n) real_one.
Proof.
  intros c Hc0 Hc1 n. induction n as [| m IH].
  - apply real_le_refl.
  - cbn [tv_rpow].
    apply (real_le_trans (real_mult c (tv_rpow c m))
             (real_mult real_one (tv_rpow c m)) real_one).
    + exact (real_le_mult_compat c real_one (tv_rpow c m)
               (tvs_rpow_pos c Hc0 m) Hc1).
    + apply (real_le_trans (real_mult real_one (tv_rpow c m)) (tv_rpow c m)).
      * apply (RealSetoid.real_eq_le _ _).
        exact (real_eq_trans (real_mult real_one (tv_rpow c m))
                 (real_mult (tv_rpow c m) real_one) (tv_rpow c m)
                 (real_mult_comm real_one (tv_rpow c m))
                 (real_mult_one (tv_rpow c m))).
      * exact IH.
Qed.

(* rpow is antitone in the exponent: n <= m gives c^m <= c^n. *)
Lemma tvs_rpow_anti_mono : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_le c real_one) (m n : nat),
  (n <= m)%nat -> real_le (tv_rpow c m) (tv_rpow c n).
Proof.
  intros c Hc0 Hc1 m. induction m as [| m' IH]; intros n Hle.
  - assert (Hn : n = 0%nat) by lia. subst. apply real_le_refl.
  - destruct n as [| n'].
    + change (tv_rpow c 0) with real_one.
      exact (tvs_rpow_le_one c Hc0 Hc1 (Datatypes.S m')).
    + assert (Hnm : (n' <= m')%nat) by lia.
      apply (RealSetoid.real_le_id_l (tv_rpow c (Datatypes.S m'))
               (real_mult c (tv_rpow c m')) (real_mult c (tv_rpow c n'))).
      -- exact (real_eq_refl (real_mult c (tv_rpow c m'))).
      -- exact (tvd_le_mult_compat_l c (tv_rpow c m') (tv_rpow c n')
                  Hc0 (IH n' Hnm)).
Qed.

(* Subtraction is antitone: e < d gives 1 - d < 1 - e (negation reverses, *)
(* then a two-step right translation). *)
Lemma tvs_lt_minus_antitone : forall (e d : Real),
  real_lt e d -> real_lt (real_minus_r real_one d) (real_minus_r real_one e).
Proof.
  intros e d Hed.
  assert (Hopp : real_lt (real_opp d) (real_opp e))
    by exact (real_opp_lt_compat e d Hed).
  apply (real_eq_lt_lt (real_minus_r real_one d)
           (real_plus real_one (real_opp d))
           (real_plus real_one (real_opp e))).
  - apply real_eq_of_zero_diff. intro n0.
    unfold real_minus_r. cbn [projT1].
    apply qeq_imp_qeqT.
    repeat first
      [ rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n0))
      | rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ _ n0))
      | rewrite (tvs_one_proj n0) ].
    ring.
  - apply (real_eq_lt_lt (real_plus real_one (real_opp d))
             (real_plus (real_opp d) real_one)
             (real_plus real_one (real_opp e))).
    + exact (real_plus_comm real_one (real_opp d)).
    + exact (real_lt_eq_lt (real_plus (real_opp d) real_one)
               (real_plus (real_opp e) real_one)
               (real_plus real_one (real_opp e))
               (real_lt_plus_compat_lt_le (real_opp d) (real_opp e)
                  real_one real_one Hopp (real_le_refl real_one))
               (real_plus_comm (real_opp e) real_one)).
Qed.

(* The zero budget: c ≈ 0 gives some N with c^n < eps for all n >= N. *)
Lemma tvs_geom_budget_zero : forall (c : Real) (Hc : real_eq c real_zero)
    (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow c n) (real_const eps)).
Proof.
  intros c Hc eps Heps. exists 1%nat. intros n Hn.
  destruct n as [| m]; [ exfalso; lia | ].
  cbn [tv_rpow].
  apply (real_eq_lt_lt (real_mult c (tv_rpow c m)) real_zero (real_const eps)).
  - exact (real_eq_trans (real_mult c (tv_rpow c m))
             (real_mult real_zero (tv_rpow c m)) real_zero
             (RealSetoid.real_eq_mult_compat c (tv_rpow c m) real_zero
                (tv_rpow c m) Hc (real_eq_refl (tv_rpow c m)))
             (real_eq_trans (real_mult real_zero (tv_rpow c m))
                (real_mult (tv_rpow c m) real_zero) real_zero
                (real_mult_comm real_zero (tv_rpow c m))
                (real_mult_zero (tv_rpow c m)))).
  - exact (real_const_lt 0 eps Heps).
Qed.

(* The three power statements at the Q layer. *)

(* Powers at the Q layer are nonnegative. *)
Lemma tvs_qpow_nonneg : forall (q : Q) (Hq : Qle 0 q) (n : nat),
  Qle 0 (tvs_qpow q n).
Proof.
  intros q Hq n. induction n as [| m IH].
  - cbn [tvs_qpow]. exact (QleT'_to_Qle _ _ Qle_0_1).
  - cbn [tvs_qpow]. apply Qmult_le_0_compat; [exact Hq | exact IH].
Qed.

(* Powers at the Q layer stay below 1: 0 <= q <= 1 gives q^n <= 1. *)
Lemma tvs_qpow_le_one : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qle q 1) (n : nat),
  Qle (tvs_qpow q n) (Qmake 1 1).
Proof.
  intros q Hq0 Hq1 n. induction n as [| m IH].
  - cbn [tvs_qpow]. apply Qle_refl.
  - cbn [tvs_qpow].
    apply (Qle_trans (q * tvs_qpow q m) (Qmake 1 1 * tvs_qpow q m)
             (Qmake 1 1)).
    + exact (Qmult_le_compat_r q (Qmake 1 1) (tvs_qpow q m) Hq1
               (tvs_qpow_nonneg q Hq0 m)).
    + apply (Qle_trans (Qmake 1 1 * tvs_qpow q m) (tvs_qpow q m)
               (Qmake 1 1)).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * exact IH.
Qed.

(* Powers at the Q layer are antitone in the exponent: 0 <= q <= 1 and n <= m *)
(* give q^m <= q^n (a closure premise of tvs_qgeom). *)
Lemma tvs_qpow_decr : forall (q : Q) (Hq0 : Qle 0 q) (Hq1 : Qle q 1)
    (m n : nat), (n <= m)%nat -> Qle (tvs_qpow q m) (tvs_qpow q n).
Proof.
  intros q Hq0 Hq1 m. induction m as [| m' IH]; intros n Hle.
  - assert (Hn : n = 0%nat) by lia. subst. apply Qle_refl.
  - destruct n as [| n'].
    + change (tvs_qpow q 0) with (Qmake 1 1).
      exact (tvs_qpow_le_one q Hq0 Hq1 (Datatypes.S m')).
    + assert (Hnm : (n' <= m')%nat) by lia.
      cbn [tvs_qpow].
      apply (Qle_trans (q * tvs_qpow q m') (tvs_qpow q m' * q)
               (q * tvs_qpow q n')).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans (tvs_qpow q m' * q) (tvs_qpow q n' * q)
                 (q * tvs_qpow q n')).
        -- exact (Qmult_le_compat_r (tvs_qpow q m') (tvs_qpow q n') q
                    (IH n' Hnm) Hq0).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* The Q Bernoulli bound: (1 + n*(1-q))*q^n <= 1 for 0 < q <= 1. *)
Lemma tvs_qbern : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qle q 1) (n : nat),
  Qle ((Qmake 1 1 + Qmake (Z.of_nat n) 1 * (1 - q)) * tvs_qpow q n) (Qmake 1 1).
Proof.
  intros q Hq0 Hq1 n.
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  induction n as [| m IH].
  - cbn [tvs_qpow]. simpl. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - cbn [tvs_qpow].
    assert (Hm0 : Qle 0 (Qmake (Z.of_nat m) 1)) by (unfold Qle; simpl; lia).
    assert (Hmq : Qle 0 (Qmake (Z.of_nat m) 1 * (1 - q)))
      by (apply Qmult_le_0_compat;
            [ exact Hm0
            | exact (proj1 (Qle_minus_iff q (Qmake 1 1)) Hq1) ]).
    assert (HA0 : Qle 0 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
    { apply (Qle_trans 0 (Qmake 1 1)
               (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
      - exact (QleT'_to_Qle _ _ Qle_0_1).
      - apply (Qle_trans (Qmake 1 1) (Qmake 1 1 + 0%Q)
                 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
        + exact (Qplus_le_compat (Qmake 1 1) (Qmake 1 1) 0%Q
                   (Qmake (Z.of_nat m) 1 * (1 - q))
                   (Qle_refl (Qmake 1 1)) Hmq). }
    assert (H1A : Qle (Qmake 1 1)
                    (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
      by exact (Qplus_le_compat (Qmake 1 1) (Qmake 1 1) 0%Q
                  (Qmake (Z.of_nat m) 1 * (1 - q))
                  (Qle_refl (Qmake 1 1)) Hmq).
    assert (Hstep : Qle ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                           * tvs_qpow q m * q)
                        (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
    { apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                          * tvs_qpow q m * q)
              (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
              (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
      - apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                            * tvs_qpow q m * q)
                 ((Qmake 1 1) * q)
                 (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))).
        + exact (Qmult_le_compat_r
                   ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))
                      * tvs_qpow q m)
                   (Qmake 1 1) q IH Hq0le).
        + apply (Qle_trans ((Qmake 1 1) * q)
                   ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) * q)
                   (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))).
          * exact (Qmult_le_compat_r (Qmake 1 1)
                     (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) q H1A Hq0le).
          * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply (Qle_trans (q * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
                 ((Qmake 1 1) * (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)))
                 (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q))).
        + exact (Qmult_le_compat_r q (Qmake 1 1)
                   (Qmake 1 1 + Qmake (Z.of_nat m) 1 * (1 - q)) Hq1 HA0).
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    destruct (Z.eq_dec (Z.of_nat (Datatypes.S m)) (Z.add 1 (Z.of_nat m)))
      as [Hz | Hzn]; [| lia].
    rewrite Hz.
    assert (Hx1 : Qle (q * tvs_qpow q m) (Qmake 1 1))
      by exact (tvs_qpow_le_one q Hq0le Hq1 (Datatypes.S m)).
    assert (H1mq : Qle 0 (Qminus (Qmake 1 1) q))
      by exact (proj1 (Qle_minus_iff q (Qmake 1 1)) Hq1).
    assert (Hbase : forall a b : Z, a = b -> Qeq (Qmake a 1) (Qmake b 1)).
    { intros a b Hab. cbv [Qeq Qnum Qden]. cbn.
      rewrite Hab. reflexivity. }
    assert (Hqadd : Qeq (Qmake (Z.add 1 (Z.of_nat m)) 1)
                        (Qplus (Qmake 1 1) (Qmake (Z.of_nat m) 1))).
    { change (Qeq (Qmake (Z.add 1 (Z.of_nat m)) 1)
                  (Qmake (1 * 1 + Z.of_nat m * 1) (1 * 1))).
      apply Hbase. ring. }
    apply (Qle_trans ((1 + Qmake (Z.add 1 (Z.of_nat m)) 1
                         * (Qminus (Qmake 1 1) q))
                        * (q * tvs_qpow q m))
            ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (Qminus (Qmake 1 1) q))
               * (q * tvs_qpow q m)
               + (Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
            (Qmake 1 1)).
    + rewrite Hqadd. apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (Qmake 1 1 * q + Qminus (Qmake 1 1) q)).
      * apply (Qplus_le_compat
                  ((Qmake 1 1 + Qmake (Z.of_nat m) 1 * (Qminus (Qmake 1 1) q))
                     * (q * tvs_qpow q m))
                  (Qmake 1 1 * q)
                  ((Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
                  (Qminus (Qmake 1 1) q)).
        -- apply (Qle_trans ((Qmake 1 1 + Qmake (Z.of_nat m) 1
                               * (Qminus (Qmake 1 1) q))
                               * (q * tvs_qpow q m))
                   (((Qmake 1 1 + Qmake (Z.of_nat m) 1
                        * (Qminus (Qmake 1 1) q))
                       * tvs_qpow q m) * q)
                   (Qmake 1 1 * q)).
          ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          ++ exact (Qmult_le_compat_r
                      ((Qmake 1 1 + Qmake (Z.of_nat m) 1
                          * (Qminus (Qmake 1 1) q))
                         * tvs_qpow q m)
                      (Qmake 1 1) q IH Hq0le).
        -- apply (Qle_trans ((Qminus (Qmake 1 1) q) * (q * tvs_qpow q m))
                   ((q * tvs_qpow q m) * (Qminus (Qmake 1 1) q))
                   (Qminus (Qmake 1 1) q)).
          ++ apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
          ++ apply (Qle_trans ((q * tvs_qpow q m) * (Qminus (Qmake 1 1) q))
                     ((Qmake 1 1) * (Qminus (Qmake 1 1) q))
                     (Qminus (Qmake 1 1) q)).
            ** exact (Qmult_le_compat_r (q * tvs_qpow q m) (Qmake 1 1)
                       (Qminus (Qmake 1 1) q) Hx1 H1mq).
            ** apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* Geometric cancellation at the Q layer: 0 < m and a*m < b*m give a < b. *)
Lemma tvs_qmult_lt_cancel_r : forall a b m : Q,
  Qlt 0 m -> Qlt (a * m) (b * m) -> Qlt a b.
Proof.
  intros a b m Hm H.
  assert (H2 := Qmult_lt_compat_r (a * m)%Q (b * m)%Q (Qinv m)
                   (Qinv_lt_0_compat m Hm) H).
  assert (Ha : Qeq ((a * m) * Qinv m) a).
  { field. intro Hc. apply (Qlt_not_eq 0 m Hm). symmetry. exact Hc. }
  assert (Hb : Qeq ((b * m) * Qinv m) b).
  { field. intro Hc. apply (Qlt_not_eq 0 m Hm). symmetry. exact Hc. }
  setoid_rewrite Ha in H2. setoid_rewrite Hb in H2. exact H2.
Qed.

(* The geometric budget at the Q layer: 0 < q < 1 gives some N with *)
(* q^n < eps for all n >= N. *)
Lemma tvs_qgeom : forall (q : Q) (Hq0 : Qlt 0 q) (Hq1 : Qlt q 1) (eps : Q)
    (Heps : Qlt 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (tvs_qpow q n) eps).
Proof.
  intros q Hq0 Hq1 eps Heps.
  assert (Hq0le : Qle 0 q) by (apply (Qlt_le_weak 0 q); exact Hq0).
  assert (Hq1le : Qle q 1) by (apply (Qlt_le_weak q 1); exact Hq1).
  assert (Hone : Qlt 0 (1 - q)%Q) by exact (proj1 (Qlt_minus_iff q (Qmake 1 1)) Hq1).
  assert (Hep : Qlt 0 ((1 - q)%Q * eps)) by (apply Qmult_lt_0_compat; assumption).
  destruct (q_arch_inv ((1 - q)%Q * eps)
             (Qlt_to_QltT 0 ((1 - q)%Q * eps) Hep)) as [M HM].
  assert (HNbpos : Qlt 0 (Z.of_nat (M + 2) # 1)) by (apply tvs_qofnat_pos; lia).
  assert (Hmul := Qmult_lt_compat_r (1 / (Z.of_nat (M + 2) # 1))
                     ((1 - q)%Q * eps) (Z.of_nat (M + 2) # 1) HNbpos
                     (QltT_to_Qlt (1 / (Z.of_nat (M + 2) # 1)) ((1 - q)%Q * eps) HM)).
  assert (Hinv : Qeq ((1 / (Z.of_nat (M + 2) # 1))
                        * (Z.of_nat (M + 2) # 1)) (Qmake 1 1)).
  { field.
    intro Hc. apply (Qlt_not_eq 0 (Z.of_nat (M + 2) # 1) HNbpos).
    apply Qeq_sym. exact Hc. }
  setoid_rewrite Hinv in Hmul.
  (* 1 < ((1-q)*eps)*Nb; reorder into (Nb*(1-q))*eps. *)
  assert (Hsw1 : Qeq ((1 - q)%Q * eps * (Z.of_nat (M + 2) # 1))
                     ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps)) by ring.
  setoid_rewrite Hsw1 in Hmul.
  exists (M + 2)%nat. intros n Hn.
  assert (Hb := tvs_qbern q Hq0 Hq1le n).
  assert (Hkey : Qle ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                     (Qmake 1 1)).
  { assert (HX : Qle ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                     (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    { apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
               (0%Q + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
               (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - exact (Qplus_le_compat 0%Q (Qmake 1 1)
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 (QleT'_to_Qle _ _ Qle_0_1)
                 (Qle_refl ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))). }
    assert (HX0 : Qle 0 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
      by (apply Qmult_le_0_compat;
            [ apply (Qlt_le_weak 0 (Z.of_nat (M + 2) # 1)); exact HNbpos
            | apply (Qlt_le_weak 0 (1 - q)%Q); exact Hone ]).
    assert (Hdec2 : Qle (tvs_qpow q n) (tvs_qpow q (M + 2)))
      by exact (tvs_qpow_decr q Hq0le Hq1le n (M + 2) Hn).
    apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
             ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))
             (Qmake 1 1)).
    - apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
               (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
               ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                 (tvs_qpow q (M + 2) * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                 ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q (M + 2))).
        * exact (Qmult_le_compat_r (tvs_qpow q n) (tvs_qpow q (M + 2))
                   ((Z.of_nat (M + 2) # 1) * (1 - q)%Q) Hdec2 HX0).
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qle_trans ((Z.of_nat (M + 2) # 1) * (1 - q)%Q
                          * tvs_qpow q (M + 2))
               ((Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                  * tvs_qpow q (M + 2))
               (Qmake 1 1)).
      + exact (Qmult_le_compat_r ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 (Qmake 1 1 + (Z.of_nat (M + 2) # 1) * (1 - q)%Q)
                 (tvs_qpow q (M + 2)) HX (tvs_qpow_nonneg q Hq0le (M + 2))).
      + exact (tvs_qbern q Hq0 Hq1le (M + 2)). }
  assert (HXlt : Qlt ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                     ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps))
    by exact (Qle_lt_trans
                ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * tvs_qpow q n)
                (Qmake 1 1)
                ((Z.of_nat (M + 2) # 1) * (1 - q)%Q * eps)
                Hkey Hmul).
  assert (HXlt2 : Qlt (tvs_qpow q n * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))
                      (eps * ((Z.of_nat (M + 2) # 1) * (1 - q)%Q))).
  { setoid_rewrite (Qmult_comm (tvs_qpow q n)
                      ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    setoid_rewrite (Qmult_comm eps
                      ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
    exact HXlt. }
  apply (tvs_qmult_lt_cancel_r (tvs_qpow q n) eps
           ((Z.of_nat (M + 2) # 1) * (1 - q)%Q)).
  - apply (Qmult_lt_0_compat (Z.of_nat (M + 2) # 1) (1 - q)%Q).
    + apply tvs_qofnat_pos. lia.
    + exact Hone.
  - exact HXlt2.
Qed.

(* ################ Part 3: the Q projection-saturation engine (power *)
(* ################ monotonicity, projection bridges, the Real geometric budget) #### *)

(* Powers preserve order on the left factor: 0 <= a <= b gives a^n <= b^n. *)
Lemma tvs_qpow_mono : forall (a b : Q) (Hab : Qle a b) (Ha0 : Qle 0 a)
    (n : nat), Qle (tvs_qpow a n) (tvs_qpow b n).
Proof.
  intros a b Hab Ha0 n.
  assert (Hb0 : Qle 0 b) by (apply (Qle_trans 0 a b); [ exact Ha0 | exact Hab ]).
  induction n as [| m IH].
  - cbn [tvs_qpow]. apply Qle_refl.
  - cbn [tvs_qpow].
    apply (Qle_trans (a * tvs_qpow a m) (b * tvs_qpow a m)
             (b * tvs_qpow b m)).
    + exact (Qmult_le_compat_r a b (tvs_qpow a m) Hab (tvs_qpow_nonneg a Ha0 m)).
    + apply (Qle_trans (b * tvs_qpow a m) (tvs_qpow a m * b)
               (b * tvs_qpow b m)).
      * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans (tvs_qpow a m * b) (tvs_qpow b m * b)
                 (b * tvs_qpow b m)).
        -- exact (Qmult_le_compat_r (tvs_qpow a m) (tvs_qpow b m) b IH Hb0).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

(* The Q projection of tv_rpow: projT1 (tv_rpow c n) k == tvs_qpow (projT1 c k) n. *)
Lemma tvs_qpow_proj : forall (c : Real) (k n : nat),
  Qeq (projT1 (tv_rpow c n) k) (tvs_qpow (projT1 c k) n).
Proof.
  intros c k n. induction n as [| m IH].
  - exact (tvs_one_proj k).
  - cbn [tv_rpow]. rewrite (qeqT_imp_qeq _ _ (real_mult_proj c (tv_rpow c m) k)).
    cbn [tvs_qpow]. setoid_rewrite IH. apply Qeq_refl.
Qed.

(* ################ Part 3.5: continuation (small Q helpers, budget closure, *)
(* ################ dispatch) #### *)

(* Small Q helper, one: 0 < w gives 1 - w < 1 (Qlt_minus_iff backwards plus *)
(* a ring equivalence). *)
Lemma tvs_qlt_one_minus_r : forall w : Q,
  Qlt 0 w -> Qlt (Qminus (Qmake 1 1) w) (Qmake 1 1).
Proof.
  intros w Hw.
  apply (proj2 (Qlt_minus_iff (Qminus (Qmake 1 1) w) (Qmake 1 1))).
  assert (Hr : Qeq (Qminus (Qmake 1 1) (Qminus (Qmake 1 1) w)) w) by ring.
  rewrite Hr. exact Hw.
Qed.

(* Small Q helper, two: 0 < b and b < c - a give a < c - b (the same *)
(* difference turned around twice). *)
Lemma tvs_qlt_swap_sub : forall a b c : Q,
  Qlt 0 b -> Qlt b (Qminus c a) -> Qlt a (Qminus c b).
Proof.
  intros a b c H1 H2.
  apply (proj2 (Qlt_minus_iff a (Qminus c b))).
  assert (Hr : Qeq (Qminus (Qminus c b) a) (Qminus (Qminus c a) b)) by ring.
  rewrite Hr.
  exact (proj1 (Qlt_minus_iff b (Qminus c a)) H2).
Qed.

(* Small Q helper, three: 2t == e and p < t give t < e - p (the gap *)
(* statement). *)
Lemma tvs_qlt_gap : forall e p t : Q,
  Qeq (Qplus t t) e -> Qlt p t -> Qlt t (Qminus e p).
Proof.
  intros e p t H0 H1.
  apply (proj2 (Qlt_minus_iff t (Qminus e p))).
  rewrite <- H0.
  assert (Hr : Qeq (Qminus (Qminus (Qplus t t) p) t) (Qminus t p)) by ring.
  rewrite Hr.
  exact (proj1 (Qlt_minus_iff p t) H1).
Qed.

(* The left/right projections of max under NatLe (the bound position of *)
(* real_lt is a NatLe form, as recorded in the compiled interface). *)
Lemma tvs_natle_max_l : forall a b k : nat, NatLe (Nat.max a b) k -> NatLe a k.
Proof.
  intros a b k H. apply NatLe_lift.
  apply (Nat.le_trans a (Nat.max a b) k (Nat.le_max_l a b)
           (NatLe_drop (Nat.max a b) k H)).
Qed.

Lemma tvs_natle_max_r : forall a b k : nat, NatLe (Nat.max a b) k -> NatLe b k.
Proof.
  intros a b k H. apply NatLe_lift.
  apply (Nat.le_trans b (Nat.max a b) k (Nat.le_max_r a b)
           (NatLe_drop (Nat.max a b) k H)).
Qed.

(* Small Q helper, four: 0 < eps gives 0 < eps/2 (via Qlt_shift_div_l, the *)
(* same shape as the original L299). *)
Lemma tvs_qlt_half_posT : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 2)%Q.
Proof.
  intro eps. intro Heps.
  apply Qlt_to_QltT. apply Qlt_shift_div_l; [reflexivity | ].
  simpl. apply QltT_to_Qlt. exact Heps.
Qed.

Lemma tvs_qlt_half_pos : forall eps : Q, QltT 0 eps -> Qlt 0 (eps / 2)%Q.
Proof.
  intros eps Heps. apply QltT_to_Qlt. exact (tvs_qlt_half_posT eps Heps).
Qed.

(* The Real geometric budget (the missing pieces completed to closure: the *)
(* two-sided projections pinch out q := 1 - w1 in (0,1), and the Q *)
(* projection-saturation route closes). *)
Lemma tvs_omd_pow_budget : forall (c : Real) (Hc0 : real_lt real_zero c)
    (Hc1 : real_lt c real_one) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow c n) (real_const eps)).
Proof.
  intros c Hc0 Hc1 eps Heps.
  destruct Hc0 as [w0 [Hw0 [N0 HN0]]].
  destruct Hc1 as [w1 [Hw1 [N1 HN1]]].
  assert (Hw0q : Qlt 0 w0) by (apply QltT_to_Qlt; exact Hw0).
  assert (Hw1q : Qlt 0 w1) by (apply QltT_to_Qlt; exact Hw1).
  assert (Hq1 : Qlt (Qminus (Qmake 1 1) w1) (Qmake 1 1))
    by exact (tvs_qlt_one_minus_r w1 Hw1q).
  set (k0 := Nat.max N0 N1).
  assert (Hk0 : QltT w0 (projT1 c k0 - projT1 real_zero k0))
    by (apply HN0; apply NatLe_lift; apply Nat.le_max_l).
  assert (Hk1 : QltT w1 (projT1 real_one k0 - projT1 c k0))
    by (apply HN1; apply NatLe_lift; apply Nat.le_max_r).
  assert (Hck0 : Qlt 0 (projT1 c k0))
    by (apply (tvs_qlt_sub_r w0 (projT1 c k0) (projT1 real_zero k0) Hw0q);
        apply QltT_to_Qlt; exact Hk0).
  assert (Hck1 : Qlt w1 (Qminus (Qmake 1 1) (projT1 c k0)))
    by exact (QltT_to_Qlt w1 (Qminus (Qmake 1 1) (projT1 c k0)) Hk1).
  assert (Hckq : Qlt (projT1 c k0) (Qminus (Qmake 1 1) w1))
    by exact (tvs_qlt_swap_sub (projT1 c k0) w1 (Qmake 1 1) Hw1q Hck1).
  assert (Hq0 : Qlt 0 (Qminus (Qmake 1 1) w1))
    by exact (Qlt_trans 0 (projT1 c k0) (Qminus (Qmake 1 1) w1) Hck0 Hckq).
  assert (Hepsh : Qlt 0 (eps / 2)%Q) by exact (tvs_qlt_half_pos eps Heps).
  destruct (tvs_qgeom (Qminus (Qmake 1 1) w1) Hq0 Hq1 (eps / 2)%Q Hepsh)
    as [Nq HNq].
  exists (Nat.max Nq (Nat.max N0 N1)). intros n Hn.
  unfold real_lt. exists (eps / 2)%Q. split.
  - apply Qlt_to_QltT. exact Hepsh.
  - exists (Nat.max N0 N1). intros k Hk.
    assert (Hk0' : QltT w0 (projT1 c k - projT1 real_zero k))
      by (apply HN0; exact (tvs_natle_max_l N0 N1 k Hk)).
    assert (Hk1' : QltT w1 (projT1 real_one k - projT1 c k))
      by (apply HN1; exact (tvs_natle_max_r N0 N1 k Hk)).
    assert (Hnq' : Qlt (tvs_qpow (Qminus (Qmake 1 1) w1) n) (eps / 2)%Q)
      by (apply HNq;
          exact (Nat.le_trans Nq (Nat.max Nq (Nat.max N0 N1)) n
                   (Nat.le_max_l Nq (Nat.max N0 N1)) Hn)).
    assert (Hck0' : Qlt 0 (projT1 c k))
      by (apply (tvs_qlt_sub_r w0 (projT1 c k) (projT1 real_zero k) Hw0q);
          apply QltT_to_Qlt; exact Hk0').
    assert (Hck1' : Qlt w1 (Qminus (Qmake 1 1) (projT1 c k)))
      by exact (QltT_to_Qlt w1 (Qminus (Qmake 1 1) (projT1 c k)) Hk1').
    assert (Hckq' : Qle (projT1 c k) (Qminus (Qmake 1 1) w1))
      by (apply Qlt_le_weak;
          exact (tvs_qlt_swap_sub (projT1 c k) w1 (Qmake 1 1) Hw1q Hck1')).
    assert (Hmono : Qle (tvs_qpow (projT1 c k) n)
                        (tvs_qpow (Qminus (Qmake 1 1) w1) n))
      by exact (tvs_qpow_mono _ _ Hckq' (Qlt_le_weak 0 _ Hck0') n).
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_const_proj eps k)).
    setoid_rewrite (tvs_qpow_proj c k n).
    apply (tvs_qlt_gap eps (tvs_qpow (projT1 c k) n) (eps / 2)%Q).
    + field.
    + exact (Qle_lt_trans _ _ _ Hmono Hnq').
Qed.

(* Dispatch of the delta budget: the two Or branches of delta <= 1 unify *)
(* (the lt branch through the geometric budget, the eq branch through the *)
(* zero budget). *)
Lemma tvs_delta_budget : forall (dlt : Real) (Hd0 : real_lt real_zero dlt)
    (Hd1 : real_le dlt real_one) (eps : Q) (Heps : QltT 0 eps),
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_rpow (tv_omd dlt) n) (real_const eps)).
Proof.
  intros dlt Hd0 Hd1 eps Heps.
  destruct Hd1 as [Hdlt | Hd1e].
  - exact (tvs_omd_pow_budget (tv_omd dlt) (tv_omd_pos_of_lt dlt Hdlt)
             (geod_b_kappa_lt_one dlt Hd0) eps Heps).
  - exact (tvs_geom_budget_zero (tv_omd dlt) (tv_omd_eq_zero dlt Hd1e) eps Heps).
Qed.

(* The eq-to-real_eq bridge and the split of the iteration (definitional *)
(* equalities). *)
Lemma tvs_eq_real_eq : forall x y : Real, x = y -> real_eq x y.
Proof.
  intros x y Hxy eps Heps.
  rewrite Hxy.
  exists 0%nat. intros n _.
  apply Qlt_to_QltT.
  assert (Hz : Qeq (Qabs (projT1 y n - projT1 y n)) 0).
  { apply (Qeq_trans _ (Qabs 0) _).
    - apply Qabs_wd. ring.
    - cbn [Qabs]. apply Qeq_refl. }
  rewrite Hz.
  exact (QltT_to_Qlt 0 eps Heps).
Qed.

Lemma tvs_titer_add_eq : forall (states : list (list Real))
    (K : list Real -> list Real -> Real) (m k : nat) (mu : list Real -> Real),
  tv_titer states K (m + k) mu = tv_titer states K m (tv_titer states K k mu).
Proof.
  intros states K m. induction m as [| m IH]; intros k mu.
  - reflexivity.
  - change (Nat.add (Datatypes.S m) k) with (Datatypes.S (Nat.add m k)).
    cbn [tv_titer]. f_equal. apply IH.
Qed.

(* The four Real-layer constant bridges (used by the seminorm chain below). *)
Lemma tvs_abs_opp : forall x : Real, real_eq (real_abs (real_opp x)) (real_abs x).
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj (real_opp x) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_abs_proj x n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj x n)).
  setoid_rewrite (Qabs_opp (projT1 x n)).
  ring.
Qed.

Lemma tvs_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)%Q).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const a) (real_const b) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj b n)).
  ring.
Qed.

Lemma tvs_two_eq : real_eq (real_const (Qmake 2 1)) (real_plus real_one real_one).
Proof.
  apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Qmake 2 1) n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one real_one n)).
  setoid_rewrite (tvs_one_proj n).
  ring.
Qed.

(* The pointwise Q projection of real_of_nat (closed by unfolding Qeq and *)
(* rewriting through the multiplicative action of Z, as in the part01 *)
(* adjustment). *)
Lemma tvs_ofnat_proj : forall (n k : nat),
  Qeq (projT1 (real_of_nat n) k) (Z.of_nat n # 1).
Proof.
  intro n. induction n as [| m IH].
  - intro k. cbn [real_of_nat].
    replace (Z.of_nat 0)%Z with 0%Z by reflexivity.
    apply qeqT_imp_qeq. apply real_const_proj.
  - intro k. cbn [real_of_nat].
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_of_nat m) k)).
    rewrite (tvs_one_proj k).
    rewrite IH.
    unfold Qeq. cbn [Qnum Qden Qplus Qminus Qopp].
    rewrite !Z.mul_1_r.
    replace (Z.of_nat (Datatypes.S m)) with (Z.add 1 (Z.of_nat m)) by lia.
    reflexivity.
Qed.

Lemma tvs_ofnat_const_eq : forall n : nat,
  real_eq (real_of_nat n) (real_const (Qmake (Z.of_nat n) 1)).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  apply qeq_imp_qeqT.
  setoid_rewrite (tvs_ofnat_proj n k).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (Z.of_nat n # 1) k)).
  ring.
Qed.

(* ################ Part 4: the tvs_tv seminorm contraction chain (the main *)
(* ################ engine of M1) #### *)

(* The half-factor-free seminorm: the sum over the enumeration of |mu - nu| *)
(* (twice tv_doeblin; this dodges the unreachable projection of *)
(* real_inv_pos, and under the Or encoding the factor 2 cancels the half *)
(* factor exactly). *)
Definition tvs_tv (states : list (list Real)) (mu nu : list Real -> Real) : Real :=
  real_list_sum (list Real)
    (fun s : list Real => real_abs (real_minus_r (mu s) (nu s))) states.

Lemma tvs_const_two_pos : real_le real_zero (real_const (Qmake 2 1)).
Proof.
  apply tvd_lt_le. apply real_const_lt. exact qltT_0_2.
Qed.

Lemma tvs_two_half_one :
  real_eq (real_mult (real_const (Qmake 2 1)) tv_half) real_one.
Proof.
  apply (real_eq_trans (real_mult (real_const (Qmake 2 1)) tv_half)
           (real_mult tv_half (real_const (Qmake 2 1))) real_one).
  - exact (real_mult_comm (real_const (Qmake 2 1)) tv_half).
  - apply (real_eq_trans (real_mult tv_half (real_const (Qmake 2 1)))
             (real_mult tv_half (real_plus real_one real_one)) real_one).
    + apply (RealSetoid.real_eq_mult_compat tv_half (real_const (Qmake 2 1))
               tv_half (real_plus real_one real_one)
               (real_eq_refl tv_half) tvs_two_eq).
    + apply (real_eq_trans (real_mult tv_half (real_plus real_one real_one))
               (real_mult (real_plus real_one real_one) tv_half) real_one).
      * exact (real_mult_comm tv_half (real_plus real_one real_one)).
      * exact (real_inv_pos_correct (real_plus real_one real_one) tv_two_pos).
Qed.

(* Doubling tv_doeblin gives tvs_tv (2*(half*sum) == sum, pure eq algebra). *)
Lemma tvs_doeblin_double : forall (states : list (list Real))
    (a b : list Real -> Real),
  real_eq (real_mult (real_const (Qmake 2 1)) (tv_doeblin states a b))
          (tvs_tv states a b).
Proof.
  intros states a b.
  apply (real_eq_trans
           (real_mult (real_const (Qmake 2 1)) (tv_doeblin states a b))
           (real_mult (real_mult (real_const (Qmake 2 1)) tv_half)
                      (tvs_tv states a b))
           (tvs_tv states a b)).
  - exact (real_mult_assoc (real_const (Qmake 2 1)) tv_half
             (tvs_tv states a b)).
  - apply (real_eq_trans
             (real_mult (real_mult (real_const (Qmake 2 1)) tv_half)
                        (tvs_tv states a b))
             (real_mult real_one (tvs_tv states a b))
             (tvs_tv states a b)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_const (Qmake 2 1)) tv_half)
               (tvs_tv states a b) real_one (tvs_tv states a b)
               tvs_two_half_one (real_eq_refl (tvs_tv states a b))).
    + apply (real_eq_trans (real_mult real_one (tvs_tv states a b))
               (real_mult (tvs_tv states a b) real_one)
               (tvs_tv states a b)).
      * exact (real_mult_comm real_one (tvs_tv states a b)).
      * exact (real_mult_one (tvs_tv states a b)).
Qed.

(* The contraction statement: tvs_tv(K^n mu, K^n nu) <= omd^n * tvs_tv(mu, nu) *)
(* (the original tv_doeblin_iter with the factor 2 cancelling the half *)
(* factor; the two Or branches transport through le_id). *)
Lemma tvs_tv_iter :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
    (Hg : real_lt real_zero gamma) (z : list Real -> list Real -> Real)
    (Hzlo : forall i j : list Real, real_le (real_opp gamma) (z i j))
    (Hzhi : forall i j : list Real, real_le (z i j) gamma)
    (Labs : forall f : list Real -> Real,
       real_le (real_abs (real_list_sum (list Real) f states))
               (real_list_sum (list Real)
                  (fun w : list Real => real_abs (f w)) states))
    (n : nat) (mu nu : list Real -> Real),
  real_eq (real_list_sum (list Real) mu states) real_one ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_le (tvs_tv states
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
          (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                     (tvs_tv states mu nu)).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma Hg z Hzlo Hzhi Labs n mu nu Hmu Hnu.
  assert (Hcon := tv_doeblin_iter states (tvd_K states n_pos Ttemp Ttemp_pos z)
                    (tvd_K_row states n_pos Ttemp Ttemp_pos z)
                    (tvd_u states n_pos) (tvd_u_norm states n_pos)
                    (tvd_dstar Ttemp Ttemp_pos gamma)
                    (tvd_dstar_le_one Ttemp Ttemp_pos gamma Hg)
                    (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hzlo Hzhi)
                    Labs n mu nu Hmu Hnu).
  assert (H2 := real_le_mult_compat_r (real_const (Qmake 2 1))
                   (tv_doeblin states
                      (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                      (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
                   (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                              (tv_doeblin states mu nu))
                   tvs_const_two_pos Hcon).
  assert (HL1 : real_eq (real_mult (real_const (Qmake 2 1))
                          (tv_doeblin states
                             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
                  (tvs_tv states
                     (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                     (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
    by exact (tvs_doeblin_double states _ _).
  assert (HR2 : real_eq (real_mult (real_const (Qmake 2 1))
                          (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                                      (tv_doeblin states mu nu)))
                  (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                              (tvs_tv states mu nu))).
  { apply (real_eq_trans
             (real_mult (real_const (Qmake 2 1))
                (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                           (tv_doeblin states mu nu)))
             (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                (real_mult (real_const (Qmake 2 1)) (tv_doeblin states mu nu)))
             (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                         (tvs_tv states mu nu))).
    - exact (tvd_mult_swap_ab (real_const (Qmake 2 1))
                (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                (tv_doeblin states mu nu)).
    - apply (RealSetoid.real_eq_mult_compat
               (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
               (real_mult (real_const (Qmake 2 1)) (tv_doeblin states mu nu))
               (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
               (tvs_tv states mu nu)
               (real_eq_refl (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n))
               (tvs_doeblin_double states mu nu)). }
  apply (RealSetoid.real_le_id_l
           (tvs_tv states
              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
           (real_mult (real_const (Qmake 2 1))
              (tv_doeblin states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
           (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                       (tvs_tv states mu nu))
           (real_eq_sym (real_mult (real_const (Qmake 2 1))
                           (tv_doeblin states
                              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                              (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
              (tvs_tv states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu))
              HL1)).
  exact (RealSetoid.real_le_id_r
           (real_mult (real_const (Qmake 2 1))
              (tv_doeblin states
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n mu)
                 (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) n nu)))
           (real_mult (real_const (Qmake 2 1))
              (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                         (tv_doeblin states mu nu)))
           (real_mult (tv_rpow (tv_omd (tvd_dstar Ttemp Ttemp_pos gamma)) n)
                       (tvs_tv states mu nu))
           HR2 H2).
Qed.

(* The uniform base bound: a normalized nonnegative nu gives *)
(* tvs_tv(nu, u) < 2 + len + 1 (pointwise triangle inequality, a +1 slack, *)
(* then summation). *)
Lemma tvs_tv_unif_bound :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
    (gamma : Real) (z : list Real -> list Real -> Real)
    (nu : list Real -> Real),
  (forall i : list Real, real_le real_zero (nu i)) ->
  real_eq (real_list_sum (list Real) nu states) real_one ->
  real_lt (tvs_tv states nu (tvd_u states n_pos))
          (real_const
             (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                    (Qmake 1 1))).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z nu Hnu Hnorm.
  assert (Hpt : forall i : list Real,
    real_le (real_abs (real_minus_r (nu i) (tvd_u states n_pos i)))
            (real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)).
  { intro i.
    assert (Htri := real_abs_triangle_le_eps (nu i)
                      (real_opp (tvd_u states n_pos i)) real_one real_lt_zero_one).
    assert (Habsnu : real_eq (real_abs (nu i)) (nu i))
      by exact (tvd_abs_le_id (nu i) (Hnu i)).
    assert (Habsu : real_eq (real_abs (real_opp (tvd_u states n_pos i)))
                             (tvd_u states n_pos i)).
    { apply (real_eq_trans (real_abs (real_opp (tvd_u states n_pos i)))
               (real_abs (tvd_u states n_pos i)) (tvd_u states n_pos i)).
      - exact (tvs_abs_opp (tvd_u states n_pos i)).
      - exact (tvd_abs_le_id (tvd_u states n_pos i)
                 (tvd_lt_le real_zero (tvd_u states n_pos i)
                    (real_inv_pos_pos (real_of_nat (length states)) n_pos))). }
    exact (RealSetoid.real_le_id_r
             (real_abs (real_minus_r (nu i) (tvd_u states n_pos i)))
             (real_plus (real_plus (real_abs (nu i))
                          (real_abs (real_opp (tvd_u states n_pos i)))) real_one)
             (real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
             (RealSetoid.real_eq_plus_compat
                (real_plus (real_abs (nu i))
                   (real_abs (real_opp (tvd_u states n_pos i))))
                real_one
                (real_plus (nu i) (tvd_u states n_pos i)) real_one
                (RealSetoid.real_eq_plus_compat (real_abs (nu i))
                   (real_abs (real_opp (tvd_u states n_pos i)))
                   (nu i) (tvd_u states n_pos i) Habsnu Habsu)
                (real_eq_refl real_one))
             Htri). }
  assert (Hsum : real_le (tvs_tv states nu (tvd_u states n_pos))
                   (real_list_sum (list Real)
                      (fun i : list Real =>
                         real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                      states))
    by (apply real_list_sum_le; exact Hpt).
  assert (Hrhs : real_eq
    (real_list_sum (list Real)
       (fun i : list Real =>
          real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one) states)
    (real_plus (real_plus real_one real_one)
       (real_mult (real_of_nat (length states)) real_one))).
  { apply (real_eq_trans
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                states)
             (real_plus
                (real_list_sum (list Real)
                   (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                   states)
                (real_list_sum (list Real) (fun _ : list Real => real_one) states))
             (real_plus (real_plus real_one real_one)
                (real_mult (real_of_nat (length states)) real_one))).
    - exact (real_list_sum_add (list Real)
                (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                (fun _ : list Real => real_one) states).
    - apply (RealSetoid.real_eq_plus_compat
                (real_list_sum (list Real)
                   (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                   states)
                (real_list_sum (list Real) (fun _ : list Real => real_one) states)
                (real_plus real_one real_one)
                (real_mult (real_of_nat (length states)) real_one)).
      + apply (real_eq_trans
                  (real_list_sum (list Real)
                     (fun i : list Real => real_plus (nu i) (tvd_u states n_pos i))
                     states)
                  (real_plus (real_list_sum (list Real) nu states)
                             (real_list_sum (list Real) (tvd_u states n_pos) states))
                  (real_plus real_one real_one)).
        * exact (real_list_sum_add (list Real) nu (tvd_u states n_pos) states).
        * exact (RealSetoid.real_eq_plus_compat (real_list_sum (list Real) nu states)
                    (real_list_sum (list Real) (tvd_u states n_pos) states)
                    real_one real_one Hnorm (tvd_u_norm states n_pos)).
      + exact (tvd_list_sum_const (list Real) real_one states). }
  assert (Hone : real_eq real_one (real_const (Qmake 1 1))).
  { apply real_eq_of_zero_diff. intro n.
    apply qeq_imp_qeqT.
    setoid_rewrite (tvs_one_proj n).
    ring. }
  assert (Hlen : real_eq (real_mult (real_of_nat (length states)) real_one)
                   (real_const (Qmake (Z.of_nat (length states)) 1))).
  { apply (real_eq_trans (real_mult (real_of_nat (length states)) real_one)
             (real_mult (real_const (Qmake (Z.of_nat (length states)) 1)) real_one)
             (real_const (Qmake (Z.of_nat (length states)) 1))).
    - apply (RealSetoid.real_eq_mult_compat (real_of_nat (length states))
               real_one (real_const (Qmake (Z.of_nat (length states)) 1)) real_one
               (tvs_ofnat_const_eq (length states)) Hone).
    - exact (real_mult_one (real_const (Qmake (Z.of_nat (length states)) 1))). }
  assert (HC : real_eq
    (real_plus (real_plus real_one real_one)
       (real_mult (real_of_nat (length states)) real_one))
    (real_const
       (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
          (Qmake (Z.of_nat (length states)) 1)))).
  { apply (RealSetoid.real_eq_plus_compat
             (real_plus real_one real_one)
             (real_mult (real_of_nat (length states)) real_one)
             (real_const (Qplus (Qmake 1 1) (Qmake 1 1)))
             (real_const (Qmake (Z.of_nat (length states)) 1))
             (RealSetoid.real_eq_plus_compat real_one real_one
                (real_const (Qmake 1 1)) (real_const (Qmake 1 1)) Hone Hone)
             Hlen). }
  assert (Hltc : real_lt
    (real_const (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                   (Qmake (Z.of_nat (length states)) 1)))
    (real_const (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                   (Qmake 1 1)))).
  { apply real_const_lt. apply Qlt_to_QltT. unfold Qlt. simpl. lia. }
  apply (real_le_lt_trans (tvs_tv states nu (tvd_u states n_pos))
           (real_const
              (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                 (Qmake (Z.of_nat (length states)) 1)))
           (real_const
              (Qplus (Qplus (Qmake 2 1) (Qmake (Z.of_nat (length states)) 1))
                     (Qmake 1 1)))).
  - exact (RealSetoid.real_le_id_r (tvs_tv states nu (tvd_u states n_pos))
             (real_list_sum (list Real)
                (fun i : list Real =>
                   real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                states)
             (real_const
                (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                   (Qmake (Z.of_nat (length states)) 1)))
             (real_eq_trans
                (real_list_sum (list Real)
                   (fun i : list Real =>
                      real_plus (real_plus (nu i) (tvd_u states n_pos i)) real_one)
                   states)
                (real_plus (real_plus real_one real_one)
                   (real_mult (real_of_nat (length states)) real_one))
                (real_const
                   (Qplus (Qplus (Qmake 1 1) (Qmake 1 1))
                      (Qmake (Z.of_nat (length states)) 1))) Hrhs HC)
             Hsum).
  - exact Hltc.
Qed.

(* ################ Part 5: the coordinate Cauchy modulus (the core of M1) #### *)

(* Multiplication of nonnegative factors under the Or encoding (all four *)
(* branches constructed). *)
Lemma tvs_mult_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b -> real_le real_zero (real_mult a b).
Proof.
  intros a b Ha Hb. destruct Ha as [Ha | Ha]; destruct Hb as [Hb | Hb].
  - apply tvd_lt_le. exact (real_mult_pos_compat a b Ha Hb).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult a real_zero) real_zero
                (RealSetoid.real_eq_mult_compat a b a real_zero (real_eq_refl a)
                   (real_eq_sym real_zero b Hb))
                (real_mult_zero a))).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult real_zero b) real_zero
                (RealSetoid.real_eq_mult_compat a b real_zero b
                   (real_eq_sym real_zero a Ha) (real_eq_refl b))
                (real_eq_trans (real_mult real_zero b) (real_mult b real_zero)
                   real_zero
                   (real_mult_comm real_zero b) (real_mult_zero b)))).
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult a b) real_zero
             (real_eq_trans (real_mult a b) (real_mult real_zero b) real_zero
                (RealSetoid.real_eq_mult_compat a b real_zero b
                   (real_eq_sym real_zero a Ha) (real_eq_refl b))
                (real_eq_trans (real_mult real_zero b)
                   (real_mult real_zero real_zero) real_zero
                   (RealSetoid.real_eq_mult_compat real_zero b real_zero real_zero
                      (real_eq_refl real_zero) (real_eq_sym real_zero b Hb))
                   (real_mult_zero real_zero)))).
Qed.

(* The iterated distribution is nonnegative at every coordinate. *)
Lemma tvs_iter_nonneg :
  forall (states : list (list Real))
    (n_pos : real_lt real_zero (real_of_nat (length states)))
    (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
    (z : list Real -> list Real -> Real) (t : nat) (i : list Real),
  real_le real_zero
    (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) t
              (tvd_u states n_pos) i).
Proof.
  intros states n_pos Ttemp Ttemp_pos z t. induction t as [| t IH]; intro i.
  - apply tvd_lt_le. exact (real_inv_pos_pos (real_of_nat (length states)) n_pos).
  - unfold tv_step.
    apply real_list_sum_nonneg. intro w.
    exact (tvs_mult_nonneg
             (tv_titer states (tvd_K states n_pos Ttemp Ttemp_pos z) t
                       (tvd_u states n_pos) w)
             (tvd_K states n_pos Ttemp Ttemp_pos z w i) (IH w)
             (tvd_K_pos states n_pos Ttemp Ttemp_pos z w i)).
Qed.

(* The pointwise extractor: tvs_tv(a,b) < eps/2 gives |a(j) - b(j)| < eps *)
(* for j in the enumeration. *)
Lemma tvs_pt_of_tv_lt : forall (states : list (list Real))
    (a b : list Real -> Real) (j : list Real) (eps : Q),
  InT j states -> QltT 0 (eps / 2)%Q ->
  real_lt (tvs_tv states a b) (real_const (eps / 2)%Q) ->
  real_lt (real_abs (real_minus_r (a j) (b j))) (real_const eps).
Proof.
  intros states a b j eps Hj Heph Htv.
  destruct Htv as [wt [Hwt [Nt HNt]]].
  unfold real_lt. exists (eps / 2)%Q. split.
  - exact Heph.
  - exists Nt. intros k Hk.
    apply Qlt_to_QltT.
    setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj eps k)).
    apply (tvs_qlt_gap eps (projT1 (real_abs (real_minus_r (a j) (b j))) k)
             (eps / 2)%Q).
    + field.
    + apply (Qle_lt_trans (projT1 (real_abs (real_minus_r (a j) (b j))) k)
               (projT1 (tvs_tv states a b) k) (eps / 2)%Q).
      * exact (tvs_qsum_ge_abs (list Real)
                  (fun i : list Real => real_minus_r (a i) (b i)) j states k Hj).
      * apply (tvs_qlt_sub_r wt (eps / 2)%Q (projT1 (tvs_tv states a b) k)).
        -- exact (QltT_to_Qlt 0 wt Hwt).
        -- exact (QltT_to_Qlt wt
                    (eps / 2 - projT1 (tvs_tv states a b) k)%Q (HNt k Hk)).
Qed.

(* The Qeq constant bridge. *)
Lemma tvs_const_eq_of_Qeq : forall a b : Q,
  Qeq a b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b Hab. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj a n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj b n)).
  rewrite Hab. ring.
Qed.

(* Annihilation by iteration: c ≈ 0 gives c^(S t) ≈ 0. *)
Lemma tvs_rpow_zero : forall (c : Real) (Hc : real_eq c real_zero) (t : nat),
  real_eq (tv_rpow c (Datatypes.S t)) real_zero.
Proof.
  intros c Hc t. induction t as [| m IH].
  - cbn [tv_rpow].
    exact (real_eq_trans (real_mult c real_one) c real_zero
             (real_mult_one c) Hc).
  - change (tv_rpow c (Datatypes.S (Datatypes.S m)))
      with (real_mult c (tv_rpow c (Datatypes.S m))).
    exact (real_eq_trans (real_mult c (tv_rpow c (Datatypes.S m))) real_zero
             real_zero
             (real_eq_trans (real_mult c (tv_rpow c (Datatypes.S m)))
                (real_mult real_zero (tv_rpow c (Datatypes.S m))) real_zero
                (RealSetoid.real_eq_mult_compat c (tv_rpow c (Datatypes.S m))
                   real_zero (tv_rpow c (Datatypes.S m)) Hc
                   (real_eq_refl (tv_rpow c (Datatypes.S m))))
                (real_eq_trans (real_mult real_zero (tv_rpow c (Datatypes.S m)))
                   (real_mult (tv_rpow c (Datatypes.S m)) real_zero) real_zero
                   (real_mult_comm real_zero (tv_rpow c (Datatypes.S m)))
                   (real_mult_zero (tv_rpow c (Datatypes.S m)))))
             (real_eq_refl real_zero)).
Qed.

(* Honest registration: the coordinate-Cauchy main statement tvs_coord_cauchy *)
(* has a settled structure but is not closed here.  The chain in full: *)
(* tvs_tv_iter (the contraction), tvs_tv_unif_bound (the uniform base bound), *)
(* tvs_delta_budget (the two-branch dispatch of the omd geometric budget), *)
(* tvs_pt_of_tv_lt (the pointwise extraction), and the delta*=1 annihilation *)
(* chain tvs_iter_nonneg / tvs_mult_nonneg / tvs_rpow_zero -- all are *)
(* registered and closed.  Only the assembly remains: an aux taking the *)
(* HNB bound as an argument (the m<=n case direct, the n<=m case through the *)
(* symmetry of abs), with the delta*<1 branch through the strict product *)
(* chain tvs_omd_pow_budget / tvs_rpow_pos and the delta*=1 branch through *)
(* the annihilation chain tvs_rpow_zero.  The full design note lives in the *)
(* continuation design document. *)

(* ################ Assumption audit (same scope as the registered statements) ################ *)
Print Assumptions tvs_tv_iter.
Print Assumptions tvs_tv_unif_bound.
Print Assumptions tvs_omd_pow_budget.
Print Assumptions tvs_delta_budget.
Print Assumptions tvs_pt_of_tv_lt.
(* Honest registration: the assembly of tvs_coord_cauchy is not closed; the *)
(* closed prefix is kept.  The settled structure: an aux taking the HNB *)
(* bound as an argument (the m<=n case direct, the n<=m case through the *)
(* symmetry of abs) plus the two-branch budget.  Every factor statement is *)
(* proved: tvs_tv_iter / tvs_tv_unif_bound / tvs_delta_budget / *)
(* tvs_pt_of_tv_lt / tvs_iter_nonneg / tvs_mult_nonneg / tvs_rpow_zero / *)
(* tvs_const_eq_of_Qeq / tvs_qlt_*.  The one remaining blocker: a closer for *)
(* Qlt goals is missing -- the stdlib has no Qlt_0_1, and lia/lra do not *)
(* accept Qlt and (a?=b)=Lt goals (verified by direct testing).  HCQ *)
(* (0 < CQ) needs Qlt_le_trans 0 1 CQ, whose Qle 2 <= CQ side is one step *)
(* away.  The prescription is settled: turn Qle 2 <= CQ into Qle 0 (CQ-1) *)
(* with proj2 of Qle_minus_iff (the green shape with 0 on the left), plus *)
(* Qlt 0 1 by unfold Qlt; simpl; reflexivity (closes on the concrete *)
(* instance).  The full assembly draft lives in the continuation design *)
(* document. *)
