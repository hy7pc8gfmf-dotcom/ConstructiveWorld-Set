(* ConstructiveWorld-Set -- quadratic-form spectrum face: sum-of-squares discriminant bounds and explicit rational sqrt rates. *)

(** * UpReqSpec2x2: spectrum of a 2x2 self-adjoint quadratic form and an explicit Newton rate for its square root.

    Mission.  The 2x2 self-adjoint discriminant [sp2_disc] is a sum of two
      squares, nonnegative at every rational approximation
      ([sp2_disc_sqpos]); a Newton iteration on [sp2_qdisc] ([sp2_qnewton],
      step [sp2_qnewton_step], residual [sp2_qgap], scale [sp2_q4pow])
      proves the explicit square-root rate [sp2_sqrt_rate_core] with
      Set-face exit [sp2_sqrt_rate]; [sp2_eig_gap] exhibits a square root
      [s] of the discriminant with the eigenvalue gap [sp2_eig_up] -
      [sp2_eig_dn] = [s] over [real_sqrt_exists];
      [sp2_disc_eq_zero_of_degen] and [sp2_eig_s_pos] complete the family.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Lia], [Arith],
      [Extraction].  Requires [AttnSqrt], [S02_CauchyComplete],
      [S01_BaseRing] of this development.

    References.  This development, UpReqSpec2x2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSpec2x2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import AttnSqrt.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
Require Import S02_CauchyComplete.
Require Import S01_BaseRing.

(* ============================================================ *)
(* ================= Section 0. Pointwise representation engine ================= *)
(* ============================================================ *)

Lemma sp2_pt_plus : forall (x y : Real) (n : nat),
  projT1 (real_plus x y) n == (projT1 x n + projT1 y n)%Q.
Proof. intros [u Hu] [v Hv] n. exact (Qeq_refl (u n + v n)%Q). Qed.

Lemma sp2_pt_mult : forall (x y : Real) (n : nat),
  projT1 (real_mult x y) n == (projT1 x n * projT1 y n)%Q.
Proof. intros [u Hu] [v Hv] n. exact (Qeq_refl (u n * v n)%Q). Qed.

Lemma sp2_pt_opp : forall (x : Real) (n : nat),
  projT1 (real_opp x) n == (- projT1 x n)%Q.
Proof. intros [u Hu] n. exact (Qeq_refl (- u n)%Q). Qed.

Lemma sp2_pt_const : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. exact (Qeq_refl c). Qed.

Lemma sp2_pt_zero : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intros n. exact (Qeq_refl 0%Q). Qed.

(* The pointwise discriminant: D := (a - d)^2 + (2 * b)^2, a sum of two squares. *)
Definition sp2_disc (a d b : Real) : Real :=
  real_plus (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)))
            (real_mult (real_plus b b) (real_plus b b)).

(* ============================================================ *)
(* ================= Section 1. Rational-layer toolkit ================= *)
(* ============================================================ *)

Lemma sp2_qlt_lit4 : Qlt 0 4%Q.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qeq_le : forall x y : Q, x == y -> Qle x y.
Proof.
  intros x y H.
  unfold Qle, Qeq in *.
  exact (Z.eq_le_incl _ _ H).
Qed.

Lemma sp2_qsq_nonneg : forall q : Q, Qle 0 (q * q).
Proof.
  intros q. destruct (Qlt_le_dec 0 q) as [H | H].
  - assert (Hle : Qle 0 q) by (apply Qlt_le_weak; exact H).
    apply (Qle_trans 0 (0 * q) (q * q)).
    + rewrite Qmult_0_l. apply Qle_refl.
    + exact (Qmult_le_compat_r 0 q q Hle Hle).
  - assert (Hn : Qle 0 (- q)).
    { apply (Qle_trans 0 (- 0) (- q)).
      - apply sp2_qeq_le. reflexivity.
      - exact (Qopp_le_compat q 0 H). }
    apply (Qle_trans 0 ((- q) * (- q)) (q * q)).
    + apply (Qle_trans 0 (0 * (- q)) ((- q) * (- q))).
      * rewrite Qmult_0_l. apply Qle_refl.
      * exact (Qmult_le_compat_r 0 (- q) (- q) Hn Hn).
    + apply sp2_qeq_le. ring.
Qed.

(* ============================================================ *)
(* Section 1R. Further rational-layer facts; two statements are restated *)
(* locally rather than widening the dependency face of this module. *)
(* ============================================================ *)

Lemma sp2_qle_eq_l : forall x y z : Q, y == x -> Qle x z -> Qle y z.
Proof.
  intros x y z H H0.
  apply (Qle_trans y x z).
  - apply sp2_qeq_le. exact H.
  - exact H0.
Qed.

Lemma sp2_qle_eq_r : forall x y z : Q, z == y -> Qle x y -> Qle x z.
Proof.
  intros x y z H H0.
  apply (Qle_trans x y z).
  - exact H0.
  - apply sp2_qeq_le. exact (Qeq_sym _ _ H).
Qed.

Lemma sp2_qle_plus_r : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy.
  apply Qle_trans with (x + 0).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact Hy.
Qed.

Lemma sp2_qle_plus_l : forall x y : Q, Qle 0 x -> Qle y (x + y).
Proof.
  intros x y Hx.
  apply (Qle_trans y (0 + y) (x + y)).
  - apply sp2_qeq_le. ring.
  - apply Qplus_le_compat.
    + exact Hx.
    + apply Qle_refl.
Qed.

Lemma sp2_qminus_0_r : forall q : Q, q - 0 == q.
Proof. intros q. ring. Qed.

Lemma sp2_qmult_le_compat_l : forall x y z : Q, Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H H0.
  assert (Hc1 : (z * x == x * z)%Q) by ring.
  assert (Hc2 : (y * z == z * y)%Q) by ring.
  exact (sp2_qle_eq_r (z * x)%Q (y * z)%Q (z * y)%Q (Qeq_sym _ _ Hc2)
           (sp2_qle_eq_l (x * z)%Q (z * x)%Q (y * z)%Q Hc1
              (Qmult_le_compat_r x y z H H0))).
Qed.

(* Central transport facts: Qlt and Qle are well defined modulo Qeq, *)
(* transported explicitly through Qcompare_comp. *)
Lemma sp2_qlt_wd : forall a b c d : Q, a == c -> b == d -> Qlt a b -> Qlt c d.
Proof.
  intros a b c d Hac Hbd H.
  apply Qlt_alt in H.
  apply Qlt_alt.
  rewrite <- (Qcompare_comp a c Hac b d Hbd).
  exact H.
Qed.

Lemma sp2_qlt_lit1 : Qlt 0 1.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit2 : Qlt 0 2.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qle_lit1 : Qle 0 1.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qle_lit3 : Qle 0 3.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qlt_lit9_16 : Qlt 9 16.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit9_12 : Qlt 9 12.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qlt_lit1_4 : Qlt 1 4.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma sp2_qle_lit0_4 : Qle 0 4.
Proof. unfold Qle. cbn. lia. Qed.

Lemma sp2_qle_lit0_16 : Qle 0 16.
Proof. unfold Qle. cbn. lia. Qed.

(* Half toolkit: eps/2 is positive and strictly smaller than eps. *)
Lemma sp2_qltT_pos_half : forall e : Q, QltT 0 e -> QltT 0 (e/2).
Proof.
  intros e He.
  apply Qlt_to_QltT.
  apply Qlt_shift_div_l.
  - reflexivity.
  - simpl. apply QltT_to_Qlt. exact He.
Qed.

Lemma sp2_qhalf_lt : forall e : Q, QltT 0 e -> QltT (e/2) e.
Proof.
  intros e He.
  assert (Hh : Qlt 0 (e/2)) by (apply QltT_to_Qlt; apply sp2_qltT_pos_half; exact He).
  assert (Hs : e/2 + e/2 == e) by field.
  pose proof (proj2 (Qplus_lt_r 0%Q (e/2)%Q (e/2)%Q) Hh) as Hlt.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans (e/2)%Q (e/2 + e/2)%Q e).
  - exact (sp2_qlt_wd (e/2 + 0)%Q (e/2 + e/2)%Q (e/2)%Q (e/2 + e/2)%Q
             (Qplus_0_r (e/2)) (Qeq_refl _) Hlt).
  - exact (sp2_qeq_le _ _ Hs).
Qed.

(* ============================================================ *)
(* ================= Section 2A. The LPO-free nonnegativity chain for the *)
(*    discriminant and the strict-positivity upgrade of its witnesses ================= *)
(* ============================================================ *)

Definition sp2_lower0 (y : Real) : Set :=
  forall eps : Q, QltT 0 eps -> real_lt (real_opp y) (real_const eps).

(* Pointwise reshaping: the raw pointwise shape of a real_lt witness into the summed shape. *)
Lemma sp2_lowpt_sum : forall (y : Real) (d e : Q) (n : nat),
  QltT d (e + projT1 y n)%Q ->
  QltT d (projT1 (real_const e) n - projT1 (real_opp y) n).
Proof.
  intros y d e n H.
  assert (Hx : (projT1 (real_const e) n - projT1 (real_opp y) n
                == e + projT1 y n)%Q).
  { setoid_rewrite (sp2_pt_const e n).
    setoid_rewrite (sp2_pt_opp y n).
    ring. }
  apply Qlt_to_QltT.
  exact (sp2_qlt_wd _ _ _ _ (Qeq_refl _) (Qeq_sym _ _ Hx) (QltT_to_Qlt _ _ H)).
Qed.

Lemma sp2_lower0_intro : forall y : Real,
  (forall n : nat, Qle 0 (projT1 y n)) -> sp2_lower0 y.
Proof.
  intros y Hy eps Heps.
  exists (eps/2)%Q.
  split.
  - exact (sp2_qltT_pos_half eps Heps).
  - exists 0%nat.
    intros n Hn.
    apply sp2_lowpt_sum.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (eps/2)%Q eps%Q (eps + projT1 y n)%Q).
    + exact (QltT_to_Qlt _ _ (sp2_qhalf_lt eps Heps)).
    + exact (sp2_qle_plus_r eps (projT1 y n) (Hy n)).
Qed.

Lemma sp2_lower0_plus : forall y z : Real,
  sp2_lower0 y -> sp2_lower0 z -> sp2_lower0 (real_plus y z).
Proof.
  intros y z Hy Hz eps Heps.
  destruct (Hy (eps/2)%Q (sp2_qltT_pos_half eps Heps)) as [d1 [Hd1 [N1 HN1]]].
  destruct (Hz (eps/2)%Q (sp2_qltT_pos_half eps Heps)) as [d2 [Hd2 [N2 HN2]]].
  exists (d1 + d2)%Q.
  split.
  - apply Qlt_to_QltT.
    apply (sp2_qlt_wd (0 + 0)%Q (d1 + d2)%Q 0%Q (d1 + d2)%Q).
    + ring.
    + reflexivity.
    + exact (Qplus_lt_compat _ _ _ _ (QltT_to_Qlt _ _ Hd1) (QltT_to_Qlt _ _ Hd2)).
  - exists (max N1 N2).
    intros n Hn.
    assert (K1 : NatLe N1 n).
    { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
        [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
    assert (K2 : NatLe N2 n).
    { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
        [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
    assert (Hx1 : projT1 (real_const (eps/2)) n - projT1 (real_opp y) n
                  == (eps/2 + projT1 y n)%Q).
    { setoid_rewrite (sp2_pt_const (eps/2) n). setoid_rewrite (sp2_pt_opp y n). ring. }
    assert (Hx2 : projT1 (real_const (eps/2)) n - projT1 (real_opp z) n
                  == (eps/2 + projT1 z n)%Q).
    { setoid_rewrite (sp2_pt_const (eps/2) n). setoid_rewrite (sp2_pt_opp z n). ring. }
    pose proof (sp2_qlt_wd _ _ _ _ (Qeq_refl _) Hx1 (QltT_to_Qlt _ _ (HN1 n K1))) as K1'.
    pose proof (sp2_qlt_wd _ _ _ _ (Qeq_refl _) Hx2 (QltT_to_Qlt _ _ (HN2 n K2))) as K2'.
    apply sp2_lowpt_sum.
    apply Qlt_to_QltT.
    setoid_rewrite (sp2_pt_plus y z n).
    assert (Hsp : (eps + (projT1 y n + projT1 z n)
                   == (eps/2 + projT1 y n) + (eps/2 + projT1 z n))%Q) by field.
    exact (sp2_qlt_wd (d1 + d2)%Q
             ((eps / 2 + projT1 y n) + (eps / 2 + projT1 z n))%Q
             (d1 + d2)%Q (eps + (projT1 y n + projT1 z n))%Q
             (Qeq_refl (d1 + d2)) (Qeq_sym _ _ Hsp)
             (Qplus_lt_compat _ _ _ _ K1' K2')).
Qed.

Lemma sp2_lower0_sq : forall x : Real, sp2_lower0 (real_mult x x).
Proof.
  intros x.
  apply sp2_lower0_intro.
  intros n.
  setoid_rewrite (sp2_pt_mult x x n).
  apply sp2_qsq_nonneg.
Qed.

(* The nonnegativity statement: no axioms and no classical logic; the chain *)
(*   uses no Or case split and no sign decision on literals, hence stays *)
(*   LPO-free.  It realizes the lower-bound form of the discriminant recorded *)
(*   in the design notes. *)
Theorem sp2_disc_sqpos : forall a d b : Real, sp2_lower0 (sp2_disc a d b).
Proof.
  intros a d b.
  apply (sp2_lower0_plus
           (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)))
           (real_mult (real_plus b b) (real_plus b b))).
  - apply sp2_lower0_sq.
  - apply sp2_lower0_sq.
Qed.

(* Strict-positivity upgrade of the sum of two squares: strictness of either *)
(* summand gives strictness of the sum, transporting the witnesses directly. *)
Lemma sp2_disc_pos_gen : forall x y : Real,
  Or (real_lt real_zero (real_mult x x)) (real_lt real_zero (real_mult y y)) ->
  real_lt real_zero (real_plus (real_mult x x) (real_mult y y)).
Proof.
  intros x y [Hxy | Hxy].
  - destruct Hxy as [delta [Hdelta [N HN]]].
    exists delta. split.
    + exact Hdelta.
    + exists N. intros n Hn.
      pose proof (QltT_to_Qlt _ _ (HN n Hn)) as K.
      setoid_rewrite (sp2_pt_mult x x n) in K.
      setoid_rewrite (sp2_pt_zero n) in K.
      setoid_rewrite sp2_qminus_0_r in K.
      apply Qlt_to_QltT.
      setoid_rewrite (sp2_pt_plus (real_mult x x) (real_mult y y) n).
      setoid_rewrite (sp2_pt_mult x x n).
      setoid_rewrite (sp2_pt_mult y y n).
      setoid_rewrite (sp2_pt_zero n).
      setoid_rewrite sp2_qminus_0_r.
      apply (Qlt_le_trans delta (projT1 x n * projT1 x n)
               (projT1 x n * projT1 x n + projT1 y n * projT1 y n)).
      * exact K.
      * exact (sp2_qle_plus_r _ _ (sp2_qsq_nonneg _)).
  - destruct Hxy as [delta [Hdelta [N HN]]].
    exists delta. split.
    + exact Hdelta.
    + exists N. intros n Hn.
      pose proof (QltT_to_Qlt _ _ (HN n Hn)) as K.
      setoid_rewrite (sp2_pt_mult y y n) in K.
      setoid_rewrite (sp2_pt_zero n) in K.
      setoid_rewrite sp2_qminus_0_r in K.
      apply Qlt_to_QltT.
      setoid_rewrite (sp2_pt_plus (real_mult x x) (real_mult y y) n).
      setoid_rewrite (sp2_pt_mult x x n).
      setoid_rewrite (sp2_pt_mult y y n).
      setoid_rewrite (sp2_pt_zero n).
      setoid_rewrite sp2_qminus_0_r.
      apply (Qlt_le_trans delta (projT1 y n * projT1 y n)
               (projT1 x n * projT1 x n + projT1 y n * projT1 y n)).
      * exact K.
      * exact (sp2_qle_plus_l _ _ (sp2_qsq_nonneg _)).
Qed.

Corollary sp2_disc_pos_of_sq : forall a d b : Real,
  real_lt real_zero (real_mult (real_plus a (real_opp d)) (real_plus a (real_opp d))) ->
  real_lt real_zero (sp2_disc a d b).
Proof.
  intros a d b H.
  exact (sp2_disc_pos_gen (real_plus a (real_opp d)) (real_plus b b) (inl H)).
Qed.

Corollary sp2_disc_pos_of_bsq : forall a d b : Real,
  real_lt real_zero (real_mult (real_plus b b) (real_plus b b)) ->
  real_lt real_zero (sp2_disc a d b).
Proof.
  intros a d b H.
  exact (sp2_disc_pos_gen (real_plus a (real_opp d)) (real_plus b b) (inr H)).
Qed.

(* ============================================================ *)
(* ================= Section 2B. The explicit rational-layer Newton rate for *)
(*    the square root of the discriminant (multiplicative invariant, division-free) ================= *)
(*   Range D in [1, 4], start x0 = 2, invariant gap_n * 4^n <= 3; the exit *)
(*   face is QleT'.  The general scaled-input form carrying a QeqT witness is *)
(*   not encoded here; the recorded form covers the normalized range directly. *)
(* ============================================================ *)

Definition sp2_qdisc (a d b : Q) : Q := (a - d) * (a - d) + 4 * b * b.
Definition sp2_qnewton_step (D x : Q) : Q := (x + D/x)/2.
Fixpoint sp2_qnewton (D x : Q) (n : nat) : Q :=
  match n with
  | Datatypes.O => x
  | Datatypes.S m => sp2_qnewton_step D (sp2_qnewton D x m)
  end.
Fixpoint sp2_q4pow (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S m => 4 * sp2_q4pow m
  end.
Definition sp2_qgap (D x : Q) : Q := x * x - D.

Lemma sp2_qnewton_0 : forall D x : Q, sp2_qnewton D x 0 == x.
Proof. intros D x. exact (Qeq_refl x). Qed.

Lemma sp2_qnewton_S : forall (D x : Q) (n : nat),
  sp2_qnewton D x (Datatypes.S n) == sp2_qnewton_step D (sp2_qnewton D x n).
Proof. intros D x n. exact (Qeq_refl (sp2_qnewton_step D (sp2_qnewton D x n))). Qed.

Lemma sp2_q4pow_S : forall n : nat, sp2_q4pow (Datatypes.S n) == 4 * sp2_q4pow n.
Proof. intros n. exact (Qeq_refl (4 * sp2_q4pow n)%Q). Qed.

Lemma sp2_q4pow_0 : sp2_q4pow 0 == 1%Q.
Proof. exact (Qeq_refl 1%Q). Qed.

Lemma sp2_q4pow_pos : forall n : nat, Qle 1 (sp2_q4pow n).
Proof.
  induction n as [| m IHm].
  - apply Qle_refl.
  - apply (Qle_trans 1%Q 4%Q (4 * sp2_q4pow m)%Q).
    + apply Qlt_le_weak. exact sp2_qlt_lit4.
    + exact (sp2_qle_eq_l (4 * 1)%Q 4%Q (4 * sp2_q4pow m)%Q
               (Qeq_sym _ _ (Qmult_1_l 4))
               (sp2_qmult_le_compat_l 1%Q (sp2_q4pow m) 4%Q IHm sp2_qle_lit0_4)).
Qed.

Lemma sp2_q4pow_nn : forall n : nat, Qle 0 (sp2_q4pow n).
Proof.
  intros n.
  apply (Qle_trans 0%Q 1%Q (sp2_q4pow n)).
  - exact sp2_qle_lit1.
  - exact (sp2_q4pow_pos n).
Qed.

Lemma sp2_qgap_E : forall D x : Q, sp2_qgap D x == (x * x - D)%Q.
Proof. intros D x. exact (Qeq_refl (x * x - D)%Q). Qed.

Lemma sp2_qgap_ge0 : forall D x : Q, Qle D (x * x) -> Qle 0 (sp2_qgap D x).
Proof.
  intros D x H.
  assert (Ha : (D + - D == 0)%Q) by ring.
  assert (Hb : (x * x + - D == sp2_qgap D x)%Q) by (unfold sp2_qgap; ring).
  exact (sp2_qle_eq_r 0%Q (x * x + - D)%Q (sp2_qgap D x) (Qeq_sym _ _ Hb)
           (sp2_qle_eq_l (D + - D)%Q 0%Q (x * x + - D)%Q (Qeq_sym _ _ Ha)
              (Qplus_le_compat _ _ _ _ H (Qle_refl (- D)%Q)))).
Qed.

Lemma sp2_qle1_neq0 : forall x : Q, Qle 1 x -> ~ (x == 0)%Q.
Proof.
  intros x H Hz.
  apply (Qlt_irrefl 0%Q).
  apply (Qlt_le_trans 0%Q 1%Q 0%Q).
  - exact sp2_qlt_lit1.
  - apply (Qle_trans 1%Q x%Q 0%Q).
    + exact H.
    + apply sp2_qeq_le. exact Hz.
Qed.

(* Newton step residual identity: the residual of the step times 4 * x * x *)
(* equals the squared residual of the input; one field-solve under x != 0. *)
Lemma sp2_qstep_gap : forall D x : Q, ~ (x == 0)%Q ->
  Qeq ((sp2_qnewton_step D x * sp2_qnewton_step D x - D) * (4 * x * x))
      ((x * x - D) * (x * x - D)).
Proof.
  intros D x Hx.
  unfold sp2_qnewton_step.
  field.
  assumption.
Qed.

(* Inductive bounds on the normalized scale x0 = 2: 0 < x_n, 1 <= x_n and *)
(* D <= x_n^2 hold at every depth. *)
Lemma sp2_qnewton_bnd : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat,
    And (QltT 0 (sp2_qnewton D 2 n))
        (And (QleT' 1 (sp2_qnewton D 2 n))
             (QleT' D (sp2_qnewton D 2 n * sp2_qnewton D 2 n))).
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - split; [exact (Qlt_to_QltT _ _ sp2_qlt_lit2) | split].
    + apply Qle_to_QleT'. unfold Qle. cbn. lia.
    + exact (Qle_to_QleT' _ _ HD4).
  - destruct IHm as [Hpos [H1le HDle]].
    assert (Hx0 := sp2_qle1_neq0 (sp2_qnewton D 2 m) (QleT'_to_Qle _ _ H1le)).
    assert (H1xx : Qle 1%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
    { exact (Qle_trans 1%Q D%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q HD1 (QleT'_to_Qle _ _ HDle)). }
    assert (H4pos : Qlt 0 (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
    { apply (sp2_qlt_wd (0 * 4)%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m * 4)%Q
                        0%Q (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q).
      - ring.
      - ring.
      - exact (Qmult_lt_compat_r 0%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q 4%Q
                 sp2_qlt_lit4
                 (Qlt_le_trans 0%Q 1%Q (sp2_qnewton D 2 m * sp2_qnewton D 2 m)
                    sp2_qlt_lit1 H1xx)). }
    assert (HDpos : Qlt 0 D%Q).
    { apply (Qlt_le_trans 0%Q 1%Q D%Q sp2_qlt_lit1 HD1). }
    assert (Hdx : Qlt 0 (D / sp2_qnewton D 2 m)%Q).
    { apply (sp2_qlt_wd (0 * / sp2_qnewton D 2 m)%Q (D * / sp2_qnewton D 2 m)%Q
                        0%Q (D / sp2_qnewton D 2 m)%Q).
      - ring.
      - reflexivity.
      - exact (Qmult_lt_compat_r 0%Q D%Q (/ sp2_qnewton D 2 m)%Q
                 (Qinv_lt_0_compat (sp2_qnewton D 2 m) (QltT_to_Qlt _ _ Hpos)) HDpos). }
    assert (Hspos : Qlt 0 (sp2_qnewton_step D (sp2_qnewton D 2 m))).
    { apply (sp2_qlt_wd (0 * (1#2))%Q
                        ((sp2_qnewton D 2 m + D / sp2_qnewton D 2 m) * (1#2))%Q
                        0%Q ((sp2_qnewton D 2 m + D / sp2_qnewton D 2 m) * (1#2))%Q).
      - ring.
      - reflexivity.
      - exact (Qmult_lt_compat_r 0%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q (1#2)
                 (Qinv_lt_0_compat 2%Q sp2_qlt_lit2)
                 (sp2_qlt_wd (0 + 0)%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q
                             0%Q (sp2_qnewton D 2 m + D / sp2_qnewton D 2 m)%Q
                             (Qplus_0_l 0) (Qeq_refl _)
                             (Qplus_lt_compat _ _ _ _ (QltT_to_Qlt _ _ Hpos) Hdx))). }
    assert (Hgap' : Qle 0 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)))).
    { destruct (Qlt_le_dec (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m))) 0%Q)
        as [Hc | Hc].
      - exfalso.
        pose proof (sp2_qstep_gap D (sp2_qnewton D 2 m) Hx0) as Hid.
        apply (Qlt_irrefl ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                            * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q).
        apply (Qlt_le_trans ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                              * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q
                            0%Q
                            ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                             * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q).
        + apply (sp2_qlt_wd
                   (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m))
                    * (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))%Q
                   (0 * (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))%Q
                   ((sp2_qnewton D 2 m * sp2_qnewton D 2 m - D)
                    * (sp2_qnewton D 2 m * sp2_qnewton D 2 m - D))%Q
                   0%Q
                   Hid (Qmult_0_l (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m))
                   (Qmult_lt_compat_r (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)))
                      0%Q (4 * sp2_qnewton D 2 m * sp2_qnewton D 2 m)%Q H4pos Hc)).
        + apply sp2_qsq_nonneg.
      - exact Hc. }
    assert (HDle' : Qle D%Q (sp2_qnewton_step D (sp2_qnewton D 2 m)
                              * sp2_qnewton_step D (sp2_qnewton D 2 m))).
    { apply (Qle_trans D%Q
              (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)) + D)%Q
              (sp2_qnewton_step D (sp2_qnewton D 2 m)
               * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      - exact (sp2_qle_eq_l (0 + D)%Q D%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 m)) + D)%Q
                 (Qeq_sym _ _ (Qplus_0_l D))
                 (Qplus_le_compat _ _ _ _ Hgap' (Qle_refl D))).
      - apply sp2_qeq_le.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton_step D (sp2_qnewton D 2 m))).
        ring. }
    destruct (Qlt_le_dec (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q) as [Hlt' | H1le'].
    + exfalso.
      assert (Hxxlt : Qlt (sp2_qnewton_step D (sp2_qnewton D 2 m)
                            * sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q).
      { apply (Qlt_trans (sp2_qnewton_step D (sp2_qnewton D 2 m)
                           * sp2_qnewton_step D (sp2_qnewton D 2 m))
                         (1 * sp2_qnewton_step D (sp2_qnewton D 2 m))%Q 1%Q).
        - exact (Qmult_lt_compat_r (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                   (sp2_qnewton_step D (sp2_qnewton D 2 m)) Hspos Hlt').
        - exact (sp2_qlt_wd (sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                            (1 * sp2_qnewton_step D (sp2_qnewton D 2 m))%Q 1%Q
                            (Qeq_sym _ _ (Qmult_1_l (sp2_qnewton_step D (sp2_qnewton D 2 m))))
                            (Qeq_refl 1) Hlt'). }
      pose proof (Qle_trans 1%Q D%Q (sp2_qnewton_step D (sp2_qnewton D 2 m)
                                  * sp2_qnewton_step D (sp2_qnewton D 2 m))
                    HD1 HDle') as H1xx'.
      apply (Qlt_irrefl (sp2_qnewton_step D (sp2_qnewton D 2 m)
                          * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      apply (Qlt_le_trans (sp2_qnewton_step D (sp2_qnewton D 2 m)
                            * sp2_qnewton_step D (sp2_qnewton D 2 m)) 1%Q
                          (sp2_qnewton_step D (sp2_qnewton D 2 m)
                           * sp2_qnewton_step D (sp2_qnewton D 2 m))).
      * exact Hxxlt.
      * exact H1xx'.
    + split; [exact (Qlt_to_QltT _ _ Hspos) | split; [exact (Qle_to_QleT' _ _ H1le') | exact (Qle_to_QleT' _ _ HDle')]].
Qed.


(* Step preservation of gap <= 1, by contradiction: 1 <= gap(step x) gives *)
(* 4 x^2 <= gap(step x) * 4 x^2 == gap^2 <= 1, against 4 <= 4 x^2. *)
Lemma sp2_qgap_le1_S : forall D x : Q,
  Qle 1 x -> Qlt 0 x -> Qle D (x * x) -> Qle (sp2_qgap D x) 1 ->
  Qle (sp2_qgap D (sp2_qnewton_step D x)) 1.
Proof.
  intros D x H1le Hpos HDle Hg.
  destruct (Qlt_le_dec 1%Q (sp2_qgap D (sp2_qnewton_step D x))) as [Hc | Hc].
  - exfalso.
    assert (Hx0 := sp2_qle1_neq0 x H1le).
    assert (Hxx : Qle 1%Q (x * x)%Q).
    { exact (Qle_trans 1%Q x%Q (x * x)%Q H1le
               (sp2_qle_eq_l (1 * x)%Q x%Q (x * x)%Q (Qeq_sym _ _ (Qmult_1_l x))
                  (Qmult_le_compat_r 1%Q x%Q x%Q H1le (Qlt_le_weak _ _ Hpos)))). }
    assert (Hr4 : (x * x * 4 == 4 * x * x)%Q) by ring.
    assert (H4le : Qle 4%Q (4 * x * x)%Q).
    { exact (sp2_qle_eq_r 4%Q (x * x * 4)%Q (4 * x * x)%Q (Qeq_sym _ _ Hr4)
               (sp2_qle_eq_l (1 * 4)%Q 4%Q (x * x * 4)%Q (Qeq_sym _ _ (Qmult_1_l 4))
                  (Qmult_le_compat_r 1%Q (x * x)%Q 4%Q Hxx sp2_qle_lit0_4))). }
    assert (H0_4xx : Qle 0%Q (4 * x * x)%Q).
    { exact (Qle_trans 0%Q 4%Q (4 * x * x)%Q sp2_qle_lit0_4 H4le). }
    assert (Hg0 : Qle 0 (sp2_qgap D x)) by (apply sp2_qgap_ge0; exact HDle).
    assert (Hgap2le : Qle (sp2_qgap D x * sp2_qgap D x) 1%Q).
    { apply (Qle_trans (sp2_qgap D x * sp2_qgap D x)
              (1 * sp2_qgap D x)%Q 1%Q).
      - exact (Qmult_le_compat_r (sp2_qgap D x) 1%Q (sp2_qgap D x) Hg Hg0).
      - apply (Qle_trans (1 * sp2_qgap D x)%Q (sp2_qgap D x) 1%Q).
        + apply sp2_qeq_le. exact (Qmult_1_l (sp2_qgap D x)).
        + exact Hg. }
    assert (Hchain : Qle (4 * x * x) (sp2_qgap D x * sp2_qgap D x)).
    { exact (sp2_qle_eq_r (4 * x * x)%Q
               (sp2_qgap D (sp2_qnewton_step D x) * (4 * x * x))%Q
               (sp2_qgap D x * sp2_qgap D x)%Q
               (Qeq_sym _ _ (sp2_qstep_gap D x Hx0))
               (sp2_qle_eq_l (1 * (4 * x * x))%Q (4 * x * x)%Q
                  (sp2_qgap D (sp2_qnewton_step D x) * (4 * x * x))%Q
                  (Qeq_sym _ _ (Qmult_1_l (4 * x * x)))
                  (Qmult_le_compat_r 1%Q (sp2_qgap D (sp2_qnewton_step D x))
                     (4 * x * x) (Qlt_le_weak _ _ Hc) H0_4xx))). }
    apply (Qlt_irrefl 1%Q).
    apply (Qlt_le_trans 1%Q 4%Q 1%Q).
    + exact sp2_qlt_lit1_4.
    + apply (Qle_trans 4%Q (4 * x * x)%Q 1%Q).
      * exact H4le.
      * exact (Qle_trans (4 * x * x)%Q (sp2_qgap D x * sp2_qgap D x)%Q 1%Q
                 Hchain Hgap2le).
  - exact Hc.
Qed.

(* Base case gap_1 <= 1 on the x0 = 2 scale: gap_1 * 16 == gap_0^2 <= 9 < 16, *)
(* by contradiction. *)
Lemma sp2_qgap1_le1 : forall D : Q, Qle 1 D -> Qle D 4 ->
  Qle (sp2_qgap D (sp2_qnewton D 2 1)) 1.
Proof.
  intros D HD1 HD4.
  destruct (Qlt_le_dec 1%Q (sp2_qgap D (sp2_qnewton D 2 1))) as [Hc | Hc].
  - exfalso.
    assert (Hx0 : ~ (2%Q == 0)%Q).
    { intro Hz. apply (Qlt_irrefl 0%Q).
        exact (sp2_qlt_wd 0%Q 2%Q 0%Q 0%Q (Qeq_refl 0) Hz sp2_qlt_lit2). }
    pose proof (sp2_qstep_gap D 2%Q Hx0) as Hid.
    assert (HD4' : Qle D (2 * 2)%Q) by exact HD4.
    assert (Hg0 : Qle 0 (sp2_qgap D 2%Q)) by (apply sp2_qgap_ge0; exact HD4').
    assert (Hg0le3 : Qle (sp2_qgap D 2%Q) 3%Q).
    { apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
      - exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q) (Qopp_le_compat 1%Q D%Q HD1)).
      - apply sp2_qeq_le. reflexivity. }
    assert (Hg0sq : Qle (sp2_qgap D 2%Q * sp2_qgap D 2%Q) 9%Q).
    { apply (Qle_trans (sp2_qgap D 2%Q * sp2_qgap D 2%Q)
              (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q).
      - exact (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q (sp2_qgap D 2%Q) Hg0le3 Hg0).
      - assert (Hr9 : (3 * sp2_qgap D 2%Q == sp2_qgap D 2%Q * 3)%Q) by ring.
        exact (sp2_qle_eq_l (sp2_qgap D 2%Q * 3)%Q (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q Hr9
                 (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q 3%Q Hg0le3 sp2_qle_lit3)). }
    assert (H16 : Qle 16%Q (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q).
    { exact (sp2_qle_eq_l (1 * 16)%Q 16%Q
               (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
               (Qeq_sym _ _ (Qmult_1_l 16))
               (Qmult_le_compat_r 1%Q (sp2_qgap D (sp2_qnewton D 2 1)) 16%Q (Qlt_le_weak _ _ Hc)
                  sp2_qle_lit0_16)). }
    apply (Qlt_irrefl 9%Q).
    apply (Qlt_le_trans 9%Q 16%Q 9%Q).
    + exact sp2_qlt_lit9_16.
    + apply (Qle_trans 16%Q (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q 9%Q).
      * exact H16.
      * apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
                 (sp2_qgap D 2%Q * sp2_qgap D 2%Q)%Q 9%Q).
        -- apply sp2_qeq_le.
           assert (Hg1 : sp2_qgap D (sp2_qnewton D 2 1)
                         == (sp2_qnewton_step D 2 * sp2_qnewton_step D 2 - D)%Q)
             by (exact (sp2_qgap_E D (sp2_qnewton_step D 2%Q))).
           assert (Hg0e : sp2_qgap D 2%Q == (2 * 2 - D)%Q)
             by (exact (sp2_qgap_E D 2%Q)).
           setoid_rewrite Hg1.
           setoid_rewrite Hg0e.
           setoid_rewrite (Qeq_sym _ _ Hid).
           ring.
        -- exact Hg0sq.
  - exact Hc.
Qed.

(* Induction: gap_n <= 1 for every n >= 1. *)
Lemma sp2_qgap_le1 : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat, Qle (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S n))) 1.
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - exact (sp2_qgap1_le1 D HD1 HD4).
  - destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S m)) as [Hpos [H1le HDle]].
    exact (sp2_qgap_le1_S D (sp2_qnewton D 2 (Datatypes.S m)) (QleT'_to_Qle _ _ H1le) (QltT_to_Qlt _ _ Hpos) (QleT'_to_Qle _ _ HDle) IHm).
Qed.

(* Main rate through the multiplicative invariant: gap_n * 4^n <= 3; the *)
(*   chain is division-free and uses no Or case split.  The step reassociates *)
(*   gap(step x) * (4 * 4^m) == (gap x * 4^m) * gap x <= 3 * gap x <= 3, *)
(*   transported throughout by sp2_qle_eq_l / sp2_qle_eq_r. *)

Theorem sp2_sqrt_rate_core : forall D : Q, Qle 1 D -> Qle D 4 ->
  forall n : nat, Qle (sp2_qgap D (sp2_qnewton D 2 n) * sp2_q4pow n) 3%Q.
Proof.
  intros D HD1 HD4 n.
  induction n as [| m IHm].
  - (* Base case n = 0: gap_0 * 4^0 == 4 - D <= 3 follows from 1 <= D. *)
    apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 0) * sp2_q4pow 0)%Q
              (sp2_qgap D 2%Q) 3%Q).
    + apply sp2_qeq_le.
      apply (Qeq_trans (sp2_qgap D (sp2_qnewton D 2 0) * sp2_q4pow 0)%Q
              ((sp2_qnewton D 2 0 * sp2_qnewton D 2 0 - D) * 1%Q)%Q
              (sp2_qgap D 2%Q)).
      * setoid_rewrite (sp2_qgap_E D (sp2_qnewton D 2 0)).
        setoid_rewrite sp2_q4pow_0.
        ring.
      * setoid_rewrite (sp2_qnewton_0 D 2%Q).
        setoid_rewrite (sp2_qgap_E D 2%Q).
        ring.
    + apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
      * exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q)
                 (Qopp_le_compat 1%Q D%Q HD1)).
      * apply sp2_qeq_le. reflexivity.
  - destruct m as [| m'].
    + (* Case n = 1: 3 < gap_1 * 4 would give 12 < gap_1 * 16 == gap_0^2 <= 9, *)
      (* against 9 < 12. *)
      destruct (Qlt_le_dec (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1)%Q 3%Q)
        as [H | H].
      * exact (Qlt_le_weak _ _ H).
      * exfalso.
        assert (Hx0 : ~ (2%Q == 0)%Q).
        { intro Hz. apply (Qlt_irrefl 0%Q).
        exact (sp2_qlt_wd 0%Q 2%Q 0%Q 0%Q (Qeq_refl 0) Hz sp2_qlt_lit2). }
        pose proof (sp2_qstep_gap D 2%Q Hx0) as Hid.
        assert (HD4' : Qle D (2 * 2)%Q) by exact HD4.
        assert (Hg0 : Qle 0 (sp2_qgap D 2%Q)) by (apply sp2_qgap_ge0; exact HD4').
        assert (Hg0le3 : Qle (sp2_qgap D 2%Q) 3%Q).
        { apply (Qle_trans (sp2_qgap D 2%Q) (2 * 2 + - 1)%Q 3%Q).
          - exact (Qplus_le_compat _ _ _ _ (Qle_refl (2 * 2)%Q)
                     (Qopp_le_compat 1%Q D%Q HD1)).
          - apply sp2_qeq_le. reflexivity. }
        assert (Hg0sq : Qle (sp2_qgap D 2%Q * sp2_qgap D 2%Q) 9%Q).
        { apply (Qle_trans (sp2_qgap D 2%Q * sp2_qgap D 2%Q)
                  (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q).
          - exact (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q (sp2_qgap D 2%Q)
                     Hg0le3 Hg0).
          - assert (Hr9 : (3 * sp2_qgap D 2%Q == sp2_qgap D 2%Q * 3)%Q) by ring.
            exact (sp2_qle_eq_l (sp2_qgap D 2%Q * 3)%Q (3 * sp2_qgap D 2%Q)%Q (3 * 3)%Q Hr9
                     (Qmult_le_compat_r (sp2_qgap D 2%Q) 3%Q 3%Q Hg0le3 sp2_qle_lit3)). }
        apply (Qlt_irrefl 9%Q).
        apply (Qlt_le_trans 9%Q (3 * 4)%Q 9%Q).
        -- exact sp2_qlt_lit9_12.
        -- apply (Qle_trans (3 * 4)%Q
                     (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1 * 4)%Q 9%Q).
           ++ exact (Qmult_le_compat_r 3%Q
                       (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1)%Q 4%Q
                       H sp2_qle_lit0_4).
           ++ apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * sp2_q4pow 1 * 4)%Q
                       (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q 9%Q).
              ** apply sp2_qeq_le.
                 setoid_rewrite (sp2_q4pow_S 0).
                 setoid_rewrite sp2_q4pow_0.
                 ring.
              ** apply (Qle_trans (sp2_qgap D (sp2_qnewton D 2 1) * 16)%Q
                         ((2 * 2 - D) * (2 * 2 - D))%Q 9%Q).
                 *** apply sp2_qeq_le.
                     assert (Hg1 : sp2_qgap D (sp2_qnewton D 2 1)
                                   == (sp2_qnewton_step D 2 * sp2_qnewton_step D 2 - D)%Q)
                       by (exact (sp2_qgap_E D (sp2_qnewton_step D 2%Q))).
                     setoid_rewrite Hg1.
                     setoid_rewrite (Qeq_sym _ _ Hid).
                     ring.
                 *** exact Hg0sq.
    + (* Main chain at n = S (Datatypes.S m'), with x := sp2_qnewton D 2 (S m'): *)
      (* gap(step x) * (4 * 4^m) <= gap(step x) * ((4 * x^2) * 4^m) *)
      (* == (gap x * 4^m) * gap x <= 3 * gap x <= 3, from the ring-reshaped *)
      (* identity, the induction premise, and gap x <= 1. *)
      destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S m')) as [Hpos [H1le HDle]].
      destruct (sp2_qnewton_bnd D HD1 HD4 (Datatypes.S (Datatypes.S m')))
        as [_ [_ HDle2]].
      pose proof (sp2_qgap_le1 D HD1 HD4 m') as Hg1.
      assert (Hx0 := sp2_qle1_neq0 (sp2_qnewton D 2 (Datatypes.S m')) (QleT'_to_Qle _ _ H1le)).
      pose proof (sp2_qstep_gap D (sp2_qnewton D 2 (Datatypes.S m')) Hx0) as Hid.
      assert (Hgx0 : Qle 0 (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))))
        by (apply sp2_qgap_ge0; exact (QleT'_to_Qle _ _ HDle)).
      assert (Hgw0 : Qle 0 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))))
        by (apply sp2_qgap_ge0; exact (QleT'_to_Qle _ _ HDle2)).
      assert (Hxx : Qle 1%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q).
      { exact (Qle_trans 1%Q D%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 HD1 (QleT'_to_Qle _ _ HDle)). }
      assert (H4le : Qle 4%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q).
      { assert (Hr4 : (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4
                        == 4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q)
          by ring.
        exact (sp2_qle_eq_r 4%Q
                 (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4)%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 (Qeq_sym _ _ Hr4)
                 (sp2_qle_eq_l (1 * 4)%Q 4%Q
                    (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m') * 4)%Q
                    (Qeq_sym _ _ (Qmult_1_l 4))
                    (Qmult_le_compat_r 1%Q
                       (sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q 4%Q
                       Hxx sp2_qle_lit0_4))). }
      assert (Hsc : Qle (4 * sp2_q4pow (Datatypes.S m'))%Q
                        ((4 * sp2_qnewton D 2 (Datatypes.S m')
                          * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))%Q).
      { exact (Qmult_le_compat_r 4%Q
                 (4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))%Q
                 (sp2_q4pow (Datatypes.S m')) H4le (sp2_q4pow_nn (Datatypes.S m'))). }
      assert (HeqBC :
        (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
         * ((4 * sp2_qnewton D 2 (Datatypes.S m') * sp2_qnewton D 2 (Datatypes.S m'))
            * sp2_q4pow (Datatypes.S m')))
        == ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
             * sp2_q4pow (Datatypes.S m'))
            * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))).
      { assert (Hr : (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                      * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                          * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))
                      == (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                          * (4 * sp2_qnewton D 2 (Datatypes.S m')
                             * sp2_qnewton D 2 (Datatypes.S m')))
                         * sp2_q4pow (Datatypes.S m'))%Q)
          by ring.
        setoid_rewrite Hr.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))).
        setoid_rewrite Hid.
        setoid_rewrite (sp2_qgap_E D (sp2_qnewton D 2 (Datatypes.S m'))).
        ring. }
      assert (Hl3 : Qle (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q 3%Q).
      { apply (Qle_trans (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q
                (3 * 1)%Q 3%Q).
        - exact (sp2_qmult_le_compat_l
                   (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) 1%Q 3%Q
                   Hg1 sp2_qle_lit3).
        - apply sp2_qeq_le. reflexivity. }
      assert (Hce : Qle ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                           * sp2_q4pow (Datatypes.S m'))
                          * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) 3%Q).
      { apply (Qle_trans _
                (3 * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q 3%Q).
        - exact (Qmult_le_compat_r
                   (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                    * sp2_q4pow (Datatypes.S m'))%Q
                   3%Q (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))) IHm Hgx0).
        - exact Hl3. }
      apply (Qle_trans
              (sp2_qgap D (sp2_qnewton D 2 (Datatypes.S (Datatypes.S m')))
               * sp2_q4pow (Datatypes.S (Datatypes.S m')))%Q
              (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
               * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                   * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m')))%Q
              3%Q).
      * exact (sp2_qmult_le_compat_l
                 (4 * sp2_q4pow (Datatypes.S m'))%Q
                 ((4 * sp2_qnewton D 2 (Datatypes.S m')
                   * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m'))%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m'))))
                 Hsc Hgw0).
      * exact (sp2_qle_eq_l
                 ((sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m'))
                   * sp2_q4pow (Datatypes.S m'))
                  * sp2_qgap D (sp2_qnewton D 2 (Datatypes.S m')))%Q
                 (sp2_qgap D (sp2_qnewton_step D (sp2_qnewton D 2 (Datatypes.S m')))
                  * ((4 * sp2_qnewton D 2 (Datatypes.S m')
                      * sp2_qnewton D 2 (Datatypes.S m')) * sp2_q4pow (Datatypes.S m')))%Q
                 3%Q HeqBC Hce).
Qed.

(* Set-face exit of the main rate, carried by QleT' at the recorded exit *)
(*   position.  The Id branch of the right QleT summand is eliminated by *)
(*   destruct; QleT' inputs enter the rational layer through the *)
(*   QleT'_to_Qle bridge. *)

Theorem sp2_sqrt_rate : forall D : Q, QleT 1 D -> QleT' D 4 -> forall n : nat,
  And (QleT' 0 (sp2_qgap D (sp2_qnewton D 2 n)))
      (QleT' (sp2_qgap D (sp2_qnewton D 2 n) * sp2_q4pow n) 3%Q).
Proof.
  intros D HD1 HD4 n.
  assert (Hq1 : Qle 1 D).
  { destruct HD1 as [H | H].
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact H.
    - destruct H. apply Qle_refl. }
  assert (Hq4 : Qle D 4) by (apply QleT'_to_Qle; exact HD4).
  split.
  - apply Qle_to_QleT'.
    apply sp2_qgap_ge0.
    destruct (sp2_qnewton_bnd D Hq1 Hq4 n) as [_ [_ HDle]].
    exact (QleT'_to_Qle _ _ HDle).
  - apply Qle_to_QleT'.
    exact (sp2_sqrt_rate_core D Hq1 Hq4 n).
Qed.

(* ============================================================ *)
(* ================= Section 2C. The main statement sp2_eig_gap, reusing *)
(*    AttnSqrt.real_sqrt_exists as recorded ================= *)
(*   The premise face real_le splits into the strict branch and the *)
(*   degenerate branch D == 0, where s := 0 covers the conclusion outright. *)
(*   Witness shape: s >= 0, s * s == D, and eig_up - eig_dn == s, by the *)
(*   pointwise algebra |X_n - s_n| = 0. *)
(* ============================================================ *)

Definition sp2_half : Real := real_const (1#2).
Definition sp2_eig_up (a d s : Real) : Real :=
  real_plus (real_mult sp2_half (real_plus a d)) (real_mult sp2_half s).
Definition sp2_eig_dn (a d s : Real) : Real :=
  real_plus (real_mult sp2_half (real_plus a d))
            (real_opp (real_mult sp2_half s)).

Lemma sp2_eig_diff_eq : forall a d s : Real,
  real_eq (real_plus (sp2_eig_up a d s) (real_opp (sp2_eig_dn a d s))) s.
Proof.
  intros a d s eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hz : Qabs (projT1 (real_plus (sp2_eig_up a d s)
                                        (real_opp (sp2_eig_dn a d s))) n
                     - projT1 s n) == 0%Q).
  { apply (Qeq_trans _ (Qabs 0%Q) _).
    - apply Qabs_wd.
      setoid_rewrite (sp2_pt_plus (sp2_eig_up a d s) (real_opp (sp2_eig_dn a d s)) n).
      setoid_rewrite (sp2_pt_opp (sp2_eig_dn a d s) n).
      setoid_rewrite (sp2_pt_plus (real_mult sp2_half (real_plus a d)) (real_mult sp2_half s) n).
      setoid_rewrite (sp2_pt_plus (real_mult sp2_half (real_plus a d)) (real_opp (real_mult sp2_half s)) n).
      setoid_rewrite (sp2_pt_mult sp2_half (real_plus a d) n).
      setoid_rewrite (sp2_pt_mult sp2_half s n).
      setoid_rewrite (sp2_pt_opp (real_mult sp2_half s) n).
      setoid_rewrite (sp2_pt_const (1#2) n).
      setoid_rewrite (sp2_pt_plus a d n).
      setoid_rewrite (sp2_pt_mult sp2_half s n).
      setoid_rewrite (sp2_pt_const (1#2) n).
      ring.

    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Hz.
  apply QltT_to_Qlt.
  exact Heps.
Qed.
Theorem sp2_eig_gap : forall a d b : Real,
  real_le real_zero (sp2_disc a d b) ->
  sigT (fun s : Real => And (real_le real_zero s)
        (And (real_eq (real_mult s s) (sp2_disc a d b))
             (real_eq (real_plus (sp2_eig_up a d s)
                                 (real_opp (sp2_eig_dn a d s))) s))).
Proof.
  intros a d b HD.
  destruct (real_sqrt_exists (sp2_disc a d b) HD) as [s [Hpos Hsq]].
  exists s.
  split.
  - exact Hpos.
  - split.
    + exact Hsq.
    + apply sp2_eig_diff_eq.
Qed.

(* ============================================================ *)
(* ================= Section 2E. Two companion statements: the degenerate *)
(*    D = 0 face in eps-uniform form, and strict positivity of s ================= *)
(*   Rational engine: the eta := eps/(4+eps) scale with 0 < eta, eta <= 1 *)
(*   and 2*eta < eps, in place of a squared-fraction scale. *)
(* ============================================================ *)

Lemma sp2_qsq_abs_id : forall u : Q, (u * u == Qabs u * Qabs u)%Q.
Proof.
  intro u.
  destruct (Qlt_le_dec 0 u) as [H | H].
  - setoid_rewrite (Qabs_pos u (Qlt_le_weak _ _ H)). ring.
  - setoid_rewrite (Qabs_neg u H). ring.
Qed.

(* |u| <= eta and eta <= 1 give u * u <= eta * eta; the upper-bound side *)
(* needs no 0 < |u| case split. *)
Lemma sp2_qsq_le_eta : forall u eta : Q, Qle 0 eta -> Qle eta 1 -> Qle (Qabs u) eta ->
  Qle (u * u) (eta * eta).
Proof.
  intros u eta H0e He1 Hub.
  exact (sp2_qle_eq_l (Qabs u * Qabs u)%Q (u * u)%Q (eta * eta)%Q
           (sp2_qsq_abs_id u)
           (Qle_trans (Qabs u * Qabs u)%Q (eta * Qabs u)%Q (eta * eta)%Q
              (Qmult_le_compat_r (Qabs u) eta (Qabs u) Hub (Qabs_nonneg u))
              (sp2_qmult_le_compat_l (Qabs u) eta eta Hub H0e))).
Qed.

(* The eta := eps/(4+eps) scale: 0 < eta, eta <= 1 and 2*eta < eps, from the *)
(* strict 2 < 4 + eps; no case split on squared positivity. *)
Lemma sp2_q_eta_kit : forall e : Q, Qlt 0 e ->
  And (QltT 0 (e/(4+e)))
      (And (QleT' (e/(4+e)) 1) (QltT (2*(e/(4+e))) e)).
Proof.
  intros e He.
  assert (H0e : Qle 0 e) by (apply Qlt_le_weak; exact He).
  assert (H4p : Qlt 0 (4 + e)).
  { exact (Qlt_le_trans 0%Q 4%Q (4+e)%Q sp2_qlt_lit4 (sp2_qle_plus_r 4%Q e%Q H0e)). }
  assert (Hn0 : ~ ((4 + e) == 0)%Q).
  { intro Hz. apply (Qlt_irrefl 0%Q).
    exact (sp2_qlt_wd 0%Q (4+e)%Q 0%Q 0%Q (Qeq_refl 0%Q) Hz H4p). }
  assert (Hηe : (e/(4+e)*(4+e) == e)%Q) by (field; assumption).
  assert (Hηpos : Qlt 0 (e/(4+e))).
  { destruct (Qlt_le_dec 0 (e/(4+e))) as [Hc | Hc].
    - exact Hc.
    - exfalso.
      assert (Hr : (0 == 0 * (4+e))%Q) by ring.
      assert (Hbad : Qle (e/(4+e)*(4+e)) 0%Q).
      { exact (sp2_qle_eq_r _ _ _ Hr
                 (Qmult_le_compat_r (e/(4+e)) 0%Q (4+e)%Q Hc (Qlt_le_weak _ _ H4p))). }
      apply (Qlt_irrefl e%Q).
      exact (Qle_lt_trans e%Q 0%Q e%Q
               (sp2_qle_eq_l (e/(4+e)*(4+e))%Q e%Q 0%Q (Qeq_sym _ _ Hηe) Hbad)
               He). }
  assert (Hreq : (4 + e == e + 4)%Q) by ring.
  assert (Hle4p : Qle e (4 + e)).
  { exact (sp2_qle_eq_r e%Q (e+4)%Q (4+e)%Q Hreq (sp2_qle_plus_r e%Q 4%Q sp2_qle_lit0_4)). }
  assert (Hηle1 : Qle (e/(4+e)) 1).
  { assert (Hηinvpos : Qle 0 (/ (4+e))).
    { apply Qlt_le_weak. exact (Qinv_lt_0_compat (4+e)%Q H4p). }
    exact (sp2_qle_eq_r (e * / (4+e))%Q ((4+e) * / (4+e))%Q 1%Q
             (Qeq_sym _ _ (Qmult_inv_r (4+e)%Q Hn0))
             (Qmult_le_compat_r e%Q (4+e)%Q (/ (4+e)) Hle4p Hηinvpos)). }
  assert (H2lt : Qlt 2%Q (4 + e)).
  { exact (Qlt_le_trans 2%Q 4%Q (4+e)%Q sp2_qlt_lit2 (sp2_qle_plus_r 4%Q e%Q H0e)). }
  assert (Hη2lt : Qlt (2 * (e/(4+e))) e).
  { assert (Hr2 : ((4+e) * (e/(4+e)) == e)%Q).
    { assert (Hc : ((4+e) * (e/(4+e)) == (e/(4+e)) * (4+e))%Q) by ring.
      exact (Qeq_trans _ _ _ Hc Hηe). }
    exact (sp2_qlt_wd (2 * (e/(4+e)))%Q ((4+e) * (e/(4+e)))%Q
             (2 * (e/(4+e)))%Q e%Q (Qeq_refl _) Hr2
             (Qmult_lt_compat_r 2%Q (4+e)%Q (e/(4+e))%Q Hηpos H2lt)). }
  split; [exact (Qlt_to_QltT _ _ Hηpos) | split; [exact (Qle_to_QleT' _ _ Hηle1) | exact (Qlt_to_QltT _ _ Hη2lt)]].
Qed.

(* Degenerate face in eps-uniform form: a - d == 0 and 2*b == 0 give *)
(* D == 0, with the uniform pointwise bound |D_n| < eps. *)
Corollary sp2_disc_eq_zero_of_degen : forall a d b : Real,
  real_eq (real_plus a (real_opp d)) real_zero ->
  real_eq (real_plus b b) real_zero ->
  real_eq (sp2_disc a d b) real_zero.
Proof.
  intros a d b Hu Hb eps Heps.
  pose proof (sp2_q_eta_kit eps (QltT_to_Qlt _ _ Heps)) as [Hη0 [Hη1 Hη2]].
  destruct (Hu (eps/(4+eps))%Q Hη0) as [N1 HN1].
  destruct (Hb (eps/(4+eps))%Q Hη0) as [N2 HN2].
  exists (max N1 N2).
  intros n Hn.
  assert (K1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (K2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  pose proof (QltT_to_Qlt _ _ (HN1 n K1)) as H1q.
  pose proof (QltT_to_Qlt _ _ (HN2 n K2)) as H2q.
  assert (Hx1 : Qabs (projT1 (real_plus a (real_opp d)) n - projT1 real_zero n)
                == Qabs (projT1 a n - projT1 d n)%Q).
  { setoid_rewrite (sp2_pt_plus a (real_opp d) n).
    setoid_rewrite (sp2_pt_opp d n).
    setoid_rewrite (sp2_pt_zero n).
    apply Qabs_wd. ring. }
  assert (H1' : Qlt (Qabs (projT1 a n - projT1 d n)) (eps/(4+eps))%Q)
    by exact (sp2_qlt_wd _ _ _ _ Hx1 (Qeq_refl _) H1q).
  assert (Hx2 : Qabs (projT1 (real_plus b b) n - projT1 real_zero n)
                == Qabs (projT1 b n + projT1 b n)%Q).
  { setoid_rewrite (sp2_pt_plus b b n).
    setoid_rewrite (sp2_pt_zero n).
    apply Qabs_wd. ring. }
  assert (H2' : Qlt (Qabs (projT1 b n + projT1 b n)) (eps/(4+eps))%Q)
    by exact (sp2_qlt_wd _ _ _ _ Hx2 (Qeq_refl _) H2q).
  assert (HDpt : projT1 (sp2_disc a d b) n
                 == (projT1 (real_mult (real_plus a (real_opp d))
                                        (real_plus a (real_opp d))) n
                      + projT1 (real_mult (real_plus b b) (real_plus b b)) n)%Q)
    by exact (sp2_pt_plus _ _ n).
  assert (HDu : projT1 (real_mult (real_plus a (real_opp d))
                                  (real_plus a (real_opp d))) n
                == ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n))%Q).
  { setoid_rewrite (sp2_pt_mult (real_plus a (real_opp d)) (real_plus a (real_opp d)) n).
    setoid_rewrite (sp2_pt_plus a (real_opp d) n).
    setoid_rewrite (sp2_pt_opp d n).
    ring. }
  assert (HDv : projT1 (real_mult (real_plus b b) (real_plus b b)) n
                == ((projT1 b n + projT1 b n) * (projT1 b n + projT1 b n))%Q).
  { setoid_rewrite (sp2_pt_mult (real_plus b b) (real_plus b b) n).
    setoid_rewrite (sp2_pt_plus b b n).
    ring. }
  assert (HDn : projT1 (sp2_disc a d b) n - projT1 real_zero n
                == ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n)
                    + (projT1 b n + projT1 b n) * (projT1 b n + projT1 b n))%Q).
  { setoid_rewrite HDpt. setoid_rewrite HDu. setoid_rewrite HDv.
    setoid_rewrite (sp2_pt_zero n). ring. }
  apply Qlt_to_QltT.
  setoid_rewrite HDn.
  assert (Hη0le : Qle 0 (eps/(4+eps))) by (apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Hη0)).
  assert (Hb1 : Qle (Qabs (projT1 a n - projT1 d n)) (eps/(4+eps)))
    by exact (Qlt_le_weak _ _ H1').
  assert (Hb2 : Qle (Qabs (projT1 b n + projT1 b n)) (eps/(4+eps)))
    by exact (Qlt_le_weak _ _ H2').
  assert (Hs1 : Qle (Qabs (projT1 a n - projT1 d n) * Qabs (projT1 a n - projT1 d n))
                    ((eps/(4+eps)) * (eps/(4+eps))))
    by exact (sp2_qle_eq_l _ _ _
               (Qeq_sym _ _ (sp2_qsq_abs_id (projT1 a n - projT1 d n)))
               (sp2_qsq_le_eta (projT1 a n - projT1 d n) (eps/(4+eps)) Hη0le (QleT'_to_Qle _ _ Hη1) Hb1)).
  assert (Hs2 : Qle (Qabs (projT1 b n + projT1 b n) * Qabs (projT1 b n + projT1 b n))
                    ((eps/(4+eps)) * (eps/(4+eps))))
    by exact (sp2_qle_eq_l _ _ _
               (Qeq_sym _ _ (sp2_qsq_abs_id (projT1 b n + projT1 b n)))
               (sp2_qsq_le_eta (projT1 b n + projT1 b n) (eps/(4+eps)) Hη0le (QleT'_to_Qle _ _ Hη1) Hb2)).
  assert (Hr1 : (eps/(4+eps) == 1 * (eps/(4+eps)))%Q) by ring.
  assert (Hηsqle : Qle ((eps/(4+eps)) * (eps/(4+eps))) (eps/(4+eps)))
    by exact (sp2_qle_eq_r _ _ _ Hr1 (Qmult_le_compat_r (eps/(4+eps)) 1%Q (eps/(4+eps)) (QleT'_to_Qle _ _ Hη1) Hη0le)).
  apply (Qle_lt_trans (Qabs ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n)
                             + (projT1 b n + projT1 b n) * (projT1 b n + projT1 b n)))
                      (Qabs ((projT1 a n - projT1 d n) * (projT1 a n - projT1 d n))
                       + Qabs ((projT1 b n + projT1 b n) * (projT1 b n + projT1 b n)))
                      eps%Q).
  - exact (Qabs_triangle _ _).
  - setoid_rewrite (Qabs_Qmult (projT1 a n - projT1 d n) (projT1 a n - projT1 d n)).
    setoid_rewrite (Qabs_Qmult (projT1 b n + projT1 b n) (projT1 b n + projT1 b n)).
    apply (Qle_lt_trans (Qabs (projT1 a n - projT1 d n) * Qabs (projT1 a n - projT1 d n)
                         + Qabs (projT1 b n + projT1 b n) * Qabs (projT1 b n + projT1 b n))
                        (2 * (eps/(4+eps)))%Q eps%Q).
    + apply (Qle_trans _ ((eps/(4+eps)) * (eps/(4+eps))
                           + (eps/(4+eps)) * (eps/(4+eps)))%Q (2 * (eps/(4+eps)))%Q).
      * exact (Qplus_le_compat _ _ _ _ Hs1 Hs2).
      * apply (Qle_trans _ ((eps/(4+eps)) + (eps/(4+eps)))%Q (2 * (eps/(4+eps)))%Q).
        -- exact (Qplus_le_compat _ _ _ _ Hηsqle Hηsqle).
        -- apply sp2_qeq_le. ring.
    + exact (QltT_to_Qlt _ _ Hη2).
Qed.

(* Strict-positivity corollary: strict 0 < D makes the eigen-gap witness s *)
(*   strictly positive.  The equal branch s == 0 is refuted: s^2 == 0 in the *)
(*   eps-uniform sense gives D == 0, against strict 0 < D. *)
Corollary sp2_eig_s_pos : forall a d b : Real,
  real_lt real_zero (sp2_disc a d b) ->
  sigT (fun s : Real => And (real_lt real_zero s)
        (And (real_eq (real_mult s s) (sp2_disc a d b))
             (real_eq (real_plus (sp2_eig_up a d s)
                                 (real_opp (sp2_eig_dn a d s))) s))).
Proof.
  intros a d b Hlt.
  destruct (sp2_eig_gap a d b (inl Hlt)) as [s [Hpos [Hsq Heig]]].
  exists s.
  destruct Hpos as [Hslt | Hseq].
  - split; [exact Hslt | split; [exact Hsq | exact Heig]].
  - exfalso.
    assert (Hss0 : real_eq (real_mult s s) real_zero).
    { intros eps2 Heps2.
      pose proof (sp2_q_eta_kit eps2 (QltT_to_Qlt _ _ Heps2)) as [Hη0 [Hη1 Hη2]].
      destruct (Hseq (eps2/(4+eps2))%Q Hη0) as [M HM].
      exists M. intros m Hm.
      pose proof (QltT_to_Qlt _ _ (HM m Hm)) as Habs0.
      assert (Hxs : Qabs (projT1 real_zero m - projT1 s m) == Qabs (- projT1 s m)%Q).
      { setoid_rewrite (sp2_pt_zero m). apply Qabs_wd. ring. }
      assert (Habs : Qlt (Qabs (- projT1 s m)) (eps2/(4+eps2))%Q)
        by exact (sp2_qlt_wd _ _ _ _ Hxs (Qeq_refl _) Habs0).
      assert (Habs' : Qlt (Qabs (projT1 s m)) (eps2/(4+eps2))%Q).
      { exact (sp2_qlt_wd (Qabs (- projT1 s m))%Q (eps2/(4+eps2))%Q
                 (Qabs (projT1 s m))%Q (eps2/(4+eps2))%Q
                 (Qabs_opp (projT1 s m)) (Qeq_refl _) Habs). }
      assert (Hη0le : Qle 0 (eps2/(4+eps2))) by (apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Hη0)).
      assert (Hb1 : Qle (Qabs (projT1 s m)) (eps2/(4+eps2)))
        by exact (Qlt_le_weak _ _ Habs').
      assert (Hpt : projT1 (real_mult s s) m - projT1 real_zero m
                    == (projT1 s m * projT1 s m)%Q).
      { setoid_rewrite (sp2_pt_mult s s m). setoid_rewrite (sp2_pt_zero m). ring. }
      assert (H12 : Qle 1 2) by (unfold Qle; cbn; lia).
      apply Qlt_to_QltT.
      setoid_rewrite Hpt.
      apply (Qle_lt_trans (Qabs (projT1 s m * projT1 s m)) (2*(eps2/(4+eps2)))%Q eps2%Q).
      - apply (Qle_trans (Qabs (projT1 s m * projT1 s m)) (eps2/(4+eps2))%Q
                 (2*(eps2/(4+eps2)))%Q).
        + apply (proj2 (Qabs_Qle_condition (projT1 s m * projT1 s m) (eps2/(4+eps2)))).
          split.
          * assert (Hr0 : (0 == - 0)%Q) by ring.
            exact (Qle_trans (- (eps2/(4+eps2)))%Q 0%Q (projT1 s m * projT1 s m)%Q
                     (sp2_qle_eq_r (- (eps2/(4+eps2)))%Q (- 0)%Q 0%Q Hr0
                        (Qopp_le_compat 0%Q (eps2/(4+eps2)) Hη0le))
                     (sp2_qsq_nonneg (projT1 s m))).
          * assert (Hr1b : (eps2/(4+eps2) == 1 * (eps2/(4+eps2)))%Q) by ring.
            exact (Qle_trans (projT1 s m * projT1 s m)
                     ((eps2/(4+eps2)) * (eps2/(4+eps2)))
                     (eps2/(4+eps2))
                     (sp2_qsq_le_eta (projT1 s m) (eps2/(4+eps2)) Hη0le (QleT'_to_Qle _ _ Hη1) Hb1)
                     (sp2_qle_eq_r _ _ _ Hr1b
                        (Qmult_le_compat_r (eps2/(4+eps2)) 1%Q (eps2/(4+eps2))
                           (QleT'_to_Qle _ _ Hη1) Hη0le))).
        + assert (Hr2 : (2 * (eps2/(4+eps2)) == (eps2/(4+eps2)) * 2)%Q) by ring.
          assert (Hr3 : ((eps2/(4+eps2)) == (eps2/(4+eps2)) * 1)%Q) by ring.
          exact (sp2_qle_eq_l ((eps2/(4+eps2)) * 1)%Q (eps2/(4+eps2))%Q
                   (2 * (eps2/(4+eps2)))%Q Hr3
                   (sp2_qle_eq_r _ _ _ Hr2
                      (sp2_qmult_le_compat_l 1%Q 2%Q (eps2/(4+eps2)) H12 Hη0le))).
      - exact (QltT_to_Qlt _ _ Hη2). }
    assert (HD0 : real_eq (sp2_disc a d b) real_zero).
    { exact (real_eq_trans (sp2_disc a d b) (real_mult s s) real_zero
               (real_eq_sym (real_mult s s) (sp2_disc a d b) Hsq) Hss0). }
    destruct (real_lt_irrefl real_zero
               (real_lt_eq_lt real_zero (sp2_disc a d b) real_zero Hlt HD0)).
Qed.


(* ============================================================ *)
(* ================= Section 2D. Scalar-only Separate Extraction check (no *)
(*    Obj.magic may appear) and the Print Assumptions audit of every exit *)
(*    statement (all Closed) ================= *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sp2_qdisc sp2_qnewton_step sp2_qnewton sp2_q4pow sp2_qgap.

Print Assumptions sp2_disc_sqpos.
Print Assumptions sp2_sqrt_rate_core.
Print Assumptions sp2_sqrt_rate.
Print Assumptions sp2_eig_gap.
Print Assumptions sp2_disc_eq_zero_of_degen.
Print Assumptions sp2_eig_s_pos.

(*                                                                *)
(* Design notes.  Proof shapes recorded for the statements of this *)
(*   module and for sibling forms not encoded here; each such note *)
(*   says plainly which side it belongs to.                        *)
(*                                                                *)
(* Rational toolkit notes (sibling forms not encoded in this file). *)
(* sp2_qsq_le_abs : |x| < eta gives x * x <= eta * eta, by the two *)
(*   branches of Qlt_le_dec 0 x; the positive branch quotes Qabs_pos *)
(*   and the negative branch Qabs_neg, each composing two right *)
(*   multiplications by eta with Qmult_le_compat_r under *)
(*   Qlt_le_weak.                                                   *)
(* sp2_q_epsfrac : 0 < e gives 0 < e/(4+e) and (e/(4+e))^2 < e.     *)
(*   With H41 : 0 < 4 + e by Qplus_lt_compat from the literal *)
(*   Qlt 0 4, and Hn0 : (4+e) != 0 by a Qlt_not_le contradiction *)
(*   plus the Qeq-to-Qle cast.  The bound e < (4+e)^2 runs through *)
(*   Qlt_le_trans along e + (16 + 7e + e^2), using *)
(*   proj2 (Qplus_lt_r z x y) in its shared-left-argument shape *)
(*   with the setoid form of Qplus_0_r, and closes by the *)
(*   Qeq-to-Qle cast plus ring.  Then e/(4+e) < 4 + e is *)
(*   Qmult_lt_compat_r e ((4+e)^2) (/(4+e)) on that bound and *)
(*   Qinv_lt_0_compat H41, where e/(4+e) == e * /(4+e) holds *)
(*   definitionally by reflexivity.  Positivity 0 < e/(4+e) is a *)
(*   Qlt_le_dec contradiction against 0, resting on *)
(*   eta * (4+e) == e through the setoid chain Qmult_comm (/(w), w), *)
(*   Qmult_inv_r w Hn0, Qmult_1_r; the closing step multiplies *)
(*   eta * eta < (4+e) * eta by Qmult_lt_compat_r and rewrites *)
(*   with eta * (4+e) == e.                                         *)
(* Discipline: Qeq rewriting always goes through setoid_rewrite; a *)
(*   bare rewrite does not typecheck against the Qeq setoid.        *)
(*                                                                *)
(* Nonnegativity chain and witness upgrade (encoded above).         *)
(* Definition sp2_lower0 (y : Real) : Set :=                       *)
(*   forall eps : Q, QltT 0 eps -> real_lt (real_opp y) (real_const eps). *)
(* sp2_lower0_intro: pointwise nonnegativity 0 <= y_n at every n    *)
(*   gives sp2_lower0 y, with witness delta := eps/2 and N := 0;    *)
(*   eps/2 < eps + y_n runs through Qlt_le_trans (eps/2) eps *)
(*   (eps+y_n); eps/2 < eps and 0 < eps/2 come from the half *)
(*   toolkit (Qlt_le_dec contradiction plus the field identity *)
(*   eps == eps/2 + eps/2).  Inside the real_lt unfolding, *)
(*   sp2_qminus_0_r is applied by setoid_rewrite.                   *)
(* sp2_lower0_plus: sp2_lower0 y and sp2_lower0 z give *)
(*   sp2_lower0 (y+z); apply each premise at eps/2 for delta1, N1 *)
(*   and delta2, N2, set delta := delta1 + delta2 (positivity by *)
(*   Qplus_lt_compat) and N := max N1 N2 (the NatLe_lift + *)
(*   Nat.le_trans + NatLe_drop usage pattern of the S02 *)
(*   real_lt_trans interface); the pointwise bound *)
(*   delta1 + delta2 < eps + y_n + z_n is Qplus_lt_compat plus a *)
(*   field reshaping.                                                *)
(* sp2_lower0_sq: every x gives sp2_lower0 (x*x), by *)
(*   sp2_lower0_intro and sp2_qsq_nonneg fed pointwise after the *)
(*   sp2_pt_mult reshaping of projT1.                                *)
(* The discriminant is the sum of two squares, so *)
(*   sp2_lower0_plus and sp2_lower0_sq compose it directly: no Or, *)
(*   no sign decision.                                               *)
(* sp2_disc_pos_of_sq: real_lt real_zero (u*u) gives *)
(*   real_lt real_zero (sp2_disc a d b) with u := a - d; unpack the *)
(*   real_lt witness (delta, N) and reuse it pointwise, since *)
(*   delta < u_n^2 and 0 <= (2*b_n)^2 (sp2_qsq_nonneg) give *)
(*   delta < u_n^2 + (2*b_n)^2 by Qlt_le_trans and the S02 *)
(*   nonnegative-summand lemma.                                       *)
(* sp2_disc_pos_of_bsq: symmetric, with the b^2 summand strict.      *)
(* sp2_disc_eq_zero_of_degen: real_eq of a - d and of 2*b with zero *)
(*   gives real_eq of the discriminant with zero; take *)
(*   eta := eps/(4+eps), bound both squares through the *)
(*   |x|-based estimate above, and eta^2 + 4*eta'^2 < eps through *)
(*   the epsfrac scale; Qabs enters via Qabs_pos / Qabs_neg.          *)
(*                                                                *)
(* Rational-layer Newton rate notes.  L1 through L5 and the exit *)
(*   are encoded above (sp2_qstep_gap, sp2_qnewton_bnd, *)
(*   sp2_qgap_le1_S, sp2_qgap1_le1, sp2_qgap_le1, *)
(*   sp2_sqrt_rate_core, sp2_sqrt_rate); sp2_q2pow, the *)
(*   unboundedness companion and the QeqT-scaled general input *)
(*   form are NOT encoded in this file.                              *)
(* Residual identity: step(x)^2 - D == (x^2 - D)^2 / (4*x*x), one *)
(*   field-solve; the side conditions x != 0 and the literal 2 != 0 *)
(*   split 4*x*x != 0 by Qmult_integral.                              *)
(* Inductive bounds: 0 < x_n, 1 <= x_n and D <= x_n^2; the base *)
(*   case x_0 = 2 is literal, the step lifts positivity by *)
(*   Qplus_lt_compat and Qmult_lt_compat_r on the factor (1#2), *)
(*   D <= x'^2 follows from the residual identity with *)
(*   gap_n >= 0 (Qmult_le_0_compat), and 1 <= x' from a *)
(*   Q_le_dec contradiction: x < 1 gives x^2 < x < 1 against *)
(*   1 <= D <= x^2.                                                    *)
(* Contraction: x_{n+1} <= x_n, since D/x_n <= x_n follows from *)
(*   D <= x_n^2 by multiplying 1/x_n, (a+b)/2 <= (a+a)/2 == a, and *)
(*   x_n * x_n * /x_n == x_n by field under the side condition.        *)
(* Rate by induction on the composite shape gap_n * 4^n <= 3 with *)
(*   gap_n <= 4 and gap_n <= 1 for n >= 1: the base gap_0 = 4 - D <= 3 *)
(*   needs D >= 1; in the step, the n = 0 branch squares through *)
(*   4*x_0^2 = 16 and the n >= 1 branch uses *)
(*   gap_{n+1} = gap_n^2/(4*x_n^2) <= gap_n^2/4 <= gap_n/4; both *)
(*   branches close c_{Sn} <= (gap_n/4) * 4^{Sn} == gap_n * 4^n <= 3 *)
(*   by field reshaping and Qmult_le_compat_r.                          *)
(* Exit face: D in [1,4] gives 0 <= x_n^2 - D <= 3/4^n (multiply *)
(*   c_n <= 3 by /4^n, with 4^n != 0 by Qlt_not_eq plus *)
(*   Qmult_inv_r; QleT' enters and leaves through *)
(*   QleT'_to_Qle / Qle_to_QleT').                                      *)
(* Unboundedness companion (not encoded): 0 < q gives some m with *)
(*   c < q * 4^m; the c <= 0 branch takes m := 0, otherwise *)
(*   m := Z.to_nat of a suitable scaling, lifted through *)
(*   Z2Nat.id and a Z.mul_le_mono chain on the positive side.           *)
(* QeqT-scaled general form (not encoded): a QeqT witness *)
(*   sp2_qdisc a d b == 4^k * D' with 1 <= D' <= 4 transfers the *)
(*   normalized rate by converting QeqT to Qeq through a *)
(*   Qcompare case analysis plus Qeq_alt proj2, and the upper bound *)
(*   reassociates 4^k * 3 / 4^{k+Sm} == 3 / 4^{Sm} < eps.                *)
(*                                                                *)
(* Main statement notes (encoded above).                            *)
(* half := real_const (1#2); eig_up and eig_dn are half * (a+d) *)
(*   plus and minus half * s.                                        *)
(* sp2_eig_gap: the square root witness s comes from *)
(*   projT1 (real_sqrt_exists D (inl HD)) of the AttnSqrt asset, *)
(*   reused as recorded; eig_up - eig_dn == s is pointwise, *)
(*   |X_n - s_n| == 0 < N eps with N := 0, through the Section 0 *)
(*   pointwise engine plus ring; strict positivity of s (the *)
(*   corollary) destructs the real_le Or, and the equal branch *)
(*   s == 0 yields real_eq D 0, contradicting real_lt of D with *)
(*   zero pointwise (delta < D_n and |D_n| < delta, N := max).       *)
(*   The D = 0 degenerate face is carried in eps-uniform form as *)
(*   an explicitly recorded companion statement.                      *)
(*                                                                *)

(* Superseded extraction note: an earlier list also named sp2_q2pow; *)
(* the scalar-only Separate Extraction above is the recorded form, *)
(* and the Real-layer dependency face rests on the Print Assumptions *)
(* audit alone.                                                      *)
(* ============================================================ *)

Print Assumptions sp2_pt_plus.
Print Assumptions sp2_pt_mult.
Print Assumptions sp2_pt_opp.
Print Assumptions sp2_pt_const.
Print Assumptions sp2_pt_zero.
Print Assumptions sp2_qeq_le.
Print Assumptions sp2_qnewton_0.
Print Assumptions sp2_qnewton_S.
Print Assumptions sp2_q4pow_S.
Print Assumptions sp2_q4pow_0.
Print Assumptions sp2_qgap_E.
