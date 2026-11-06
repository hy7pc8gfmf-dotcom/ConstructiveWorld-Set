(* ConstructiveWorld-Set -- Q-layer irrationality instances for sqrt 2 and sqrt 3. *)

(** * UpReqSqrt3Irrational: sqrt 2 and sqrt 3 are irrational over Q.

    Mission.  Two parallel instances of the mother theorem in
      [UpReqIrrationalCriterion], one per base.  Each family ([ir2_] for
      sqrt 2, [is3_] for sqrt 3) supplies Q-layer order lemmas, infinite
      descent ([ir2_no_sqrt2], [is3_no_sqrt3]), Newton sequences with
      decay gauges ([ir2_x], [ir2_e]; [is3_x], [is3_e]), decidable escape
      gaps, premise instances ([ir2_tail], [ir2_vanish], [ir2_escape]),
      and the main theorems [ir2_sqrt2_irrational_criterion],
      [is3_sqrt3_irrational_criterion].

    Dependencies.  Stdlib [Lia], [Setoid], [Morphisms], [Qfield], [Extraction],
      [QArith.QArith], [QArith.Qabs], [ZArith.ZArith], [Arith.Arith], [Bool.Bool].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [SumInvFactEscape],
      [UpReqBanachNormOpp], [UpReqIrrationalCriterion] of this development.

    References.  This development, UpReqSqrt3Irrational.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqSqrt3Irrational.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import Lia Setoid Morphisms Qfield.
From Stdlib Require Import Extraction.

(* ================= Section 1. the ir2_ family: sqrt 2 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

(* S0. Q-layer basics                                                *)

Lemma ir2_add_le_r : forall x y z : Q, Qle x y -> Qle (x + z) (y + z).
Proof.
  intros [xn xd] [yn yd] [zn zd]. unfold Qle in *.
  cbn [Qnum Qden Qplus] in *. nia.
Qed.

Lemma ir2_add_lt_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros x y z H.
  apply (lic_qlt_add_r x y z H).
Qed.

(* squaring is monotone on nonnegative operands: 0 ≤ v ≤ u gives v·v ≤ u·u *)
Lemma ir2_sq_mono : forall u v : Q, Qle 0 v -> Qle v u -> Qle (v*v) (u*u).
Proof.
  intros u v H0 H1.
  destruct u as [un ud]; destruct v as [vn vd].
  unfold Qle, Qmult in *. cbn [Qnum Qden] in *. nia.
Qed.

(* converse of squaring on the nonnegative quadrant: 0 ≤ u, 0 ≤ v and
   v·v < u·u give v < u *)
Lemma ir2_lt_of_sq : forall u v : Q, Qle 0 u -> Qle 0 v -> Qlt (v*v) (u*u) -> Qlt v u.
Proof.
  intros u v Hu0 Hv0 Hsq.
  destruct (Qlt_le_dec v u) as [Hlt | Hle].
  - exact Hlt.
  - exfalso.
    pose proof (ir2_sq_mono v u Hu0 Hle) as Hm.
    apply (Qlt_not_le (v*v) (u*u) Hsq Hm).
Qed.

(* the difference-of-squares identity *)
Lemma ir2_sq_diff : forall u v : Q, ((u - v) * (u + v) == u * u - v * v)%Q.
Proof.
  intros u v. unfold Qminus. ring.
Qed.

(* |u − v| == u − v for u ≥ v *)
Lemma ir2_abs_sub : forall u v : Q, Qle v u -> Qabs ((u - v)%Q) == (u - v)%Q.
Proof.
  intros u v H. apply Qabs_pos.
  unfold Qle in *. destruct u as [un ud]; destruct v as [vn vd].
  unfold Qminus, Qplus, Qopp. cbn [Qnum Qden] in *. lia.
Qed.

(* the sum of two positives is positive *)
Lemma ir2_qpos_add : forall u v : Q, Qlt 0 u -> Qlt 0 v -> Qlt 0 (u + v).
Proof.
  intros [un ud] [vn vd]. assert (Hud : (0 < Z.pos ud)%Z) by apply Pos2Z.is_pos.
  assert (Hvd : (0 < Z.pos vd)%Z) by apply Pos2Z.is_pos.
  unfold Qlt, Qplus in *. cbn [Qnum Qden] in *. nia.
Qed.

(* 2/x > 0 for x > 0 *)
Lemma ir2_div2_pos : forall v : Q, Qlt 0 v -> Qlt 0 (2%Q / v).
Proof.
  intros v Hv. unfold Qdiv.
  apply (Qmult_lt_0_compat (2#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma ir2_inv_pos : forall w : Q, Qlt 0 w -> Qle 0 (Qinv w).
Proof.
  intros [wn wd] H. unfold Qlt, Qle, Qinv in *.
  destruct wn; cbn in *; try lia; nia.
Qed.

(* the multiply-then-divide-back shape: X ≤ Y·M gives X·M⁻¹ ≤ Y for 0 < M *)
Lemma ir2_le_of_mul_le : forall X Y M : Q,
  Qlt 0 M -> Qle (X * Qinv M) Y -> Qle X (Y * M).
Proof.
  intros X Y M Hm Hle.
  assert (HMne : ~ (M == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q M Hm (Qeq_sym _ _ Hc))).
  pose proof (bno_mul_div_self M HMne) as Hb. apply qeqT_imp_qeq in Hb.
  unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
  assert (Hb2 : (Qinv M * M == 1%Q)%Q)
    by (rewrite (Qmult_comm (Qinv M) M); exact Hb).
  apply (Qle_trans X ((X * Qinv M) * M)%Q).
  - rewrite <- (Qmult_assoc X (Qinv M) M). rewrite Hb2.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qmult_1_r.
  - apply Qmult_le_compat_r; [exact Hle | apply Qlt_le_weak; exact Hm].
Qed.

(* multiplying by a positive and dividing back: X·M ≤ Y with M > 0 gives
   X ≤ Y·M⁻¹ *)
Lemma ir2_le_mul_inv : forall X Y M : Q,
  Qlt 0 M -> Qle (X * M) Y -> Qle X (Y * Qinv M).
Proof.
  intros X Y M Hm Hle.
  apply (ir2_le_of_mul_le X Y (Qinv M)).
  - destruct (Qlt_le_dec 0%Q (Qinv M)) as [Hi | Hi].
    + exact Hi.
    + exfalso. apply (Qlt_not_eq 0%Q M Hm).
      assert (Hz : (Qinv M == 0%Q)%Q)
        by (apply Qle_antisym; [exact Hi | apply ir2_inv_pos; exact Hm]).
      pose proof (Qinv_involutive M) as Hii. rewrite Hz in Hii. exact Hii.
  - rewrite Qinv_involutive. exact Hle.
Qed.

(* strict order reversal of Qinv: 0 < v < u gives u⁻¹ < v⁻¹ *)
Lemma ir2_inv_lt : forall u v : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt v u -> Qlt (Qinv u) (Qinv v).
Proof.
  intros [un ud] [vn vd] Hu Hv Hlt. unfold Qlt, Qinv in *.
  destruct un; destruct vn; cbn in *; lia.
Qed.

(* non-strict order reversal of Qinv: 0 < u ≤ v gives v⁻¹ ≤ u⁻¹ *)
Lemma ir2_inv_le : forall u v : Q, Qlt 0 u -> Qle u v -> Qle (Qinv v) (Qinv u).
Proof.
  intros [un ud] [vn vd]. unfold Qlt, Qle, Qinv in *.
  destruct un; destruct vn; cbn in *; try lia; nia.
Qed.

(* left multiplication preserves ≤: x ≤ y and 0 ≤ z give z·x ≤ z·y; the
   standard library only ships the right-multiplication form
   Qmult_le_compat_r *)
Lemma ir2_mult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z Hxy Hz. rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_le_compat_r; assumption.
Qed.

(* S1. the Z level: 2 has no rational square root, by infinite descent *)

Lemma ir2_even_of_sq_even : forall z : Z, Z.even (z * z) = true -> Z.even z = true.
Proof.
  intros z H. pose proof (Z.even_mul z z) as HM. rewrite HM in H.
  apply Bool.orb_true_iff in H. destruct H as [H | H]; exact H.
Qed.

Lemma ir2_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 2 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 2 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* a even, b even, and b strictly decreases *)
      assert (Hae : Z.even a = true).
      { apply ir2_even_of_sq_even. rewrite Heq.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec a)) in Hae. destruct Hae as [a1 Ha1].
      assert (Hbb : (b * b = 2 * (a1 * a1))%Z) by lia.
      assert (Hbe : Z.even b = true).
      { apply ir2_even_of_sq_even. rewrite Hbb.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec b)) in Hbe. destruct Hbe as [b1 Hb1].
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((2 * b1) * (2 * b1))%Z with (4 * (b1 * b1))%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

Lemma ir2_zpos_xo : forall p : positive, (Z.pos (xO p) = 2 * Z.pos p)%Z.
Proof. intro p. exact eq_refl. Qed.

Lemma ir2_no_sqrt2 : forall q : Q, ~ (q * q == 2%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 2 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    assert (Hb2 : (Z.pos (b * b)~0 = 2 * Z.pos (b * b))%Z)
      by apply ir2_zpos_xo.
    lia. }
  exact (ir2_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* S2. the Newton sequence and its basic Q-level quantities *)

Fixpoint ir2_x (n : nat) : Q :=
  match n with
  | O => 2%Q
  | Datatypes.S m => (ir2_x m + 2%Q / ir2_x m) * (1 # 2)
  end.

Definition ir2_delta (n : nat) : Q := ir2_x n * ir2_x n - 2%Q.
Definition ir2_e (n : nat) : Q := (1 # 2) * ir2_delta n.

Fixpoint ir2_qp (m : nat) : Q :=
  match m with
  | O => 1%Q
  | Datatypes.S m' => (2 # 1) * ir2_qp m'
  end.

Lemma ir2_x1 : ir2_x 1 == (3 # 2).
Proof. unfold Qeq. cbn. exact eq_refl. Qed.

Lemma ir2_qp_def : forall n : nat, ir2_qp (Datatypes.S n) == ((2 # 1) * ir2_qp n)%Q.
Proof. intros n. exact (Qeq_refl ((2 # 1) * ir2_qp n)%Q). Qed.

Lemma ir2_qp_pos : forall n : nat, Qlt 0 (ir2_qp n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [ir2_qp Qnum Qden]. lia.
  - cbn [ir2_qp]. apply (Qmult_lt_0_compat (2 # 1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* qp n is exactly 2^n; the explicit exponential form serves the nat power
   comparisons in the vanish and escape parts *)
Lemma ir2_qp_pow : forall n : nat, ir2_qp n == ((Z.of_nat (2 ^ n)) # 1)%Q.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite ir2_qp_def. rewrite IH.
    rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    cbn [Z.of_nat]. reflexivity.
Qed.


(* numerical lemmas at the nat level *)
Lemma ir2_pow_ge : forall j : nat, (Datatypes.S j <= 2 ^ j)%nat.
Proof.
  induction j as [|j IH].
  - cbn. lia.
  - replace (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat
      by (rewrite Nat.pow_succ_r'; reflexivity).
    lia.
Qed.

(* step inequalities: 6j+3 ≤ 3j² and 10j+5 ≤ 5j² hold for j ≥ 3; the
   induction step normalizes by ring to purely linear goals, where the
   three-premise product certificates of nia are not needed *)
Lemma ir2_step_le : forall j : nat, (3 <= j)%nat -> (6 * j + 3 <= 3 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (3 * Datatypes.S j * Datatypes.S j)%nat
      with (3 * j * j + 6 * j + 3)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|[|j'']]]; lia.
Qed.

Lemma ir2_step_le5 : forall j : nat, (3 <= j)%nat -> (10 * j + 5 <= 5 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (5 * Datatypes.S j * Datatypes.S j)%nat
      with (5 * j * j + 10 * j + 5)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|[|j'']]]; lia.
Qed.

Lemma ir2_pow3sq : forall j : nat, (3 * j * j <= 2 ^ (j + 8))%nat.
Proof.
  assert (Haux : forall j : nat, (3 * j * j <= 2 ^ (8 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (8 + Datatypes.S j)%nat with (Datatypes.S (8 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (3 * Datatypes.S j * Datatypes.S j)%nat
          with (3 * j * j + 6 * j + 3)%nat by ring.
        pose proof (ir2_step_le j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 8). apply Haux.
Qed.

Lemma ir2_pow5sq : forall j : nat, (5 * j * j <= 2 ^ (j + 4))%nat.
Proof.
  assert (Haux : forall j : nat, (5 * j * j <= 2 ^ (4 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (4 + Datatypes.S j)%nat with (Datatypes.S (4 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (5 * Datatypes.S j * Datatypes.S j)%nat
          with (5 * j * j + 10 * j + 5)%nat by ring.
        pose proof (ir2_step_le5 j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 4). apply Haux.
Qed.

(* S3. basic properties of the sequence (positivity, lower bound,
   monotonicity, δ algebra) *)

Lemma ir2_x_pos : forall n : nat, Qlt 0 (ir2_x n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [ir2_x Qnum Qden]. lia.
  - cbn [ir2_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | apply ir2_div2_pos; exact IH].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma ir2_delta_succ_mul : forall n : nat,
  (ir2_delta (Datatypes.S n) * (4 * (ir2_x n * ir2_x n)) == ir2_delta n * ir2_delta n)%Q.
Proof.
  intro n. unfold ir2_delta. cbn [ir2_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (ir2_x n) (ir2_x_pos n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma ir2_ge0_of_mul : forall A M : Q, Qlt 0 M -> Qle 0 (A * M) -> Qle 0 A.
Proof.
  intros [an ad] [mn md] Hm Hp. unfold Qlt, Qle, Qmult in *.
  cbn [Qnum Qden] in *. nia.
Qed.

Lemma ir2_delta_ge0 : forall n : nat, Qle 0 (ir2_delta n).
Proof.
  induction n as [|n IH].
  - unfold ir2_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [ir2_x Qnum Qden]. lia.
  - assert (HM : Qlt 0%Q (4 * (ir2_x n * ir2_x n))).
    { apply (Qmult_lt_0_compat (4#1) (ir2_x n * ir2_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (ir2_x n) (ir2_x n)); exact (ir2_x_pos n). }
    pose proof (ir2_delta_succ_mul n) as Hmul.
    assert (Hsq : Qle 0 (ir2_delta n * ir2_delta n)).
    { destruct (ir2_delta n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma ir2_delta_pos : forall n : nat, Qlt 0 (ir2_delta n).
Proof.
  intro n. pose proof (ir2_delta_ge0 n) as Hge.
  destruct (Qeq_dec (ir2_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (ir2_no_sqrt2 (ir2_x n)).
    unfold ir2_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (ir2_x n * ir2_x n) 2%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (ir2_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (ir2_delta n) 0%Q Hle Hge).
Qed.

Lemma ir2_sq_ge2 : forall n : nat, Qle 2%Q (ir2_x n * ir2_x n).
Proof.
  intro n. pose proof (ir2_delta_ge0 n) as H.
  assert (Hr : ((ir2_x n * ir2_x n - 2) + 2 == ir2_x n * ir2_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 2%Q (0%Q + 2%Q)%Q ((ir2_x n * ir2_x n - 2)%Q + 2%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma ir2_x_lb : forall n : nat, (7 # 5) <= ir2_x n.
Proof.
  intro n. pose proof (ir2_x_pos n) as Hp.
  destruct (Qlt_le_dec (ir2_x n) (7#5)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((ir2_x n) * (ir2_x n)) ((7#5) * (ir2_x n))).
    { apply (Qmult_lt_compat_r (ir2_x n) (7#5) (ir2_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((7#5) * (ir2_x n)) ((7#5) * (7#5))).
    { rewrite (Qmult_comm (7#5) (ir2_x n)).
      apply (Qmult_lt_compat_r (ir2_x n) (7#5) (7#5)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (ir2_x n * ir2_x n) 2%Q).
    { apply (Qlt_trans _ ((7#5) * (7#5))).
      - apply (Qlt_trans _ ((7#5) * (ir2_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (ir2_x n * ir2_x n) 2%Q).
    + exact H3.
    + apply ir2_sq_ge2.
  - exact Hle.
Qed.

Lemma ir2_mono : forall n : nat, ir2_x (Datatypes.S n) <= ir2_x n.
Proof.
  intro n. cbn [ir2_x].
  pose proof (ir2_sq_ge2 n) as H2.
  pose proof (ir2_x_pos n) as Hxp.
  destruct (ir2_x n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H2c : (2 * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H2 as H2'. rewrite ?Ex in H2'.
    unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0. apply qeqT_imp_qeq in Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle (2%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H2 | exact Hivp].
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               (2%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2))
                   == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma ir2_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  ir2_x k <= ir2_x n.
Proof.
  intros n k Hn1 Hnk.
  assert (Hgen : forall d : nat, ir2_x (n + d) <= ir2_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (ir2_x (n + d))).
      + apply ir2_mono.
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

Lemma ir2_x_ub : forall n : nat, (1 <= n)%nat -> ir2_x n <= (3 # 2).
Proof.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply (Qle_trans _ (ir2_x 1)).
    + apply (ir2_mono_le 1 (Datatypes.S n')); lia.
    + rewrite ir2_x1. apply Qle_refl.
Qed.

(* S4. decay of the error window (δ ≤ 1/4; δ(Sn) ≤ δn/28;
   e_n ≤ 1/2^{n+1}) *)

Lemma ir2_delta_step : forall n : nat, (1 <= n)%nat -> Qle (ir2_delta n) (1#4) ->
  Qle (ir2_delta (Datatypes.S n)) ((1#28) * ir2_delta n).
Proof.
  intros n Hn1 Hdu.
  pose proof (ir2_x_pos n) as Hxp.
  assert (Hlb : Qle ((7#5) * (7#5)) (ir2_x n * ir2_x n)).
  { apply (Qle_trans _ ((7#5) * ir2_x n)%Q).
    - apply ir2_mult_le_compat_l; [apply (ir2_x_lb n) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r; [apply (ir2_x_lb n) | apply Qlt_le_weak; apply (ir2_x_pos n)]. }
  assert (H7 : Qle 7%Q (4 * (ir2_x n * ir2_x n))).
  { apply (Qle_trans _ ((4#1) * ((7#5) * (7#5)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((7#5) * (7#5))).
      rewrite (Qmult_comm (4#1) (ir2_x n * ir2_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (ir2_delta_succ_mul n) as Hmul.
  pose proof (ir2_delta_ge0 (Datatypes.S n)) as HdS0.
  assert (Ha : Qle (7 * ir2_delta (Datatypes.S n)) (ir2_delta n * ir2_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (ir2_delta (Datatypes.S n)) (4 * (ir2_x n * ir2_x n))).
    apply Qmult_le_compat_r; [exact H7 | exact HdS0]. }
  assert (Hb : Qle (ir2_delta n * ir2_delta n) ((1#4) * ir2_delta n)).
  { apply (Qmult_le_compat_r (ir2_delta n) (1#4) (ir2_delta n));
      [exact Hdu | apply (ir2_delta_ge0 n)]. }
  assert (Hc : Qle (7 * ir2_delta (Datatypes.S n)) ((1#4) * ir2_delta n))
    by (apply (Qle_trans _ (ir2_delta n * ir2_delta n)); assumption).
  apply (Qle_trans (ir2_delta (Datatypes.S n))
    (((1#4) * ir2_delta n) * Qinv (7#1)) ((1#28) * ir2_delta n)).
  - apply (ir2_le_mul_inv (ir2_delta (Datatypes.S n)) ((1#4) * ir2_delta n) (7#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (ir2_delta (Datatypes.S n)) (7#1)). exact Hc.
  - assert (Hc2 : Qinv (7#1) == (1#7)%Q) by reflexivity.
    rewrite Hc2. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma ir2_quarter : forall n : nat, (1 <= n)%nat -> Qle (ir2_delta n) (1#4).
Proof.
  induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + change (ir2_delta 1) with (4 # 16)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + intro Hle0. assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#28) * ir2_delta (Datatypes.S n))).
      * apply (ir2_delta_step (Datatypes.S n)); [lia | exact Hdu].
      * apply (Qle_trans _ ((1#28) * (1#4))%Q).
        -- apply ir2_mult_le_compat_l; [exact Hdu | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma ir2_e_step : forall n : nat, (1 <= n)%nat ->
  Qle (ir2_e (Datatypes.S n)) ((1#2) * ir2_e n).
Proof.
  intros n Hn1. unfold ir2_e.
  apply (Qle_trans _ ((1#2) * ((1#28) * ir2_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (ir2_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#28) * ir2_delta n)).
    pose proof (ir2_quarter n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + apply (ir2_delta_step n); [exact Hn1 | exact Hdu].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (ir2_delta n) as [dn dd] eqn:Edn.
    pose proof (ir2_delta_ge0 n) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.

Lemma ir2_e_to_delta : forall n : nat,
  (ir2_e n * ir2_qp (Datatypes.S n) == ir2_delta n * ir2_qp n)%Q.
Proof.
  intro n. unfold ir2_e. rewrite ir2_qp_def. ring.
Qed.

Lemma ir2_decay : forall n : nat,
  Qle (ir2_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - change (ir2_e 1) with (4 # 32)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1#2) * ir2_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * apply (ir2_e_step (Datatypes.S n)). lia.
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * ir2_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (ir2_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact IH.
Qed.

Lemma ir2_delta_pow_le : forall n : nat, (1 <= n)%nat ->
  Qle (ir2_delta n * ir2_qp n) 1%Q.
Proof.
  intros n Hn. rewrite <- (ir2_e_to_delta n).
  destruct n as [|n'].
  - lia.
  - apply (ir2_decay n').
Qed.

(* the 1/M⁻¹ shape: 0 < u and u·v ≤ 1 give v ≤ u⁻¹ *)
Lemma ir2_le_inv : forall u v : Q, Qlt 0 u -> Qle (u * v) 1%Q -> Qle v (Qinv u).
Proof.
  intros [un ud] [vn vd] Hm Hle. unfold Qlt, Qle, Qmult, Qinv in *.
  destruct un; cbn [Qnum Qden] in *; try lia; nia.
Qed.

(* the dual: 0 < u and 1 ≤ u·v give u⁻¹ ≤ v *)
Lemma ir2_ge_inv : forall u v : Q, Qlt 0 u -> Qle 1 (u * v) -> Qle (Qinv u) v.
Proof.
  intros [un ud] [vn vd] Hm Hle. unfold Qlt, Qle, Qmult, Qinv in *.
  destruct un; cbn [Qnum Qden] in *; try lia; nia.
Qed.

(* S5. escape gap lemmas (a decidable Q-layer gap between √2 and any
   rational) *)

Lemma ir2_gap_lower : forall u v : Q,
  Qle 0 v -> Qle v u -> Qle u (3#2) -> Qle 2 (u*u) -> Qlt (v*v) 2 ->
  Qle ((2 - v*v) * (1#3)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H2 Hsq.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); assumption).
  assert (Huv0 : Qlt 0%Q (u + v)).
  { destruct (Qlt_le_dec 0%Q (u + v)) as [Hlt | Hle].
    - exact Hlt.
    - exfalso.
      assert (Huu : Qle u (u + v)).
      { apply (Qle_trans u (u + 0%Q) (u + v)).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qplus_0_r.
        - apply (Qplus_le_compat u u 0%Q v); [apply Qle_refl | exact Hv0]. }
      assert (Hu : u == 0%Q).
      { apply (Qle_antisym u 0%Q).
        - apply (Qle_trans u (u + v) 0%Q); [exact Huu | exact Hle].
        - exact Hu0. }
      pose proof H2 as H2'. rewrite Hu in H2'.
      unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'.
      clear Hu Huu Hle. lia. }
  assert (Hne : ~ ((u + v)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u + v) Huv0); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u - v) == (u*u - v*v) * Qinv (u + v))%Q).
  { pose proof (bno_mul_div_self (u + v) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u - v) * (u + v)) * Qinv (u + v)) == (u - v))%Q).
    { rewrite <- (Qmult_assoc (u - v) (u + v) (Qinv (u + v))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hw0 : Qle 0%Q (2 - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) 2%Q Hsq)).
  assert (Hub3 : Qle (u + v) 3%Q).
  { apply (Qle_trans _ ((3#2) + (3#2))%Q).
    - apply (Qplus_le_compat u (3#2) v (3#2)).
      + exact Hub.
      + apply (Qle_trans v u (3#2)); assumption.
    - unfold Qle, Qplus, Qmult. cbn [Qnum Qden]. lia. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ ((2 - v*v) * Qinv (u + v))%Q).
    + apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) (3#1)); [exact Huv0 | exact Hub3].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H2.
      * exact Hivp.
  - apply Qle_refl.
Qed.

Lemma ir2_gap_upper_small : forall u v d : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt u v -> Qle v (3#2) -> Qlt 2 (v*v) ->
  d == (u*u - 2) -> Qle 0 d -> Qle d ((2#5) * (v*v - 2)) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Hv0 Huv Hv32 Hsq Hd Hdu Hdle.
  assert (Hw0 : Qlt 0 (v*v - 2)) by (apply (lic_qlt_0_minus 2%Q (v*v)); exact Hsq).
  assert (Hpu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; assumption).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpu (Qeq_sym _ _ Hc))).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 2) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
    destruct v as [vn vd].
    unfold Qlt, Qle, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hvup : Qlt (v + u) ((3#2) + (3#2))%Q).
  { apply (Qlt_le_trans (v + u) (v + v) ((3#2) + (3#2))).
    - apply (lic_qlt_add_l v u v Huv).
    - apply (Qplus_le_compat v (3#2) v (3#2)); [exact Hv32 | exact Hv32]. }
  apply (Qle_lt_trans (d * (1#2)) ((v*v - u*u) * (1#3)) (v - u)).
  - apply (Qle_trans _ ((1#5) * (v*v - 2))%Q).
    + destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
      rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
      unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
      cbn [Qnum Qden Qplus] in *.
      assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
      assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      lia.
    + assert (H35 : Qle ((3#5) * (v*v - 2)) (v*v - u*u)).
      { rewrite Hsh.
        destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
        rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
        destruct v as [vn vd].
        unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
        cbn [Qnum Qden Qplus] in *.
        assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
        assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
        nia. }
      assert (Hr35 : (((1#3) * ((3#5) * (v*v - 2))) == ((1#5) * (v*v - 2)))%Q) by ring.
      apply (Qle_trans _ ((1#3) * ((3#5) * (v*v - 2)))%Q).
      * rewrite Hr35. apply Qle_refl.
      * rewrite (Qmult_comm (1#3) ((3#5) * (v*v - 2))).
        apply Qmult_le_compat_r; [exact H35 | unfold Qle; cbn; lia].
  - rewrite Hbridge.
    rewrite (Qmult_comm (v*v - u*u) (1#3)).
    rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
    apply (Qmult_lt_compat_r (1#3) (Qinv (v + u)) (v*v - u*u)).
    + exact Hvu2.
    + apply (ir2_inv_lt (3#1) (v + u)).
      * unfold Qlt. cbn [Qnum Qden]. lia.
      * exact Hpu.
      * apply (lic_qlt_comp_r ((3#2) + (3#2))%Q (3#1)%Q (v + u)).
        -- reflexivity.
        -- exact Hvup.
Qed.

Lemma ir2_gap_upper_big : forall u v d : Q,
  Qlt 0 u -> Qlt u v -> (3#2) <= v -> Qlt 2 (v*v) ->
  d == (u*u - 2) -> Qle 0 d -> Qle ((v + 1) * d) (v*v - 2) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Huv Hv32 Hsq Hd Hdu Hd1.
  assert (Hw0 : Qlt 0 (v*v - 2)) by (apply (lic_qlt_0_minus 2%Q (v*v)); exact Hsq).
  assert (Hvp : Qlt 0 v).
  { apply (Qlt_le_trans 0%Q (3#2) v); [unfold Qlt; cbn; lia | exact Hv32]. }
  assert (Hpvu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; [exact Hvp | exact Hu0]).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpvu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 2) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qle 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (H2vp : Qlt 0%Q ((2#1) * v)).
  { apply (Qmult_lt_0_compat (2#1) v); [unfold Qlt; cbn; lia | exact Hvp]. }
  assert (Huv2 : Qle (v + u) ((2#1) * v)).
  { apply (Qle_trans (v + u) (v + v) ((2#1) * v)).
    - apply (Qplus_le_compat v v u v); [apply Qle_refl | apply Qlt_le_weak; exact Huv].
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hdv : Qle (d * v) ((v*v - 2) - d)).
  { destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hkey : Qle (d * (1#2)) (((v*v - 2) - d) * Qinv ((2#1) * v))).
  { apply (ir2_le_mul_inv (d * (1#2)) ((v*v - 2) - d) ((2#1) * v)).
    - exact H2vp.
    - assert (Hring : (((d * (1#2)) * ((2#1) * v)) == (d * v))%Q) by ring.
      rewrite Hring. exact Hdv. }
  assert (Hvu2p : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  apply (Qle_lt_trans (d * (1#2)) (((v*v - 2) - d) * Qinv ((2#1) * v)) (v - u)).
  - exact Hkey.
  - apply (Qle_lt_trans ((v*v - 2 - d) * Qinv ((2#1) * v))
            ((v*v - u*u) * Qinv ((2#1) * v)) (v - u)).
    + assert (Hle2 : Qle (v*v - 2 - d) (v*v - u*u)).
      { rewrite Hd. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply Qmult_le_compat_r; [exact Hle2 | apply ir2_inv_pos; exact H2vp].
    + rewrite Hbridge.
      rewrite (Qmult_comm (v*v - u*u) (Qinv ((2#1) * v))).
      rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
      apply (Qmult_lt_compat_r (Qinv ((2#1) * v)) (Qinv (v + u)) (v*v - u*u)).
      * exact Hvu2p.
      * apply (ir2_inv_lt ((2#1) * v) (v + u)).
        -- exact H2vp.
        -- exact Hpvu.
        -- assert (Hr2 : (v + v == (2#1) * v)%Q) by ring.
           rewrite <- Hr2. apply (lic_qlt_add_l v u v Huv).
Qed.

(* S6. the three premise instances of the mother theorem (tail control,
   window vanishing, escape window) *)

Definition ir2_tail : lic_tail_bounded ir2_x ir2_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (ir2_mono_le n k Hn1 Hnk) as Hmono.
  pose proof (ir2_delta_ge0 n) as Hd0n.
  pose proof (ir2_delta_pos n) as Hdpn.
  assert (Habs : Qabs ((ir2_x k - ir2_x n)%Q) == (ir2_x n - ir2_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (ir2_x n + ir2_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (7#5) (ir2_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (ir2_x_lb n).
    - apply (Qlt_le_trans 0%Q (7#5) (ir2_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (ir2_x_lb k). }
  assert (Hsumne : ~ ((ir2_x n + ir2_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (ir2_x n + ir2_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((ir2_x n - ir2_x k)
                      == (ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))%Q)).
  { pose proof (bno_mul_div_self (ir2_x n + ir2_x k) Hsumne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((ir2_x n - ir2_x k) * (ir2_x n + ir2_x k))
                    * Qinv (ir2_x n + ir2_x k)) == (ir2_x n - ir2_x k))%Q).
    { rewrite <- (Qmult_assoc (ir2_x n - ir2_x k) (ir2_x n + ir2_x k)
                    (Qinv (ir2_x n + ir2_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((ir2_x n * ir2_x n - ir2_x k * ir2_x k)
                   == (ir2_delta n - ir2_delta k))%Q)
      by (unfold ir2_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((14#5)) (ir2_x n + ir2_x k)).
  { apply (Qle_trans _ ((7#5) + (7#5))%Q).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
    - apply (Qplus_le_compat (7#5) (ir2_x n) (7#5) (ir2_x k));
        [apply (ir2_x_lb n) | apply (ir2_x_lb k)]. }
  assert (Hinvp : Qle 0%Q (Qinv (ir2_x n + ir2_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))
                     (ir2_delta n * Qinv (ir2_x n + ir2_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (ir2_delta n) as [dn dd] eqn:Edn.
      destruct (ir2_delta k) as [ek ed] eqn:Edk.
      pose proof (ir2_delta_ge0 k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (ir2_delta n * Qinv (ir2_x n + ir2_x k))
                     (ir2_delta n * Qinv ((14#5)))).
  { rewrite (Qmult_comm (ir2_delta n) (Qinv (ir2_x n + ir2_x k))).
    rewrite (Qmult_comm (ir2_delta n) (Qinv ((14#5)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (14#5) (ir2_x n + ir2_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (ir2_delta n * Qinv ((14#5))) ((1#2) * ir2_delta n)).
  { destruct (ir2_delta n) as [dn dd] eqn:Edn.
    pose proof (ir2_delta_pos n) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))
          (ir2_delta n * Qinv (ir2_x n + ir2_x k)) ((1#2) * ir2_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (ir2_delta n * Qinv (ir2_x n + ir2_x k))
            (ir2_delta n * Qinv ((14#5))) ((1#2) * ir2_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition ir2_vanish : lic_vanish ir2_e.
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (Z.to_nat (Z.pos pd) + 1)%nat.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans (ir2_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (ir2_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (ir2_e (Datatypes.S n'))).
        apply (ir2_decay n').
    + apply (Qlt_le_trans (Qinv (ir2_qp (Datatypes.S (Datatypes.S n'))))
              (Qinv (Z.pos pd # 1)) ((pn # pd)%Q)).
      * apply (ir2_inv_lt (ir2_qp (Datatypes.S (Datatypes.S n'))) (Z.pos pd # 1)).
        -- apply ir2_qp_pos.
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- rewrite ir2_qp_pow.
           replace (Datatypes.S (Datatypes.S n'))%nat with (n' + 2)%nat by lia.
           assert (Hzc : (Z.pos pd <= Z.of_nat n')%Z).
           { assert (Hle : (Z.to_nat (Z.pos pd) + 1 <= Datatypes.S n')%nat) by lia.
             pose proof (proj1 (Nat2Z.inj_le _ _) Hle) as Hz.
             rewrite Nat2Z.inj_add, Nat2Z.inj_succ in Hz.
             pose proof (Z2Nat.id (Z.pos pd) (ltac:(lia))) as Hz2.
             cbn in Hz. lia. }
           pose proof (proj1 (Nat2Z.inj_le _ _) (ir2_pow_ge (n' + 2))) as Hpg.
           unfold Qlt. cbn [Qnum Qden]. lia.
      * unfold Qle, Qinv. cbn [Qnum Qden]. nia.
Qed.

Definition ir2_escape : lic_escape_window ir2_x ir2_e.
Proof.
  intro q.
  destruct (Qlt_bool 0%Q q) eqn:Hpos.
  - pose proof (lic_qlt_bool_true 0%Q q Hpos) as Hq0.
    destruct (Qlt_bool (q * q) 2%Q) eqn:H2b.
    + (* q² < 2: take N := den(q) + 8 *)
      pose proof (lic_qlt_bool_true (q * q) 2%Q H2b) as H2.
      destruct q as [a b].
      assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
      assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
      { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
        exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
        rewrite Ek in Hz. cbn in Hz. lia. }
      exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hxsq : Qle 2%Q (ir2_x (Z.to_nat (Z.pos b) + 8)
                                * ir2_x (Z.to_nat (Z.pos b) + 8)))
        by apply ir2_sq_ge2.
      assert (Hqx : Qlt ((a # b) * (a # b))
                    (ir2_x (Z.to_nat (Z.pos b) + 8)
                     * ir2_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (Qlt_le_trans ((a # b) * (a # b)) 2%Q
                    (ir2_x (Z.to_nat (Z.pos b) + 8)
                     * ir2_x (Z.to_nat (Z.pos b) + 8))); assumption).
      assert (Hqle : Qlt (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (ir2_lt_of_sq (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b));
            [apply Qlt_le_weak; apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8))
            | apply Qlt_le_weak; exact Hq0 | exact Hqx]).
      assert (Habs : Qabs ((a # b) - ir2_x (Z.to_nat (Z.pos b) + 8))%Q
                     == (ir2_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      { rewrite Qabs_Qminus. apply ir2_abs_sub. apply Qlt_le_weak. exact Hqle. }
      rewrite Habs.
      apply (Qlt_le_trans (ir2_e (Z.to_nat (Z.pos b) + 8))
              (Qinv ((3 * (Z.pos b * Z.pos b)) # 1))
              (ir2_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      * apply (Qle_lt_trans (ir2_e (Z.to_nat (Z.pos b) + 8))
                (Qinv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8))))
                (Qinv ((3 * (Z.pos b * Z.pos b)) # 1))).
        -- apply (ir2_le_inv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   (ir2_e (Z.to_nat (Z.pos b) + 8))).
           ++ apply ir2_qp_pos.
           ++ rewrite (Qmult_comm (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                       (ir2_e (Z.to_nat (Z.pos b) + 8))).
              replace (Z.to_nat (Z.pos b) + 8)%nat
                with (Datatypes.S (Z.to_nat (Z.pos b) + 7))%nat by lia.
              apply (ir2_decay (Z.to_nat (Z.pos b) + 7)).
        -- apply (ir2_inv_lt (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   ((3 * (Z.pos b * Z.pos b)) # 1)).
           ++ apply ir2_qp_pos.
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ rewrite ir2_qp_pow.
              replace (Datatypes.S (Z.to_nat (Z.pos b) + 8))%nat
                with (Z.to_nat (Z.pos b) + 8 + 1)%nat by lia.
              assert (Hb3 : (2 ^ (Z.to_nat (Z.pos b) + 8 + 1)
                             = 2 * 2 ^ (Z.to_nat (Z.pos b) + 8))%nat)
                by (rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm; reflexivity).
              assert (Hzp : (1 <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow_ge (Z.to_nat (Z.pos b) + 8)) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite Nat2Z.inj_succ in Hp. lia. }
              assert (Hz : (3 * (Z.pos b * Z.pos b)
                            <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp.
                rewrite Hkb in Hp. cbn [Z.of_nat] in Hp. lia. }
              pose proof (f_equal Z.of_nat Hb3) as Hb4.
              rewrite Nat2Z.inj_mul in Hb4. cbn [Z.of_nat] in Hb4.
              unfold Qlt. cbn [Qnum Qden]. lia.
      * apply (Qle_trans _ ((2 - (a # b) * (a # b))
                             * (1#3))%Q).
        -- apply (ir2_ge_inv ((3 * (Z.pos b * Z.pos b)) # 1)
                   (((2 - (a # b) * (a # b)) * (1#3))%Q)).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ unfold Qle, Qmult, Qminus.
              pose proof H2 as H2'. unfold Qlt, Qmult, Qminus in H2'.
              cbn [Qnum Qden Qplus Qopp] in H2' |- *.
              assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
              nia.
        -- apply (ir2_gap_lower (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b)).
           ++ apply Qlt_le_weak. exact Hq0.
           ++ apply Qlt_le_weak. exact Hqle.
           ++ apply ir2_x_ub. lia.
           ++ exact Hxsq.
           ++ exact H2.
    + (* 2 ≤ q² *)
      pose proof (lic_qlt_bool_false_le (q * q) 2%Q H2b) as Hge2.
      destruct (Qeq_dec (q * q) 2%Q) as [Heq2 | Hne2].
      * exfalso. exact (ir2_no_sqrt2 q Heq2).
      * destruct (Qlt_bool 2%Q (q * q)) eqn:H2lt.
        -- pose proof (lic_qlt_bool_true 2%Q (q * q) H2lt) as Hlt2.
           destruct (Qlt_bool (3#2) q) eqn:H32b.
           ++ (* 3/2 < q: take N := num(q) + den(q) + 1 *)
              pose proof (lic_qlt_bool_true (3#2) q H32b) as H32.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (H32z : (3 * Z.pos b < 2 * a)%Z).
              { pose proof H32 as H32'. unfold Qlt in H32'.
                cbn [Qnum Qden] in H32'. lia. }
              assert (Hz2 : (2 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt2 as H2'. unfold Qlt, Qmult in H2'.
                cbn [Qnum Qden] in H2'. lia. }
              assert (Hkba : Z.of_nat (Z.to_nat a) = a)
                by (apply Z2Nat.id; lia).
              assert (Hkbb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b)
                by (apply Z2Nat.id; lia).
              assert (HpowN : ((a + Z.pos b) * Z.pos b
                               <= Z.of_nat (2 ^ (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)))%Z).
              { replace (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat
                  with (Datatypes.S (Z.to_nat a + Z.to_nat (Z.pos b))) by lia.
                rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r.
                pose proof (ir2_pow_ge (Z.to_nat a)) as H1.
                pose proof (ir2_pow_ge (Z.to_nat (Z.pos b))) as H2.
                apply (proj1 (Nat2Z.inj_le _ _)) in H1.
                apply (proj1 (Nat2Z.inj_le _ _)) in H2.
                rewrite Nat2Z.inj_succ in H1, H2.
                pose proof (Z2Nat.id a (ltac:(lia))) as Hz3.
                pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz4.
                rewrite Hz3 in H1. rewrite Hz4 in H2.
                rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
                nia. }
              exists (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hdpow : Qle (ir2_delta (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)
                                    * ir2_qp (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)) 1%Q).
              { apply (ir2_delta_pow_le). lia. }
              assert (Hbnd : Qle (((a # b) + 1)
                                  * ir2_delta (Z.to_nat a
                                               + Z.to_nat (Z.pos b) + 1))
                           (((a # b) * (a # b)) - 2%Q)%Q).
              { apply (Qle_trans _ (((a # b) + 1)
                                    * Qinv (ir2_qp (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1)))%Q).
                - apply ir2_mult_le_compat_l.
                  + apply (ir2_le_inv (ir2_qp (Z.to_nat a
                                          + Z.to_nat (Z.pos b) + 1))
                              (ir2_delta (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1))).
                    * apply ir2_qp_pos.
                    * rewrite (Qmult_comm (ir2_qp (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                                (ir2_delta (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1))).
                      exact Hdpow.
                  + apply (Qle_trans 0%Q (a # b) ((a # b) + 1)%Q).
                    * apply Qlt_le_weak. exact Hq0.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_lt_add_r (a # b) 1%Q).
                      unfold Qlt. cbn [Qnum Qden]. lia.
                - rewrite (ir2_qp_pow (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                  assert (Hzp1 : (1 <= Z.of_nat (2 ^ (Z.to_nat a
                                                   + Z.to_nat (Z.pos b) + 1)))%Z).
                  { pose proof (ir2_pow_ge (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hp.
                    apply (proj1 (Nat2Z.inj_le _ _)) in Hp. lia. }
                  destruct (Z.of_nat (2 ^ (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1)))
                    as [|pp|pp] eqn:Ez; try lia.
                  rewrite ?Ez in HpowN.
                  unfold Qle, Qmult, Qminus, Qinv.
                  cbn [Qnum Qden Qplus Qopp] in HpowN |- *.
                  assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                  nia. }
              assert (Hdl : Qlt (ir2_delta (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                            (((a # b) * (a # b)) - 2%Q)%Q).
              { destruct (ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                  as [dn dd] eqn:Ed.
                rewrite (ir2_qp_pow (Z.to_nat a
                          + Z.to_nat (Z.pos b) + 1)) in Hdpow.
                rewrite ?Ed in Hdpow, Hbnd.
                pose proof (ir2_delta_pos (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hdp3.
                rewrite ?Ed in Hdp3.
                unfold Qle, Qlt in *.
                cbn [Qnum Qden Qmult Qminus Qopp Qplus] in *.
                assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                nia. }
              assert (Hxq : Qlt (ir2_x (Z.to_nat a
                                       + Z.to_nat (Z.pos b) + 1))
                                (a # b)).
              { apply (ir2_lt_of_sq (a # b)
                        (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak.
                  apply (ir2_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                - pose proof Hdl as Hdl'.
                  unfold ir2_delta in Hdl'.
                  pose proof (lic_qlt_minus_add_r ((a # b) * (a # b)) 2%Q)
                    as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                                2%Q) as Hr2.
                  apply (Qle_lt_trans
                          (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                           * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                          ((ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            - 2%Q) + 2%Q)%Q
                          ((a # b) * (a # b))).
                  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                    exact (Qeq_sym _ _ Hr2).
                  + apply (lic_qlt_comp_r
                              (((a # b) * (a # b) - 2%Q) + 2%Q)%Q
                              ((a # b) * (a # b))
                              ((ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                - 2%Q) + 2%Q)%Q).
                    * exact Hr1.
                    * apply (lic_qlt_add_r
                                (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 - 2%Q)%Q
                                ((a # b) * (a # b) - 2%Q)%Q
                                2%Q Hdl'). }
              assert (HeqN : (ir2_e (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                              == ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                  * (1#2))%Q).
              { unfold ir2_e. ring. }
              rewrite HeqN.
              rewrite (ir2_abs_sub (a # b)
                        (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)))
                by (apply Qlt_le_weak; exact Hxq).
              apply (ir2_gap_upper_big
                      (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                      (a # b)
                      (ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
              ** apply (ir2_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hxq.
              ** apply Qlt_le_weak. exact H32.
              ** exact Hlt2.
              ** reflexivity.
              ** apply (ir2_delta_ge0 (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hbnd.
           ++ (* 2 < q² and q ≤ 3/2: take N := den(q) + 8, the same window
                 as branch 2; x_N overtakes q from below *)
              pose proof (lic_qlt_bool_false_le (3#2) q H32b) as H32.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
              assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
              { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
                exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
                rewrite Ek in Hz. cbn in Hz. lia. }
              assert (Hq2z : (2 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt2 as H2'. unfold Qlt, Qmult in H2'.
                cbn [Qnum Qden] in H2'. lia. }
              exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hpow3 : (3 * (Z.pos b * Z.pos b)
                               <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp. rewrite Hkb in Hp.
                cbn [Z.of_nat] in Hp. lia. }
              assert (Hdpow : Qle (ir2_delta (Z.to_nat (Z.pos b) + 8)
                                    * ir2_qp (Z.to_nat (Z.pos b) + 8)) 1%Q)
                by (apply ir2_delta_pow_le; lia).
              rewrite (ir2_qp_pow (Z.to_nat (Z.pos b) + 8)) in Hdpow.
              assert (H25 : Qlt (ir2_delta (Z.to_nat (Z.pos b) + 8))
                              (((2#5) * (((a # b) * (a # b)) - 2%Q))%Q)).
              { destruct (ir2_delta (Z.to_nat (Z.pos b) + 8)) as [dn dd] eqn:Ed.
                rewrite ?Ed in Hdpow.
                pose proof (ir2_delta_pos (Z.to_nat (Z.pos b) + 8)) as Hdp.
                rewrite Ed in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
                unfold Qle, Qlt, Qmult in Hdpow. cbn [Qnum Qden] in Hdpow.
                unfold Qlt, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp] in Hdp, Hdpow |- *.
                assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                nia. }
              assert (Hdl : Qlt (ir2_delta (Z.to_nat (Z.pos b) + 8))
                              ((((a # b) * (a # b)) - 2%Q)%Q)).
              { apply (Qlt_le_trans (ir2_delta (Z.to_nat (Z.pos b) + 8))
                        (((2#5) * (((a # b) * (a # b)) - 2%Q))%Q)
                        ((((a # b) * (a # b)) - 2%Q)%Q)).
                - exact H25.
                - apply (Qle_trans _ (1%Q * (((a # b) * (a # b)) - 2%Q))%Q).
                  + apply Qmult_le_compat_r.
                    * unfold Qle. cbn [Qnum Qden]. lia.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_0_minus 2%Q ((a # b) * (a # b)) Hlt2).
                  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_l. }
              assert (Hqx : Qlt (ir2_x (Z.to_nat (Z.pos b) + 8)
                                  * ir2_x (Z.to_nat (Z.pos b) + 8))
                            ((a # b) * (a # b))).
              { assert (Hr : (((ir2_x (Z.to_nat (Z.pos b) + 8)
                                * ir2_x (Z.to_nat (Z.pos b) + 8) - 2%Q) + 2%Q)
                              == (ir2_x (Z.to_nat (Z.pos b) + 8)
                                   * ir2_x (Z.to_nat (Z.pos b) + 8)))%Q)
                  by apply lic_qlt_minus_add_r.
                rewrite <- Hr.
                apply (Qlt_le_trans _ ((((a # b) * (a # b)) - 2%Q) + 2%Q)%Q).
                - apply (lic_qlt_add_r _ _ 2%Q Hdl).
                - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply lic_qlt_minus_add_r. }
              assert (Hqle : Qlt (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b))
                by (apply (ir2_lt_of_sq (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)));
                    [apply Qlt_le_weak; exact Hq0
                    | apply Qlt_le_weak;
                       apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8))
                    | exact Hqx]).
              rewrite (ir2_abs_sub (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)))
                by (apply Qlt_le_weak; exact Hqle).
              assert (Heq8 : (ir2_e (Z.to_nat (Z.pos b) + 8)
                              == ir2_delta (Z.to_nat (Z.pos b) + 8)
                                  * (1#2))%Q).
              { unfold ir2_e. ring. }
              rewrite Heq8.
              apply (ir2_gap_upper_small
                      (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b)
                      (ir2_delta (Z.to_nat (Z.pos b) + 8))).
              ** apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8)).
              ** exact Hq0.
              ** exact Hqle.
              ** exact H32.
              ** exact Hlt2.
              ** reflexivity.
              ** apply (ir2_delta_ge0 (Z.to_nat (Z.pos b) + 8)).
              ** apply Qlt_le_weak. exact H25.
        -- (* when ¬(2 < q²) and 2 ≤ q² hold, q² == 2 follows,
              contradicting ir2_no_sqrt2 *)
           exfalso. apply Hne2.
           pose proof (lic_qlt_bool_false_le 2%Q (q * q) H2lt) as Hle2'.
           apply (Qle_antisym (q * q) 2%Q); [exact Hle2' | exact Hge2].
  - (* q ≤ 0 *)
    pose proof (lic_qlt_bool_false_le 0%Q q Hpos) as Hq0.
    destruct q as [qn qd].
    assert (Hqd : (0 < Z.pos qd)%Z) by apply Pos2Z.is_pos.
    exists 1%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus (qn # qd) (ir2_x 1)).
    rewrite (ir2_abs_sub (ir2_x 1) (qn # qd)).
    2: { apply (Qle_trans (qn # qd) 0%Q (ir2_x 1)).
         - exact Hq0.
         - apply Qlt_le_weak. apply (ir2_x_pos 1). }
    rewrite ir2_x1.
    assert (Heq1 : ir2_e 1 == (1#8)%Q) by reflexivity.
    rewrite Heq1.
    unfold Qle in Hq0. cbn [Qnum Qden] in Hq0.
    unfold Qlt, Qminus. cbn [Qnum Qden Qopp Qplus]. lia.
Defined.

(* S7. assembly of the main theorem through the mother theorem by exact
   assembly with no bypass, with the extraction check and the axiom audit *)

Theorem ir2_sqrt2_irrational_criterion : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            ir2_x
                            (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
       (real_const q)))).
Proof.
  intro q.
  exact (lic_irrational_criterion ir2_x ir2_e ir2_tail ir2_escape ir2_vanish q).
Qed.

Separate Extraction ir2_sqrt2_irrational_criterion ir2_tail ir2_vanish
  ir2_escape ir2_x ir2_delta ir2_e ir2_qp ir2_decay ir2_gap_lower
  ir2_gap_upper_small ir2_gap_upper_big ir2_no_sqrt2.

Print Assumptions ir2_sqrt2_irrational_criterion.
(* ================= Section 2. the is3_ family: sqrt 3 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

(* S1. the Z level: 3 has no rational square root, by infinite descent
   with a three-way mod 3 decision *)

Lemma is3_mod3_sq : forall z : Z, ((z * z) mod 3 = 0)%Z -> (z mod 3 = 0)%Z.
Proof.
  intros z H.
  assert (Hr : (z mod 3 = 0)%Z \/ (z mod 3 = 1)%Z \/ (z mod 3 = 2)%Z).
  { pose proof (Z.mod_pos_bound z 3 (ltac:(lia))) as Hb. lia. }
  destruct Hr as [Hr | [Hr | Hr]]; [exact Hr | | ].
  - (* z = 3k+1: z² = 3·(3k²+2k)+1, so mod 3 = 1 ≠ 0 *)
    exfalso.
    pose proof (Z.div_mod z 3 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 3)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 3 * (3 * k * k + 2 * k) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 3 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 3%Z ((3 * k * k + 2 * k)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
  - (* z = 3k+2: z² = 3·(3k²+4k+1)+1, so mod 3 = 1 ≠ 0 *)
    exfalso.
    pose proof (Z.div_mod z 3 (ltac:(lia))) as Hz.
    rewrite Hr in Hz.
    remember (z / 3)%Z as k eqn:Ek.
    assert (Hsq : (z * z = 3 * (3 * k * k + 4 * k + 1) + 1)%Z).
    { rewrite Hz at 1 2. ring. }
    rewrite Hsq in H.
    assert (Hm : ((z * z) mod 3 = 1)%Z).
    { symmetry. apply (Zmod_unique ((z * z)%Z) 3%Z ((3 * k * k + 4 * k + 1)%Z) 1%Z); lia. }
    rewrite Hsq in Hm. rewrite Hm in H. lia.
Qed.

Lemma is3_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 3 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 3 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* a divisible by 3, b divisible by 3, and b strictly decreases *)
      assert (Ham : ((a * a) mod 3 = 0)%Z).
      { rewrite Heq.
        symmetry. apply (Zmod_unique ((3 * (b * b))%Z) 3%Z ((b * b)%Z) 0%Z); lia. }
      assert (Hae : (a mod 3 = 0)%Z) by (apply is3_mod3_sq; exact Ham).
      pose proof (Z.div_mod a 3 (ltac:(lia))) as Hza. rewrite Hae in Hza.
      remember (a / 3)%Z as a1 eqn:Ea1.
      assert (Ha1 : (a = 3 * a1)%Z) by lia.
      clear Hza Ea1 Hae Ham.
      assert (Hbb : (b * b = 3 * (a1 * a1))%Z).
      { rewrite Ha1 in Heq.
        replace ((3 * a1)%Z * (3 * a1)%Z)%Z with (9 * (a1 * a1)%Z)%Z in Heq by ring.
        replace (9 * (a1 * a1)%Z)%Z with (3 * (3 * (a1 * a1)%Z)%Z)%Z in Heq by ring.
        lia. }
      assert (Hbm : ((b * b) mod 3 = 0)%Z).
      { rewrite Hbb.
        symmetry. apply (Zmod_unique ((3 * (a1 * a1))%Z) 3%Z ((a1 * a1)%Z) 0%Z); lia. }
      assert (Hbe : (b mod 3 = 0)%Z) by (apply is3_mod3_sq; exact Hbm).
      pose proof (Z.div_mod b 3 (ltac:(lia))) as Hzb. rewrite Hbe in Hzb.
      remember (b / 3)%Z as b1 eqn:Eb1.
      assert (Hb1 : (b = 3 * b1)%Z) by lia.
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((3 * b1)%Z * (3 * b1)%Z)%Z with (9 * (b1 * b1)%Z)%Z in Hbb by ring.
        replace (9 * (b1 * b1)%Z)%Z with (3 * (3 * (b1 * b1)%Z)%Z)%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

Lemma is3_no_sqrt3 : forall q : Q, ~ (q * q == 3%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 3 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    lia. }
  exact (is3_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* S2. the Newton sequence (x_0 = 2, step (x+3/x)/2) and its basic
   Q-level quantities *)

Fixpoint is3_x (n : nat) : Q :=
  match n with
  | O => 2%Q
  | Datatypes.S m => (is3_x m + 3%Q / is3_x m) * (1 # 2)
  end.

Definition is3_delta (n : nat) : Q := is3_x n * is3_x n - 3%Q.
Definition is3_e (n : nat) : Q := (1 # 2) * is3_delta n.

Lemma is3_x1 : is3_x 1 == (7 # 4).
Proof. reflexivity. Qed.

(* 7j² ≤ 2^{j+8}, the is3_pow3sq shape; it serves the strict window
   7·den² ≤ qp(SN) of the q²<3 branch *)
Lemma is3_step7 : forall j : nat, (3 <= j)%nat -> (14 * j + 7 <= 7 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (7 * Datatypes.S j * Datatypes.S j)%nat
      with (7 * j * j + 14 * j + 7)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|j']]; lia.
Qed.

Lemma is3_pow7sq : forall j : nat, (7 * j * j <= 2 ^ (j + 8))%nat.
Proof.
  assert (Haux : forall j : nat, (7 * j * j <= 2 ^ (8 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (8 + Datatypes.S j)%nat with (Datatypes.S (8 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (7 * Datatypes.S j * Datatypes.S j)%nat
          with (7 * j * j + 14 * j + 7)%nat by ring.
        pose proof (is3_step7 j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 8). apply Haux.
Qed.

(* S3. basic properties of the sequence (positivity, lower bound 5/3,
   monotonicity, δ algebra) *)

(* 3/x > 0 for x > 0 *)
Lemma is3_div3_pos : forall v : Q, Qlt 0 v -> Qlt 0 (3%Q / v).
Proof.
  intros v Hv. unfold Qdiv.
  apply (Qmult_lt_0_compat (3#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma is3_x_pos : forall n : nat, Qlt 0 (is3_x n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [is3_x Qnum Qden]. lia.
  - cbn [is3_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | apply is3_div3_pos; exact IH].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma is3_delta_succ_mul : forall n : nat,
  (is3_delta (Datatypes.S n) * (4 * (is3_x n * is3_x n)) == is3_delta n * is3_delta n)%Q.
Proof.
  intro n. unfold is3_delta. cbn [is3_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (is3_x n) (is3_x_pos n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma is3_delta_ge0 : forall n : nat, Qle 0 (is3_delta n).
Proof.
  induction n as [|n IH].
  - unfold is3_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [is3_x Qnum Qden]. lia.
  - assert (HM : Qlt 0%Q (4 * (is3_x n * is3_x n))).
    { apply (Qmult_lt_0_compat (4#1) (is3_x n * is3_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (is3_x n) (is3_x n)); exact (is3_x_pos n). }
    pose proof (is3_delta_succ_mul n) as Hmul.
    assert (Hsq : Qle 0 (is3_delta n * is3_delta n)).
    { destruct (is3_delta n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma is3_delta_pos : forall n : nat, Qlt 0 (is3_delta n).
Proof.
  intro n. pose proof (is3_delta_ge0 n) as Hge.
  destruct (Qeq_dec (is3_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (is3_no_sqrt3 (is3_x n)).
    unfold is3_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (is3_x n * is3_x n) 3%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (is3_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (is3_delta n) 0%Q Hle Hge).
Qed.

Lemma is3_sq_ge3 : forall n : nat, Qle 3%Q (is3_x n * is3_x n).
Proof.
  intro n. pose proof (is3_delta_ge0 n) as H.
  assert (Hr : ((is3_x n * is3_x n - 3) + 3 == is3_x n * is3_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 3%Q (0%Q + 3%Q)%Q ((is3_x n * is3_x n - 3)%Q + 3%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma is3_x_lb : forall n : nat, (5 # 3) <= is3_x n.
Proof.
  intro n. pose proof (is3_x_pos n) as Hp.
  destruct (Qlt_le_dec (is3_x n) (5#3)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((is3_x n) * (is3_x n)) ((5#3) * (is3_x n))).
    { apply (Qmult_lt_compat_r (is3_x n) (5#3) (is3_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((5#3) * (is3_x n)) ((5#3) * (5#3))).
    { rewrite (Qmult_comm (5#3) (is3_x n)).
      apply (Qmult_lt_compat_r (is3_x n) (5#3) (5#3)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (is3_x n * is3_x n) 3%Q).
    { apply (Qlt_trans _ ((5#3) * (5#3))).
      - apply (Qlt_trans _ ((5#3) * (is3_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (is3_x n * is3_x n) 3%Q).
    + exact H3.
    + apply is3_sq_ge3.
  - exact Hle.
Qed.

Lemma is3_mono : forall n : nat, is3_x (Datatypes.S n) <= is3_x n.
Proof.
  intro n. cbn [is3_x].
  pose proof (is3_sq_ge3 n) as H3.
  pose proof (is3_x_pos n) as Hxp.
  destruct (is3_x n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H3c : (3 * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H3 as H3'. rewrite ?Ex in H3'.
    unfold Qle, Qmult in H3'. cbn [Qnum Qden] in H3'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0. apply qeqT_imp_qeq in Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle (3%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H3 | exact Hivp].
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               (3%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2))
                   == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma is3_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  is3_x k <= is3_x n.
Proof.
  intros n k Hn1 Hnk.
  assert (Hgen : forall d : nat, is3_x (n + d) <= is3_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (is3_x (n + d))).
      + apply is3_mono.
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

Lemma is3_x_ub : forall n : nat, (1 <= n)%nat -> is3_x n <= (7 # 4).
Proof.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply (Qle_trans _ (is3_x 1)).
    + apply (is3_mono_le 1 (Datatypes.S n')); lia.
    + rewrite is3_x1. apply Qle_refl.
Qed.

(* S4. decay of the error window (δ ≤ 1/16; δ(Sn) ≤ δn/176;
   e_n ≤ 1/2^{n+1}) *)

Lemma is3_delta_step : forall n : nat, (1 <= n)%nat -> Qle (is3_delta n) (1#16) ->
  Qle (is3_delta (Datatypes.S n)) ((1#176) * is3_delta n).
Proof.
  intros n Hn1 Hdu.
  pose proof (is3_x_pos n) as Hxp.
  assert (Hlb : Qle ((5#3) * (5#3)) (is3_x n * is3_x n)).
  { apply (Qle_trans _ ((5#3) * is3_x n)%Q).
    - apply ir2_mult_le_compat_l; [apply (is3_x_lb n) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r; [apply (is3_x_lb n) | apply Qlt_le_weak; apply (is3_x_pos n)]. }
  assert (H11 : Qle 11%Q (4 * (is3_x n * is3_x n))).
  { apply (Qle_trans _ ((4#1) * ((5#3) * (5#3)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((5#3) * (5#3))).
      rewrite (Qmult_comm (4#1) (is3_x n * is3_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (is3_delta_succ_mul n) as Hmul.
  pose proof (is3_delta_ge0 (Datatypes.S n)) as HdS0.
  assert (Ha : Qle (11 * is3_delta (Datatypes.S n)) (is3_delta n * is3_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (is3_delta (Datatypes.S n)) (4 * (is3_x n * is3_x n))).
    apply Qmult_le_compat_r; [exact H11 | exact HdS0]. }
  assert (Hb : Qle (is3_delta n * is3_delta n) ((1#16) * is3_delta n)).
  { apply (Qmult_le_compat_r (is3_delta n) (1#16) (is3_delta n));
      [exact Hdu | apply (is3_delta_ge0 n)]. }
  assert (Hc : Qle (11 * is3_delta (Datatypes.S n)) ((1#16) * is3_delta n))
    by (apply (Qle_trans _ (is3_delta n * is3_delta n)); assumption).
  apply (Qle_trans (is3_delta (Datatypes.S n))
    (((1#16) * is3_delta n) * Qinv (11#1)) ((1#176) * is3_delta n)).
  - apply (ir2_le_mul_inv (is3_delta (Datatypes.S n)) ((1#16) * is3_delta n) (11#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (is3_delta (Datatypes.S n)) (11#1)). exact Hc.
  - assert (Hc2 : Qinv (11#1) == (1#11)%Q) by reflexivity.
    rewrite Hc2. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

Lemma is3_sixteenth : forall n : nat, (1 <= n)%nat -> Qle (is3_delta n) (1#16).
Proof.
  induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + change (is3_delta 1) with (1 # 16)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + intro Hle0. assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#176) * is3_delta (Datatypes.S n))).
      * apply (is3_delta_step (Datatypes.S n)); [lia | exact Hdu].
      * apply (Qle_trans _ ((1#176) * (1#16))%Q).
        -- apply ir2_mult_le_compat_l; [exact Hdu | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma is3_e_step : forall n : nat, (1 <= n)%nat ->
  Qle (is3_e (Datatypes.S n)) ((1#2) * is3_e n).
Proof.
  intros n Hn1. unfold is3_e.
  apply (Qle_trans _ ((1#2) * ((1#176) * is3_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (is3_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#176) * is3_delta n)).
    pose proof (is3_sixteenth n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + apply (is3_delta_step n); [exact Hn1 | exact Hdu].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (is3_delta n) as [dn dd] eqn:Edn.
    pose proof (is3_delta_ge0 n) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.

Lemma is3_e_to_delta : forall n : nat,
  (is3_e n * ir2_qp (Datatypes.S n) == is3_delta n * ir2_qp n)%Q.
Proof.
  intro n. unfold is3_e. rewrite ir2_qp_def. ring.
Qed.

Lemma is3_decay : forall n : nat,
  Qle (is3_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - change (is3_e 1) with (1 # 32)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1#2) * is3_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * apply (is3_e_step (Datatypes.S n)). lia.
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * is3_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (is3_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact IH.
Qed.

Lemma is3_delta_pow_le : forall n : nat, (1 <= n)%nat ->
  Qle (is3_delta n * ir2_qp n) 1%Q.
Proof.
  intros n Hn. rewrite <- (is3_e_to_delta n).
  destruct n as [|n'].
  - lia.
  - apply (is3_decay n').
Qed.

(* S5. escape gap lemmas (a decidable Q-layer gap between √3 and any
   rational) *)

(* the lower gap: q²<3 gives (3−q²)·(2/7) ≤ x_N−q (x_N ≤ 7/4, so
   1/(x_N+q) ≥ 2/7) *)
Lemma is3_gap_lower : forall u v : Q,
  Qle 0 v -> Qle v u -> Qle u (7#4) -> Qle 3 (u*u) -> Qlt (v*v) 3 ->
  Qle ((3 - v*v) * (2#7)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H3 Hsq.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); assumption).
  assert (Huv0 : Qlt 0%Q (u + v)).
  { destruct (Qlt_le_dec 0%Q (u + v)) as [Hlt | Hle].
    - exact Hlt.
    - exfalso.
      assert (Huu : Qle u (u + v)).
      { apply (Qle_trans u (u + 0%Q) (u + v)).
        - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qplus_0_r.
        - apply (Qplus_le_compat u u 0%Q v); [apply Qle_refl | exact Hv0]. }
      assert (Hu : u == 0%Q).
      { apply (Qle_antisym u 0%Q).
        - apply (Qle_trans u (u + v) 0%Q); [exact Huu | exact Hle].
        - exact Hu0. }
      pose proof H3 as H3'. rewrite Hu in H3'.
      unfold Qle, Qmult in H3'. cbn [Qnum Qden] in H3'.
      clear Hu Huu Hle. lia. }
  assert (Hne : ~ ((u + v)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u + v) Huv0); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u - v) == (u*u - v*v) * Qinv (u + v))%Q).
  { pose proof (bno_mul_div_self (u + v) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u - v) * (u + v)) * Qinv (u + v)) == (u - v))%Q).
    { rewrite <- (Qmult_assoc (u - v) (u + v) (Qinv (u + v))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hw0 : Qle 0%Q (3 - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) 3%Q Hsq)).
  assert (Hub2 : Qle (u + v) (7#2)).
  { apply (Qle_trans _ ((7#4) + (7#4))%Q).
    - apply (Qplus_le_compat u (7#4) v (7#4)).
      + exact Hub.
      + apply (Qle_trans v u (7#4)); assumption.
    - unfold Qle, Qplus, Qmult. cbn [Qnum Qden]. lia. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ ((3 - v*v) * Qinv (u + v))%Q).
    + apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) (7#2)); [exact Huv0 | exact Hub2].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H3.
      * exact Hivp.
  - apply Qle_refl.
Qed.

(* the small upper gap: 3<q²≤(7/4)² and d ≤ (4/11)(v²−3) give d/2 < v−u
   (the strictness comes from 11 < 12 = 4·3, that is
   1/(3b²) < (4/11)/b²) *)
Lemma is3_gap_upper_small : forall u v d : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt u v -> Qle v (7#4) -> Qlt 3 (v*v) ->
  d == (u*u - 3) -> Qle 0 d -> Qle d ((4#11) * (v*v - 3)) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Hv0 Huv Hv74 Hsq Hd Hdu Hdle.
  assert (Hw0 : Qlt 0 (v*v - 3)) by (apply (lic_qlt_0_minus 3%Q (v*v)); exact Hsq).
  assert (Hpu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; assumption).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 3) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
    destruct v as [vn vd].
    unfold Qlt, Qle, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hvup : Qlt (v + u) (7#2)).
  { apply (Qlt_le_trans (v + u) (v + v) (7#2)).
    - apply (lic_qlt_add_l v u v Huv).
    - apply (Qle_trans _ ((7#4) + (7#4))%Q).
      + apply (Qplus_le_compat v (7#4) v (7#4)); [exact Hv74 | exact Hv74].
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity. }
  apply (Qle_lt_trans (d * (1#2)) ((v*v - u*u) * (2#7)) (v - u)).
  - apply (Qle_trans _ ((2#11) * (v*v - 3))%Q).
    + destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
      rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
      unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
      cbn [Qnum Qden Qplus] in *.
      assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
      assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      lia.
    + assert (H711 : Qle ((7#11) * (v*v - 3)) (v*v - u*u)).
      { rewrite Hsh.
        destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
        rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
        destruct v as [vn vd].
        unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
        cbn [Qnum Qden Qplus] in *.
        assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
        assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
        nia. }
      assert (Hr27 : (((2#11) * (v*v - 3)) == ((2#7) * ((7#11) * (v*v - 3))))%Q)
        by ring.
      apply (Qle_trans _ ((2#7) * ((7#11) * (v*v - 3)))%Q).
      * rewrite Hr27. apply Qle_refl.
      * rewrite (Qmult_comm (2#7) ((7#11) * (v*v - 3))).
        apply Qmult_le_compat_r; [exact H711 | unfold Qle; cbn; lia].
  - rewrite Hbridge.
    rewrite (Qmult_comm (v*v - u*u) (2#7)).
    rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
    apply (Qmult_lt_compat_r (2#7) (Qinv (v + u)) (v*v - u*u)).
    + exact Hvu2.
    + apply (ir2_inv_lt (7#2) (v + u)).
      * unfold Qlt. cbn [Qnum Qden]. lia.
      * exact Hpu.
      * exact Hvup.
Qed.

(* the big upper gap: q > 7/4 and (v+1)d ≤ v²−3 give d/2 < v−u,
   independent of the constants *)
Lemma is3_gap_upper_big : forall u v d : Q,
  Qlt 0 u -> Qlt u v -> (7#4) <= v -> Qlt 3 (v*v) ->
  d == (u*u - 3) -> Qle 0 d -> Qle ((v + 1) * d) (v*v - 3) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Huv Hv74 Hsq Hd Hdu Hd1.
  assert (Hw0 : Qlt 0 (v*v - 3)) by (apply (lic_qlt_0_minus 3%Q (v*v)); exact Hsq).
  assert (Hvp : Qlt 0 v).
  { apply (Qlt_le_trans 0%Q (7#4) v); [unfold Qlt; cbn; lia | exact Hv74]. }
  assert (Hpvu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; [exact Hvp | exact Hu0]).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpvu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 3) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qle 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (H2vp : Qlt 0%Q ((2#1) * v)).
  { apply (Qmult_lt_0_compat (2#1) v); [unfold Qlt; cbn; lia | exact Hvp]. }
  assert (Huv2 : Qle (v + u) ((2#1) * v)).
  { apply (Qle_trans (v + u) (v + v) ((2#1) * v)).
    - apply (Qplus_le_compat v v u v); [apply Qle_refl | apply Qlt_le_weak; exact Huv].
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hdv : Qle (d * v) ((v*v - 3) - d)).
  { destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hkey : Qle (d * (1#2)) (((v*v - 3) - d) * Qinv ((2#1) * v))).
  { apply (ir2_le_mul_inv (d * (1#2)) ((v*v - 3) - d) ((2#1) * v)).
    - exact H2vp.
    - assert (Hring : (((d * (1#2)) * ((2#1) * v)) == (d * v))%Q) by ring.
      rewrite Hring. exact Hdv. }
  assert (Hvu2p : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 3)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  apply (Qle_lt_trans (d * (1#2)) (((v*v - 3) - d) * Qinv ((2#1) * v)) (v - u)).
  - exact Hkey.
  - apply (Qle_lt_trans (((v*v - 3) - d) * Qinv ((2#1) * v))
            ((v*v - u*u) * Qinv ((2#1) * v)) (v - u)).
    + assert (Hle2 : Qle (v*v - 3 - d) (v*v - u*u)).
      { rewrite Hd. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
      apply Qmult_le_compat_r; [exact Hle2 | apply ir2_inv_pos; exact H2vp].
    + rewrite Hbridge.
      rewrite (Qmult_comm (v*v - u*u) (Qinv ((2#1) * v))).
      rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
      apply (Qmult_lt_compat_r (Qinv ((2#1) * v)) (Qinv (v + u)) (v*v - u*u)).
      * exact Hvu2p.
      * apply (ir2_inv_lt ((2#1) * v) (v + u)).
        -- exact H2vp.
        -- exact Hpvu.
        -- assert (Hr2 : (v + v == (2#1) * v)%Q) by ring.
           rewrite <- Hr2. apply (lic_qlt_add_l v u v Huv).
Qed.

(* S6. the three premise instances of the mother theorem (tail control,
   window vanishing, escape window) *)

Definition is3_tail : lic_tail_bounded is3_x is3_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (is3_mono_le n k Hn1 Hnk) as Hmono.
  pose proof (is3_delta_ge0 n) as Hd0n.
  pose proof (is3_delta_pos n) as Hdpn.
  assert (Habs : Qabs ((is3_x k - is3_x n)%Q) == (is3_x n - is3_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (is3_x n + is3_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (5#3) (is3_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is3_x_lb n).
    - apply (Qlt_le_trans 0%Q (5#3) (is3_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (is3_x_lb k). }
  assert (Hsumne : ~ ((is3_x n + is3_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (is3_x n + is3_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((is3_x n - is3_x k)
                      == (is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))%Q)).
  { pose proof (bno_mul_div_self (is3_x n + is3_x k) Hsumne) as Hb. apply qeqT_imp_qeq in Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((is3_x n - is3_x k) * (is3_x n + is3_x k))
                    * Qinv (is3_x n + is3_x k)) == (is3_x n - is3_x k))%Q).
    { rewrite <- (Qmult_assoc (is3_x n - is3_x k) (is3_x n + is3_x k)
                    (Qinv (is3_x n + is3_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((is3_x n * is3_x n - is3_x k * is3_x k)
                   == (is3_delta n - is3_delta k))%Q)
      by (unfold is3_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((10#3)) (is3_x n + is3_x k)).
  { apply (Qle_trans _ ((5#3) + (5#3))%Q).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
    - apply (Qplus_le_compat (5#3) (is3_x n) (5#3) (is3_x k));
        [apply (is3_x_lb n) | apply (is3_x_lb k)]. }
  assert (Hinvp : Qle 0%Q (Qinv (is3_x n + is3_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))
                     (is3_delta n * Qinv (is3_x n + is3_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (is3_delta n) as [dn dd] eqn:Edn.
      destruct (is3_delta k) as [ek ed] eqn:Edk.
      pose proof (is3_delta_ge0 k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (is3_delta n * Qinv (is3_x n + is3_x k))
                     (is3_delta n * Qinv ((10#3)))).
  { rewrite (Qmult_comm (is3_delta n) (Qinv (is3_x n + is3_x k))).
    rewrite (Qmult_comm (is3_delta n) (Qinv ((10#3)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (10#3) (is3_x n + is3_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (is3_delta n * Qinv ((10#3))) ((1#2) * is3_delta n)).
  { destruct (is3_delta n) as [dn dd] eqn:Edn.
    pose proof (is3_delta_pos n) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((is3_delta n - is3_delta k) * Qinv (is3_x n + is3_x k))
          (is3_delta n * Qinv (is3_x n + is3_x k)) ((1#2) * is3_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (is3_delta n * Qinv (is3_x n + is3_x k))
            (is3_delta n * Qinv ((10#3))) ((1#2) * is3_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition is3_vanish : lic_vanish is3_e.
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (Z.to_nat (Z.pos pd) + 1)%nat.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans (is3_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (is3_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (is3_e (Datatypes.S n'))).
        apply (is3_decay n').
    + apply (Qlt_le_trans (Qinv (ir2_qp (Datatypes.S (Datatypes.S n'))))
              (Qinv (Z.pos pd # 1)) ((pn # pd)%Q)).
      * apply (ir2_inv_lt (ir2_qp (Datatypes.S (Datatypes.S n'))) (Z.pos pd # 1)).
        -- apply ir2_qp_pos.
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- rewrite ir2_qp_pow.
           replace (Datatypes.S (Datatypes.S n'))%nat with (n' + 2)%nat by lia.
           assert (Hzc : (Z.pos pd <= Z.of_nat n')%Z).
           { assert (Hle : (Z.to_nat (Z.pos pd) + 1 <= Datatypes.S n')%nat) by lia.
             pose proof (proj1 (Nat2Z.inj_le _ _) Hle) as Hz.
             rewrite Nat2Z.inj_add, Nat2Z.inj_succ in Hz.
             pose proof (Z2Nat.id (Z.pos pd) (ltac:(lia))) as Hz2.
             cbn in Hz. lia. }
           pose proof (proj1 (Nat2Z.inj_le _ _) (ir2_pow_ge (n' + 2))) as Hpg.
           unfold Qlt. cbn [Qnum Qden]. lia.
      * unfold Qle, Qinv. cbn [Qnum Qden]. nia.
Qed.

Definition is3_escape : lic_escape_window is3_x is3_e.
Proof.
  intro q.
  destruct (Qlt_bool 0%Q q) eqn:Hpos.
  - pose proof (lic_qlt_bool_true 0%Q q Hpos) as Hq0.
    destruct (Qlt_bool (q * q) 3%Q) eqn:H3b.
    + (* q² < 3: take N := den(q) + 8; x_N overtakes q from above *)
      pose proof (lic_qlt_bool_true (q * q) 3%Q H3b) as H3.
      destruct q as [a b].
      assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
      assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
      { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
        exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
        rewrite Ek in Hz. cbn in Hz. lia. }
      exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hxsq : Qle 3%Q (is3_x (Z.to_nat (Z.pos b) + 8)
                                * is3_x (Z.to_nat (Z.pos b) + 8)))
        by apply is3_sq_ge3.
      assert (Hqx : Qlt ((a # b) * (a # b))
                    (is3_x (Z.to_nat (Z.pos b) + 8)
                     * is3_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (Qlt_le_trans ((a # b) * (a # b)) 3%Q
                    (is3_x (Z.to_nat (Z.pos b) + 8)
                     * is3_x (Z.to_nat (Z.pos b) + 8))); assumption).
      assert (Hqle : Qlt (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (ir2_lt_of_sq (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b));
            [apply Qlt_le_weak; apply (is3_x_pos (Z.to_nat (Z.pos b) + 8))
            | apply Qlt_le_weak; exact Hq0 | exact Hqx]).
      assert (Habs : Qabs ((a # b) - is3_x (Z.to_nat (Z.pos b) + 8))%Q
                     == (is3_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      { rewrite Qabs_Qminus. apply ir2_abs_sub. apply Qlt_le_weak. exact Hqle. }
      rewrite Habs.
      apply (Qlt_le_trans (is3_e (Z.to_nat (Z.pos b) + 8))
              (Qinv ((7 * (Z.pos b * Z.pos b)) # 1))
              (is3_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      * apply (Qle_lt_trans (is3_e (Z.to_nat (Z.pos b) + 8))
                (Qinv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8))))
                (Qinv ((7 * (Z.pos b * Z.pos b)) # 1))).
        -- apply (ir2_le_inv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   (is3_e (Z.to_nat (Z.pos b) + 8))).
           ++ apply ir2_qp_pos.
           ++ rewrite (Qmult_comm (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                       (is3_e (Z.to_nat (Z.pos b) + 8))).
              replace (Z.to_nat (Z.pos b) + 8)%nat
                with (Datatypes.S (Z.to_nat (Z.pos b) + 7))%nat by lia.
              apply (is3_decay (Z.to_nat (Z.pos b) + 7)).
        -- apply (ir2_inv_lt (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   ((7 * (Z.pos b * Z.pos b)) # 1)).
           ++ apply ir2_qp_pos.
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ rewrite ir2_qp_pow.
              replace (Datatypes.S (Z.to_nat (Z.pos b) + 8))%nat
                with (Z.to_nat (Z.pos b) + 8 + 1)%nat by lia.
              assert (Hb3 : (2 ^ (Z.to_nat (Z.pos b) + 8 + 1)
                             = 2 * 2 ^ (Z.to_nat (Z.pos b) + 8))%nat)
                by (rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm; reflexivity).
              assert (Hzp : (1 <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow_ge (Z.to_nat (Z.pos b) + 8)) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite Nat2Z.inj_succ in Hp. lia. }
              assert (Hz : (7 * (Z.pos b * Z.pos b)
                            <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (is3_pow7sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp.
                rewrite Hkb in Hp. cbn [Z.of_nat] in Hp. lia. }
              pose proof (f_equal Z.of_nat Hb3) as Hb4.
              rewrite Nat2Z.inj_mul in Hb4. cbn [Z.of_nat] in Hb4.
              unfold Qlt. cbn [Qnum Qden]. lia.
      * apply (Qle_trans _ ((3 - (a # b) * (a # b))
                             * (2#7))%Q).
        -- apply (ir2_ge_inv ((7 * (Z.pos b * Z.pos b)) # 1)
                   (((3 - (a # b) * (a # b)) * (2#7))%Q)).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ unfold Qle, Qmult, Qminus.
              pose proof H3 as H3'. unfold Qlt, Qmult, Qminus in H3'.
              cbn [Qnum Qden Qplus Qopp] in H3' |- *.
              assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
              nia.
        -- apply (is3_gap_lower (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b)).
           ++ apply Qlt_le_weak. exact Hq0.
           ++ apply Qlt_le_weak. exact Hqle.
           ++ apply is3_x_ub. lia.
           ++ exact Hxsq.
           ++ exact H3.
    + (* 3 ≤ q² *)
      pose proof (lic_qlt_bool_false_le (q * q) 3%Q H3b) as Hge3.
      destruct (Qeq_dec (q * q) 3%Q) as [Heq3 | Hne3].
      * exfalso. exact (is3_no_sqrt3 q Heq3).
      * destruct (Qlt_bool 3%Q (q * q)) eqn:H3lt.
        -- pose proof (lic_qlt_bool_true 3%Q (q * q) H3lt) as Hlt3.
           destruct (Qlt_bool (7#4) q) eqn:H74b.
           ++ (* 7/4 < q: take N := num(q) + den(q) + 1; x_N approaches
                 q from below *)
              pose proof (lic_qlt_bool_true (7#4) q H74b) as H74.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (H74z : (7 * Z.pos b < 4 * a)%Z).
              { pose proof H74 as H74'. unfold Qlt in H74'.
                cbn [Qnum Qden] in H74'. lia. }
              assert (Hz3 : (3 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt3 as H3'. unfold Qlt, Qmult in H3'.
                cbn [Qnum Qden] in H3'. lia. }
              assert (Hkba : Z.of_nat (Z.to_nat a) = a)
                by (apply Z2Nat.id; lia).
              assert (Hkbb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b)
                by (apply Z2Nat.id; lia).
              assert (HpowN : ((a + Z.pos b) * Z.pos b
                               <= Z.of_nat (2 ^ (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)))%Z).
              { replace (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat
                  with (Datatypes.S (Z.to_nat a + Z.to_nat (Z.pos b))) by lia.
                rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r.
                pose proof (ir2_pow_ge (Z.to_nat a)) as H1.
                pose proof (ir2_pow_ge (Z.to_nat (Z.pos b))) as H2.
                apply (proj1 (Nat2Z.inj_le _ _)) in H1.
                apply (proj1 (Nat2Z.inj_le _ _)) in H2.
                rewrite Nat2Z.inj_succ in H1, H2.
                pose proof (Z2Nat.id a (ltac:(lia))) as Hz3w.
                pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz4w.
                rewrite Hz3w in H1. rewrite Hz4w in H2.
                rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
                nia. }
              exists (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hdpow : Qle (is3_delta (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)
                                    * ir2_qp (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)) 1%Q).
              { apply (is3_delta_pow_le). lia. }
              assert (Hbnd : Qle (((a # b) + 1)
                                  * is3_delta (Z.to_nat a
                                               + Z.to_nat (Z.pos b) + 1))
                           (((a # b) * (a # b)) - 3%Q)%Q).
              { apply (Qle_trans _ (((a # b) + 1)
                                    * Qinv (ir2_qp (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1)))%Q).
                - apply ir2_mult_le_compat_l.
                  + apply (ir2_le_inv (ir2_qp (Z.to_nat a
                                          + Z.to_nat (Z.pos b) + 1))
                              (is3_delta (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1))).
                    * apply ir2_qp_pos.
                    * rewrite (Qmult_comm (ir2_qp (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                                (is3_delta (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1))).
                      exact Hdpow.
                  + apply (Qle_trans 0%Q (a # b) ((a # b) + 1)%Q).
                    * apply Qlt_le_weak. exact Hq0.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_lt_add_r (a # b) 1%Q).
                      unfold Qlt. cbn [Qnum Qden]. lia.
                - rewrite (ir2_qp_pow (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                  assert (Hzp1 : (1 <= Z.of_nat (2 ^ (Z.to_nat a
                                                   + Z.to_nat (Z.pos b) + 1)))%Z).
                  { pose proof (ir2_pow_ge (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hp.
                    apply (proj1 (Nat2Z.inj_le _ _)) in Hp. lia. }
                  destruct (Z.of_nat (2 ^ (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1)))
                    as [|pp|pp] eqn:Ez; try lia.
                  rewrite ?Ez in HpowN.
                  unfold Qle, Qmult, Qminus, Qinv.
                  cbn [Qnum Qden Qplus Qopp] in HpowN |- *.
                  assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                  nia. }
              assert (Hdl : Qlt (is3_delta (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                            (((a # b) * (a # b)) - 3%Q)%Q).
              { destruct (is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                  as [dn dd] eqn:Ed.
                rewrite (ir2_qp_pow (Z.to_nat a
                          + Z.to_nat (Z.pos b) + 1)) in Hdpow.
                rewrite ?Ed in Hdpow, Hbnd.
                pose proof (is3_delta_pos (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hdp3.
                rewrite ?Ed in Hdp3.
                unfold Qle, Qlt in *.
                cbn [Qnum Qden Qmult Qminus Qopp Qplus] in *.
                assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                nia. }
              assert (Hxq : Qlt (is3_x (Z.to_nat a
                                       + Z.to_nat (Z.pos b) + 1))
                                (a # b)).
              { apply (ir2_lt_of_sq (a # b)
                        (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak.
                  apply (is3_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                - pose proof Hdl as Hdl'.
                  unfold is3_delta in Hdl'.
                  pose proof (lic_qlt_minus_add_r ((a # b) * (a # b)) 3%Q)
                    as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                                3%Q) as Hr2.
                  apply (Qle_lt_trans
                          (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                           * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                          ((is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            - 3%Q) + 3%Q)%Q
                          ((a # b) * (a # b))).
                  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
                    exact (Qeq_sym _ _ Hr2).
                  + apply (lic_qlt_comp_r
                              (((a # b) * (a # b) - 3%Q) + 3%Q)%Q
                              ((a # b) * (a # b))
                              ((is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                - 3%Q) + 3%Q)%Q).
                    * exact Hr1.
                    * apply (lic_qlt_add_r
                                (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 - 3%Q)%Q
                                ((a # b) * (a # b) - 3%Q)%Q
                                3%Q Hdl'). }
              assert (HeqN : (is3_e (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                              == is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                  * (1#2))%Q).
              { unfold is3_e. ring. }
              rewrite HeqN.
              rewrite (ir2_abs_sub (a # b)
                        (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)))
                by (apply Qlt_le_weak; exact Hxq).
              apply (is3_gap_upper_big
                      (is3_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                      (a # b)
                      (is3_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
              ** apply (is3_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hxq.
              ** apply Qlt_le_weak. exact H74.
              ** exact Hlt3.
              ** reflexivity.
              ** apply (is3_delta_ge0 (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hbnd.
           ++ (* 3 < q² and q ≤ 7/4: take N := den(q) + 8 with window
                 4/11; x_N overtakes q from below *)
              pose proof (lic_qlt_bool_false_le (7#4) q H74b) as H74.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
              assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
              { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
                exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
                rewrite Ek in Hz. cbn in Hz. lia. }
              assert (Hq3z : (3 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt3 as H3'. unfold Qlt, Qmult in H3'.
                cbn [Qnum Qden] in H3'. lia. }
              exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hpow3 : (3 * (Z.pos b * Z.pos b)
                               <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp. rewrite Hkb in Hp.
                cbn [Z.of_nat] in Hp. lia. }
              assert (Hdpow : Qle (is3_delta (Z.to_nat (Z.pos b) + 8)
                                    * ir2_qp (Z.to_nat (Z.pos b) + 8)) 1%Q)
                by (apply is3_delta_pow_le; lia).
              rewrite (ir2_qp_pow (Z.to_nat (Z.pos b) + 8)) in Hdpow.
              assert (H411 : Qlt (is3_delta (Z.to_nat (Z.pos b) + 8))
                              (((4#11) * (((a # b) * (a # b)) - 3%Q))%Q)).
              { destruct (is3_delta (Z.to_nat (Z.pos b) + 8)) as [dn dd] eqn:Ed.
                rewrite ?Ed in Hdpow.
                pose proof (is3_delta_pos (Z.to_nat (Z.pos b) + 8)) as Hdp.
                rewrite Ed in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
                unfold Qle, Qlt, Qmult in Hdpow. cbn [Qnum Qden] in Hdpow.
                unfold Qlt, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp] in Hdp, Hdpow |- *.
                assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                nia. }
              assert (Hdl : Qlt (is3_delta (Z.to_nat (Z.pos b) + 8))
                              ((((a # b) * (a # b)) - 3%Q)%Q)).
              { apply (Qlt_le_trans (is3_delta (Z.to_nat (Z.pos b) + 8))
                        (((4#11) * (((a # b) * (a # b)) - 3%Q))%Q)
                        ((((a # b) * (a # b)) - 3%Q)%Q)).
                - exact H411.
                - apply (Qle_trans _ (1%Q * (((a # b) * (a # b)) - 3%Q))%Q).
                  + apply Qmult_le_compat_r.
                    * unfold Qle. cbn [Qnum Qden]. lia.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_0_minus 3%Q ((a # b) * (a # b)) Hlt3).
                  + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_l. }
              assert (Hqx : Qlt (is3_x (Z.to_nat (Z.pos b) + 8)
                                  * is3_x (Z.to_nat (Z.pos b) + 8))
                            ((a # b) * (a # b))).
              { assert (Hr : (((is3_x (Z.to_nat (Z.pos b) + 8)
                                * is3_x (Z.to_nat (Z.pos b) + 8) - 3%Q) + 3%Q)
                              == (is3_x (Z.to_nat (Z.pos b) + 8)
                                   * is3_x (Z.to_nat (Z.pos b) + 8)))%Q)
                  by apply lic_qlt_minus_add_r.
                rewrite <- Hr.
                apply (Qlt_le_trans _ ((((a # b) * (a # b)) - 3%Q) + 3%Q)%Q).
                - apply (lic_qlt_add_r _ _ 3%Q Hdl).
                - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply lic_qlt_minus_add_r. }
              assert (Hqle : Qlt (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b))
                by (apply (ir2_lt_of_sq (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)));
                    [apply Qlt_le_weak; exact Hq0
                    | apply Qlt_le_weak;
                       apply (is3_x_pos (Z.to_nat (Z.pos b) + 8))
                    | exact Hqx]).
              rewrite (ir2_abs_sub (a # b) (is3_x (Z.to_nat (Z.pos b) + 8)))
                by (apply Qlt_le_weak; exact Hqle).
              assert (Heq8 : (is3_e (Z.to_nat (Z.pos b) + 8)
                              == is3_delta (Z.to_nat (Z.pos b) + 8)
                                  * (1#2))%Q).
              { unfold is3_e. ring. }
              rewrite Heq8.
              apply (is3_gap_upper_small
                      (is3_x (Z.to_nat (Z.pos b) + 8)) (a # b)
                      (is3_delta (Z.to_nat (Z.pos b) + 8))).
              ** apply (is3_x_pos (Z.to_nat (Z.pos b) + 8)).
              ** exact Hq0.
              ** exact Hqle.
              ** exact H74.
              ** exact Hlt3.
              ** reflexivity.
              ** apply (is3_delta_ge0 (Z.to_nat (Z.pos b) + 8)).
              ** apply Qlt_le_weak. exact H411.
        -- (* when ¬(3 < q²) and 3 ≤ q² hold, q² == 3 follows,
              contradicting is3_no_sqrt3 *)
           exfalso. apply Hne3.
           pose proof (lic_qlt_bool_false_le 3%Q (q * q) H3lt) as Hle3'.
           apply (Qle_antisym (q * q) 3%Q); [exact Hle3' | exact Hge3].
  - (* q ≤ 0 *)
    pose proof (lic_qlt_bool_false_le 0%Q q Hpos) as Hq0.
    destruct q as [qn qd].
    assert (Hqd : (0 < Z.pos qd)%Z) by apply Pos2Z.is_pos.
    exists 1%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus (qn # qd) (is3_x 1)).
    rewrite (ir2_abs_sub (is3_x 1) (qn # qd)).
    2: { apply (Qle_trans (qn # qd) 0%Q (is3_x 1)).
         - exact Hq0.
         - apply Qlt_le_weak. apply (is3_x_pos 1). }
    rewrite is3_x1.
    assert (Heq1 : is3_e 1 == (1#32)%Q) by reflexivity.
    rewrite Heq1.
    unfold Qle in Hq0. cbn [Qnum Qden] in Hq0.
    unfold Qlt, Qminus. cbn [Qnum Qden Qopp Qplus]. lia.
Defined.

(* S7. assembly of the main theorem through the mother theorem by exact
   assembly with no bypass, with the extraction check and the axiom audit *)

Theorem is3_sqrt3_irrational_criterion : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            is3_x
                            (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
       (real_const q)))).
Proof.
  intro q.
  exact (lic_irrational_criterion is3_x is3_e is3_tail is3_escape is3_vanish q).
Qed.

Separate Extraction is3_sqrt3_irrational_criterion is3_tail is3_vanish
  is3_escape is3_x is3_delta is3_e is3_decay is3_gap_lower
  is3_gap_upper_small is3_gap_upper_big is3_no_sqrt3.

Print Assumptions is3_sqrt3_irrational_criterion.
