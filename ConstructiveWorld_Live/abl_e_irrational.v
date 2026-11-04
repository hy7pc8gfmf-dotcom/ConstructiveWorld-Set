(* ConstructiveWorld-Set -- constructive irrationality certificates for classical constants. *)

(** * abl_e_irrational: irrationality of e with explicit computable apartness witnesses.

    Mission.  The irrationality of [e], the limit of the partial sums of the
      exponential series, delivered constructively: for every rational [q = a/b]
      there are a computable index [n] and a positive rational [eps] such that
      every partial sum from index [n] on stays at distance greater than [eps]
      from [q], as a [Set]-level [sigT] statement with boolean comparison
      faces.  The mechanism constructivizes the Fourier 1815 argument: the
      numerator of the distance between [q] and the [n]-th partial sum reduces
      to the integer [a * F_n - b * W_n], with [W_{n+1} = (n+1) * W_n + 1],
      and its trichotomy yields an explicit [eps] and index in each branch.
      Main statements: [eir_e_irrational], [eir_esum_cauchy_modulus].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [Arith.Arith], [ZArith.ZArith], [Setoid], [Lia], [Extraction].
      Requires no other module of this development.

    References.  This development, abl_e_irrational.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_e_irrational.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith ZArith.ZArith Setoid Lia Extraction.

Open Scope Q_scope.

(* ============ §0 rational helpers ============ *)

Definition eir_qz (z : Z) : Q := (z # 1)%Q.

(* reciprocal of an integer; only ever applied to positive integers *)
Definition eir_qinvz (z : Z) : Q :=
  match z with
  | Zpos p => (1 # p)%Q
  | Zneg _ => 0
  | Z0 => 0
  end.

(* the boolean strict comparison face used in delivered statements *)
Definition eir_qltb (x y : Q) : bool :=
  match (Qnum x * Z.pos (Qden y) ?= Qnum y * Z.pos (Qden x))%Z with
  | Lt => true
  | _ => false
  end.

Lemma eir_Zpos_pos : forall p : positive, (0 < Z.pos p)%Z.
Proof. intro p. apply Pos2Z.is_pos. Qed.

Lemma eir_qz_eq : forall x y : Z, (x = y)%Z -> eir_qz x == eir_qz y.
Proof. intros x y H. rewrite H. apply Qeq_refl. Qed.

Lemma eir_qz_mul : forall x y : Z, eir_qz x * eir_qz y == eir_qz (x * y).
Proof.
  intros x y. unfold Qeq, eir_qz. cbn [Qnum Qden Qmult].
  rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma eir_qz_sub : forall x y : Z, eir_qz x - eir_qz y == eir_qz (x - y).
Proof.
  intros x y. unfold Qeq, Qminus, eir_qz. cbn [Qopp Qplus Qnum Qden Qmult].
  rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma eir_qltb_iff : forall x y : Q, eir_qltb x y = true <-> (x < y)%Q.
Proof.
  intros x y. unfold eir_qltb, Qlt. split.
  - intro H. destruct (Qnum x * Z.pos (Qden y) ?= Qnum y * Z.pos (Qden x))%Z eqn:E; try discriminate; try reflexivity.
    apply Z.compare_lt_iff. exact E.
  - intro H. apply Z.compare_lt_iff in H. rewrite H. reflexivity.
Qed.

Lemma eir_qltb_intro : forall x y : Q, (x < y)%Q -> eir_qltb x y = true.
Proof. intros x y H. apply eir_qltb_iff. exact H. Qed.

Lemma eir_qltb_elim : forall x y : Q, eir_qltb x y = true -> (x < y)%Q.
Proof. intros x y H. apply eir_qltb_iff. exact H. Qed.

(* pair literals compare by the integer cross product *)
Lemma eir_qpair_lt : forall (x1 x2 : Z) (d1 d2 : positive),
  (x1 * Z.pos d2 < x2 * Z.pos d1)%Z ->
  eir_qltb ((x1 # d1)%Q) ((x2 # d2)%Q) = true.
Proof.
  intros x1 x2 d1 d2 H. apply eir_qltb_intro. unfold Qlt.
  cbn [Qnum Qden Qcompare]. exact H.
Qed.

Lemma eir_qinvz_posb : forall z : Z, (0 < z)%Z -> eir_qltb 0 (eir_qinvz z) = true.
Proof.
  intros z Hz. apply eir_qltb_intro. unfold Qlt, eir_qinvz.
  destruct z; cbn [eir_qinvz Qnum Qden] in *; lia.
Qed.

Lemma eir_qinvz_lt : forall z1 z2 : Z, (0 < z1)%Z -> (z1 < z2)%Z ->
  eir_qltb (eir_qinvz z2) (eir_qinvz z1) = true.
Proof.
  intros z1 z2 H1 H2. apply eir_qltb_intro. unfold Qlt, eir_qinvz.
  destruct z1; destruct z2; cbn [eir_qinvz Qnum Qden] in *; lia.
Qed.

Lemma eir_qlt_le : forall x y : Q, (x < y)%Q -> (x <= y)%Q.
Proof. intros x y H. apply Qlt_le_weak. exact H. Qed.

(* transport of strict comparison along the rational equality *)
Lemma eir_qlt_transport_r : forall x y e : Q, x == y -> (e < x)%Q -> (e < y)%Q.
Proof.
  intros [xa xb] [ya yb] [en ed] Hxy H.
  unfold Qeq in Hxy. cbn [Qnum Qden] in Hxy.
  unfold Qlt in H |- *. cbn [Qnum Qden] in *.
  assert (H2 : (xa * Z.pos ed * Z.pos yb = ya * Z.pos xb * Z.pos ed)%Z).
  { rewrite <- Hxy. ring. }
  assert (H1 : (en * Z.pos xb * Z.pos yb < ya * Z.pos xb * Z.pos ed)%Z).
  { replace (ya * Z.pos xb * Z.pos ed)%Z with (xa * Z.pos ed * Z.pos yb)%Z
      by (rewrite H2; reflexivity).
    apply Z.mul_lt_mono_pos_r; [lia | exact H]. }
  assert (Hb : (0 < Z.pos xb)%Z) by lia.
  apply Z.compare_lt_iff.
  apply (proj2 (Z.mul_lt_mono_pos_r (Z.pos xb) (en * Z.pos yb) (ya * Z.pos ed) Hb)).
  replace (en * Z.pos yb * Z.pos xb)%Z with (en * Z.pos xb * Z.pos yb)%Z by ring.
  replace (ya * Z.pos ed * Z.pos xb)%Z with (ya * Z.pos xb * Z.pos ed)%Z by ring.
  exact H1.
Qed.

(* transport of strict comparison along the rational equality, left face *)
Lemma eir_qlt_transport_l : forall x y e : Q, x == y -> (x < e)%Q -> (y < e)%Q.
Proof.
  intros [xa xb] [ya yb] [en ed] Hxy H.
  unfold Qeq in Hxy. cbn [Qnum Qden] in Hxy.
  unfold Qlt in H |- *. cbn [Qnum Qden] in *.
  assert (H2 : (xa * Z.pos ed * Z.pos yb = ya * Z.pos xb * Z.pos ed)%Z).
  { rewrite <- Hxy. ring. }
  assert (Hyb : (0 < Z.pos yb)%Z) by lia.
  pose proof (proj1 (Z.mul_lt_mono_pos_r (Z.pos yb) (xa * Z.pos ed)
                       (en * Z.pos xb) Hyb) H) as Hm.
  replace (xa * Z.pos ed * Z.pos yb)%Z with (ya * Z.pos xb * Z.pos ed)%Z in Hm
    by (rewrite H2; reflexivity).
  assert (Hxb : (0 < Z.pos xb)%Z) by lia.
  replace (ya * Z.pos xb * Z.pos ed)%Z with (ya * Z.pos ed * Z.pos xb)%Z in Hm
    by ring.
  replace (en * Z.pos xb * Z.pos yb)%Z with (en * Z.pos yb * Z.pos xb)%Z in Hm
    by ring.
  exact (proj2 (Z.mul_lt_mono_pos_r (Z.pos xb) (ya * Z.pos ed)
                  (en * Z.pos yb) Hxb) Hm).
Qed.

Lemma eir_qle_add_r : forall x t : Q, (0 <= t)%Q -> (x <= x + t)%Q.
Proof.
  intros x t H. apply (Qle_trans x (x + 0) (x + t)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact H].
Qed.

Lemma eir_qle_sub_r : forall x y c : Q, (x <= y)%Q -> (x - c <= y - c)%Q.
Proof.
  intros x y c H. unfold Qminus. apply Qplus_le_compat.
  - exact H.
  - apply Qopp_le_compat. apply Qle_refl.
Qed.

Lemma eir_cancel_r : forall x y c : Q, ~ (c == 0)%Q -> x * c == y * c -> x == y.
Proof.
  intros x y c Hc H.
  remember (/ c)%Q as d eqn:Ed.
  assert (Hci : c * d == 1) by (rewrite Ed; apply Qmult_inv_r; exact Hc).
  apply (Qeq_trans x (c * d * x) y).
  - apply (Qeq_sym (c * d * x) x).
    apply (Qeq_trans (c * d * x) (1 * x) x).
    + apply (Qmult_comp (c * d) 1 Hci x x (Qeq_refl x)).
    + apply Qmult_1_l.
  - apply (Qeq_trans _ ((x * c) * d)).
    + ring.
    + apply (Qeq_trans ((x * c) * d) ((y * c) * d) y).
      * apply (Qmult_comp _ _ H d d (Qeq_refl d)).
      * apply (Qeq_trans _ (c * d * y)).
        -- ring.
        -- apply (Qeq_trans _ (1 * y)).
           ++ apply (Qmult_comp (c * d) 1 Hci y y (Qeq_refl y)).
           ++ apply Qmult_1_l.
Qed.

Lemma eir_qz_neq : forall z : Z, (z <> 0)%Z -> ~ (eir_qz z == 0)%Q.
Proof.
  intros z Hz Hq. unfold Qeq, eir_qz in Hq. cbn [Qnum Qden] in Hq.
  rewrite !Z.mul_1_r in Hq. lia.
Qed.

(* multiplying a rational by its own denominator recovers the numerator *)
Lemma eir_q_mul_denom : forall q : Q, q * eir_qz (Z.pos (Qden q)) == eir_qz (Qnum q).
Proof.
  intros [p q']. unfold Qeq, eir_qz. cbn [Qnum Qden Qmult].
  rewrite !Z.mul_1_r, Pos.mul_1_r. reflexivity.
Qed.

(* strict comparison transported to the absolute value face *)
Lemma eir_abs_gt : forall X eps : Q, (eps < X)%Q -> eir_qltb eps (Qabs X) = true.
Proof. intros X eps H. apply eir_qltb_intro. apply (Qabs_gt eps X H). Qed.


(* ============ §1 factorials, terms, partial sums ============ *)

Fixpoint eir_efac (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S k => Datatypes.S k * eir_efac k
  end.

Lemma eir_efac_ge1 : forall n : nat, (1 <= eir_efac n)%nat.
Proof.
  induction n.
  - cbn [eir_efac]. lia.
  - cbn [eir_efac]. apply Nat.le_trans with (1 * eir_efac n)%nat.
    + lia.
    + apply Nat.mul_le_mono_r. lia.
Qed.

Lemma eir_efac_pos : forall n : nat, (0 < eir_efac n)%nat.
Proof. intro n. pose proof (eir_efac_ge1 n). lia. Qed.

Lemma eir_efac_ge_arg : forall n : nat, (n <= eir_efac n)%nat.
Proof.
  induction n.
  - cbn [eir_efac]. lia.
  - cbn [eir_efac].
    replace (Datatypes.S n) with (Datatypes.S n * 1)%nat at 1 by ring.
    pose proof (eir_efac_ge1 n) as H1.
    apply (Nat.mul_le_mono_l 1 (eir_efac n) (Datatypes.S n) H1).
Qed.

Lemma eir_efac_succ : forall n : nat,
  eir_efac (Datatypes.S n) = (Datatypes.S n * eir_efac n)%nat.
Proof. intro n. reflexivity. Qed.

(* strict factorial growth:  F(M+1+k) > F(M) * 2^(1+k)  for M >= 2 *)
Lemma eir_efac_pow_dom_lt : forall M k : nat, (2 <= M)%nat ->
  (eir_efac M * 2 ^ (Datatypes.S k) < eir_efac (M + Datatypes.S k))%nat.
Proof.
  intros M k HM. induction k.
  - replace (M + 1)%nat with (Datatypes.S M) by lia.
    cbn [eir_efac Nat.pow].
    replace (eir_efac M * (2 * 1))%nat with (2 * eir_efac M)%nat by ring.
    pose proof (eir_efac_ge1 M).
    apply (proj1 (Nat.mul_lt_mono_pos_r (eir_efac M) 2 (Datatypes.S M) ltac:(lia))).
    lia.
  - replace (M + Datatypes.S (Datatypes.S k))%nat with (Datatypes.S (M + Datatypes.S k))%nat by lia.
    rewrite eir_efac_succ.
    apply Nat.lt_le_trans with (2 * eir_efac (M + Datatypes.S k))%nat.
    + replace (2 ^ Datatypes.S (Datatypes.S k))%nat with (2 * 2 ^ Datatypes.S k)%nat by reflexivity.
      replace (eir_efac M * (2 * 2 ^ Datatypes.S k))%nat
        with (2 * (eir_efac M * 2 ^ Datatypes.S k))%nat by ring.
      apply (proj1 (Nat.mul_lt_mono_pos_l 2 (eir_efac M * 2 ^ Datatypes.S k)
                      (eir_efac (M + Datatypes.S k)) ltac:(lia))).
      exact IHk.
    + apply (Nat.mul_le_mono_r 2 (Datatypes.S (M + Datatypes.S k))
               (eir_efac (M + Datatypes.S k)) ltac:(lia)).
Qed.

Definition eir_qfacZ (n : nat) : Z := Z.of_nat (eir_efac n).

Lemma eir_qfacZ_ge1 : forall n : nat, (1 <= eir_qfacZ n)%Z.
Proof.
  induction n.
  - cbn [eir_qfacZ eir_efac]. apply Z.le_refl.
  - unfold eir_qfacZ in *. rewrite eir_efac_succ, Nat2Z.inj_mul.
    apply (Z.mul_le_mono_nonneg 1 (Z.of_nat (Datatypes.S n))
             1 (Z.of_nat (eir_efac n))); lia.
Qed.

Lemma eir_qfacZ_pos : forall n : nat, (0 < eir_qfacZ n)%Z.
Proof. intro n. pose proof (eir_qfacZ_ge1 n). lia. Qed.

Lemma eir_qfacZ_mono : forall n : nat, (eir_qfacZ n <= eir_qfacZ (Datatypes.S n))%Z.
Proof.
  intro n. unfold eir_qfacZ at 1 2. rewrite eir_efac_succ, Nat2Z.inj_mul.
  pose proof (eir_qfacZ_ge1 n) as H1. unfold eir_qfacZ in H1.
  assert (Hm : (1 * Z.of_nat (eir_efac n) <= Z.of_nat (Datatypes.S n) * Z.of_nat (eir_efac n))%Z)
    by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

Lemma eir_qfacZ_ge_mono : forall n m : nat, (n <= m)%nat -> (eir_qfacZ n <= eir_qfacZ m)%Z.
Proof.
  intros n m H. induction m as [|m IH].
  - assert (E : (n = 0)%nat) by lia. subst. lia.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [E|E].
    + subst. lia.
    + assert (Hn : (n <= m)%nat) by lia.
      pose proof (eir_qfacZ_mono m). lia.
Qed.

Definition eir_eterm (k : nat) : Q := eir_qinvz (eir_qfacZ k).

Fixpoint eir_esum (n : nat) : Q :=
  match n with
  | O => 1
  | S k => eir_esum k + eir_eterm (Datatypes.S k)
  end.

Lemma eir_eterm_posb : forall k : nat, eir_qltb 0 (eir_eterm k) = true.
Proof. intro k. apply eir_qinvz_posb. apply eir_qfacZ_pos. Qed.

Lemma eir_eterm_pos : forall k : nat, (0 < eir_eterm k)%Q.
Proof. intro k. apply eir_qltb_elim. apply eir_eterm_posb. Qed.

Lemma eir_eterm_dec : forall k : nat, (1 <= k)%nat ->
  eir_qltb (eir_eterm (Datatypes.S k)) (eir_eterm k) = true.
Proof.
  intros k Hk. apply eir_qinvz_lt.
  - apply eir_qfacZ_pos.
  - unfold eir_qfacZ at 1 2. rewrite eir_efac_succ, Nat2Z.inj_mul.
    pose proof (eir_qfacZ_ge1 k) as H1. unfold eir_qfacZ in H1.
    assert (H2 : (2 * Z.of_nat (eir_efac k) <= Z.of_nat (Datatypes.S k) * Z.of_nat (eir_efac k))%Z)
      by (apply Z.mul_le_mono_nonneg; lia).
    lia.
Qed.

Lemma eir_esum_mono : forall n m : nat, (n <= m)%nat -> (eir_esum n <= eir_esum m)%Q.
Proof.
  intros n m H. induction m as [|m IH].
  - assert (E : (n = 0)%nat) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [E|E].
    + subst. apply Qle_refl.
    + assert (Hn : (n <= m)%nat) by lia.
      apply (Qle_trans _ (eir_esum m)).
      * apply IH. exact Hn.
      * cbn [eir_esum]. apply eir_qle_add_r.
        apply eir_qlt_le. apply eir_qltb_elim. apply eir_eterm_posb.
Qed.

Lemma eir_esum_succ : forall n : nat,
  eir_esum (Datatypes.S n) = eir_esum n + eir_eterm (Datatypes.S n).
Proof. intro n. reflexivity. Qed.

(* ============ §2 geometric sums and the tail machine ============ *)

Fixpoint eir_hpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => q * eir_hpow q k
  end.

Fixpoint eir_g2 (J : nat) : Q :=
  match J with
  | O => 1
  | S k => eir_g2 k + eir_hpow (1 # 2) (Datatypes.S k)
  end.

Lemma eir_geo2 : forall J : nat, eir_g2 J == 2 - eir_hpow (1 # 2) J.
Proof.
  induction J.
  - reflexivity.
  - cbn [eir_g2 eir_hpow]. rewrite IHJ. ring.
Qed.

Lemma eir_qinvz_mul : forall x y : Z, (0 < x)%Z -> (0 < y)%Z ->
  eir_qinvz x * eir_qinvz y == eir_qinvz (x * y).
Proof.
  intros x y Hx Hy.
  destruct x; destruct y; cbn [eir_qinvz] in *; try lia.
  unfold Qeq. cbn [Qnum Qden Qmult]. rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma eir_hpow_half : forall j : nat, eir_hpow (1 # 2) j == eir_qinvz (Z.of_nat (2 ^ j)%nat).
Proof.
  induction j.
  - reflexivity.
  - cbn [eir_hpow]. setoid_rewrite IHj.
    replace (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat by reflexivity.
    rewrite Nat2Z.inj_mul.
    assert (Hp : (0 < Z.of_nat (2 ^ j)%nat)%Z).
    { pose proof (eir_qfacZ_ge1 0) as H0z. cbn [eir_qfacZ eir_efac] in H0z.
      assert (H1 : (1 <= 2 ^ j)%nat).
      { apply Nat.le_trans with (2 ^ 0)%nat. simpl. lia.
        apply Nat.pow_le_mono_r; lia. }
      lia. }
    setoid_rewrite <- (eir_qinvz_mul (Z.of_nat 2) (Z.of_nat (2 ^ j)%nat) ltac:(lia) Hp).
    unfold eir_qinvz at 2. cbn. reflexivity.
Qed.

(* exact closed form for the halved geometric sums, scaled by a term *)
Fixpoint eir_gsum (N J : nat) : Q :=
  match J with
  | O => eir_eterm (Datatypes.S N)
  | S k => eir_gsum N k + eir_eterm (Datatypes.S N) * eir_hpow (1 # 2) (Datatypes.S k)
  end.

Lemma eir_gsum_eq : forall N J : nat,
  eir_gsum N J == eir_eterm (Datatypes.S N) * eir_g2 J.
Proof.
  intros N J. induction J.
  - cbn [eir_gsum eir_g2]. ring.
  - cbn [eir_gsum eir_g2]. setoid_rewrite IHJ. ring.
Qed.

(* partial-sum increments:  esum(N+1+J) - esum(N) = sum_{j<=J} 1/(N+1+j)! *)
Fixpoint eir_etail (N J : nat) : Q :=
  match J with
  | O => eir_eterm (Datatypes.S N)
  | S k => eir_etail N k + eir_eterm (N + 2 + k)
  end.

Lemma eir_etail_eq : forall N J : nat,
  eir_esum (N + Datatypes.S J) - eir_esum N == eir_etail N J.
Proof.
  intros N J. induction J.
  - replace (N + 1)%nat with (Datatypes.S N) by lia.
    cbn [eir_esum eir_etail]. ring.
  - replace (N + Datatypes.S (Datatypes.S J))%nat with (Datatypes.S (N + Datatypes.S J))%nat by lia.
    rewrite eir_esum_succ.
    assert (Hrg : ((eir_esum (N + Datatypes.S J) + eir_eterm (Datatypes.S (N + Datatypes.S J)))
             - eir_esum N)
            == ((eir_esum (N + Datatypes.S J) - eir_esum N)
            + eir_eterm (Datatypes.S (N + Datatypes.S J)))) by ring.
    setoid_rewrite Hrg.
    setoid_rewrite IHJ.
    replace (Datatypes.S (N + Datatypes.S J))%nat with (N + 2 + J)%nat by lia.
    cbn [eir_etail]. ring.
Qed.

(* each tail term is strictly dominated by the geometric term *)
Instance eir_qltb_comp : Proper (Qeq ==> Qeq ==> eq) eir_qltb.
Proof.
  intros x1 x2 Hx12 y1 y2 Hy12.
  destruct (eir_qltb x1 y1) eqn:E1; destruct (eir_qltb x2 y2) eqn:E2; try reflexivity.
  - apply eir_qltb_iff in E1.
    setoid_rewrite Hx12 in E1. setoid_rewrite Hy12 in E1.
    rewrite (proj2 (eir_qltb_iff x2 y2) E1) in E2. discriminate.
  - apply eir_qltb_iff in E2.
    setoid_rewrite <- Hx12 in E2. setoid_rewrite <- Hy12 in E2.
    rewrite (proj2 (eir_qltb_iff x1 y1) E2) in E1. discriminate.
Qed.

Lemma eir_eterm_dom : forall N k : nat, (1 <= N)%nat ->
  eir_qltb (eir_eterm (N + 2 + k))
           (eir_eterm (Datatypes.S N) * eir_hpow (1 # 2) (Datatypes.S k)) = true.
Proof.
  intros N k HN. unfold eir_eterm, eir_qfacZ in *.
  assert (HM : (2 <= Datatypes.S N)%nat) by lia.
  pose proof (eir_efac_pow_dom_lt (Datatypes.S N) k HM) as Hd.
  replace (Datatypes.S N + Datatypes.S k)%nat with (N + 2 + k)%nat in Hd by lia.
  assert (H1 : (0 < eir_qfacZ (Datatypes.S N))%Z) by apply eir_qfacZ_pos.
  assert (H3 : (0 < Z.of_nat (2 ^ Datatypes.S k)%nat)%Z).
  { replace (2 ^ Datatypes.S k)%nat with (2 * 2 ^ k)%nat by reflexivity.
    apply (proj1 (Nat2Z.inj_lt 0 (2 * 2 ^ k)%nat)).
    apply Nat.neq_0_lt_0.
    destruct ((2 ^ k)%nat) as [|kp] eqn:Ek.
    - pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hnz. lia.
    - lia. }
  assert (Hpos : (0 < eir_qfacZ (Datatypes.S N) * Z.of_nat (2 ^ Datatypes.S k)%nat)%Z) by lia.
  apply eir_qltb_intro.
  setoid_rewrite eir_hpow_half.
  unfold eir_eterm.
  setoid_rewrite (eir_qinvz_mul (eir_qfacZ (Datatypes.S N))
                   (Z.of_nat (2 ^ Datatypes.S k)%nat) H1 H3).
  apply eir_qltb_elim. apply eir_qinvz_lt.
  + exact Hpos.
  + unfold eir_qfacZ in *. rewrite eir_efac_succ in *. rewrite !Nat2Z.inj_mul in *.
    replace (Z.of_nat (S N) * Z.of_nat (eir_efac N) * Z.of_nat (2 ^ S k))%Z
      with (Z.of_nat (S N * eir_efac N * 2 ^ S k))%Z
      by (rewrite !Nat2Z.inj_mul; reflexivity).
    apply (proj1 (Nat2Z.inj_lt _ _)). exact Hd.
Qed.

(* the tail is dominated by its geometric majorant *)
Lemma eir_etail_le_gsum : forall N J : nat, (1 <= N)%nat ->
  (eir_etail N J <= eir_gsum N J)%Q.
Proof.
  intros N J HN. induction J as [|J IHJ].
  - cbn [eir_etail eir_gsum]. apply Qle_refl.
  - cbn [eir_etail eir_gsum].
    apply (Qle_trans _ (eir_gsum N J + eir_eterm (N + 2 + J)%nat)).
    + apply Qplus_le_compat; [exact IHJ | apply Qle_refl].
    + apply Qplus_le_compat; [apply Qle_refl | apply eir_qlt_le].
      apply eir_qltb_elim. apply eir_eterm_dom. exact HN.
Qed.

(* the uniform tail bound:  tail_N(J) <= 2/(N+1)! *)
Lemma eir_etail_le : forall N J : nat, (1 <= N)%nat ->
  (eir_etail N J <= 2 * eir_eterm (Datatypes.S N))%Q.
Proof.
  intros N J HN. apply (Qle_trans _ (eir_gsum N J)).
  - apply eir_etail_le_gsum. exact HN.
  - assert (Hs : eir_gsum N J == eir_eterm (Datatypes.S N) * (2 - eir_hpow (1 # 2) J)).
    { apply (Qeq_trans _ (eir_eterm (Datatypes.S N) * eir_g2 J)).
      - apply eir_gsum_eq.
      - setoid_rewrite eir_geo2. apply Qeq_refl. }
    setoid_rewrite Hs.
    assert (Hh : (0 <= eir_hpow (1 # 2) J)%Q).
    { setoid_rewrite eir_hpow_half.
      apply Qlt_le_weak. apply eir_qltb_elim. apply eir_qinvz_posb.
      assert (H2p : (1 <= 2 ^ J)%nat).
      { pose proof (Nat.pow_nonzero 2 J ltac:(lia)) as Hnz. lia. }
      lia. }
    assert (Hhle : ((2 - eir_hpow (1 # 2) J) <= 2)%Q).
    { assert (Hsp : (2 - eir_hpow (1 # 2) J) + eir_hpow (1 # 2) J == 2) by ring.
      apply (Qle_trans _ (2 - eir_hpow (1 # 2) J + eir_hpow (1 # 2) J)).
      - apply eir_qle_add_r. exact Hh.
      - rewrite Hsp. apply Qle_refl. }
    setoid_rewrite (Qmult_comm (eir_eterm (Datatypes.S N)) (2 - eir_hpow (1 # 2) J)).
    apply (Qmult_le_compat_r (2 - eir_hpow (1 # 2) J) 2 (eir_eterm (Datatypes.S N)) Hhle).
    apply Qlt_le_weak. apply eir_qltb_elim. apply eir_eterm_posb.
Qed.
(* ============ §3 Set-level statement faces ============ *)

(* Leibniz equality as a Set: statements built from it are informative
   data, and the boolean comparison faces of §0 lift to it directly. *)
Inductive eir_IdT (A : Set) (x : A) : A -> Set :=
| eir_IdT_refl : eir_IdT A x x.

Lemma eir_IdT_eq : forall (A : Set) (x y : A), eir_IdT A x y -> x = y.
Proof. intros A x y H. destruct H. reflexivity. Qed.

(* strict and non-strict order faces on Q, rooted in the boolean
   comparisons eir_qltb and Qle_bool *)
Definition eir_QltT (x y : Q) : Set := eir_IdT bool (eir_qltb x y) true.
Definition eir_QleT (x y : Q) : Set := eir_IdT bool (Qle_bool x y) true.

Lemma eir_QltT_elim : forall x y : Q, eir_QltT x y -> (x < y)%Q.
Proof.
  intros x y H. apply eir_qltb_elim.
  unfold eir_QltT in H. exact (eir_IdT_eq bool _ true H).
Qed.

Lemma eir_QltT_intro : forall x y : Q, (x < y)%Q -> eir_QltT x y.
Proof.
  intros x y H. unfold eir_QltT. rewrite (eir_qltb_intro _ _ H).
  apply eir_IdT_refl.
Qed.

Lemma eir_QleT_elim : forall x y : Q, eir_QleT x y -> (x <= y)%Q.
Proof.
  intros x y H. unfold eir_QleT in H. pose proof (eir_IdT_eq bool _ true H) as E.
  unfold Qle. apply Z.leb_le. exact E.
Qed.

Lemma eir_QleT_intro : forall x y : Q, (x <= y)%Q -> eir_QleT x y.
Proof.
  intros x y H. unfold eir_QleT.
  assert (Hb : Qle_bool x y = true) by (unfold Qle in H; apply Z.leb_le; exact H).
  rewrite Hb. apply eir_IdT_refl.
Qed.

(* equality of rationals refines to their non-strict order *)
Lemma eir_qeq_le : forall x y : Q, x == y -> (x <= y)%Q.
Proof.
  intros x y H. unfold Qle, Qeq in *. rewrite <- H. apply Z.le_refl.
Qed.

Lemma eir_Qabs_eq_le : forall x : Q, (0 <= x)%Q -> Qabs x == x.
Proof.
  intros [xn xd] H. cbn [Qabs].
  destruct xn as [|p|p].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qle in H. cbn [Qnum Qden] in H. lia.
Qed.

Lemma eir_Qabs_eq_ge : forall x : Q, (x <= 0)%Q -> Qabs x == - x.
Proof.
  intros x H. rewrite <- (Qabs_opp x). apply eir_Qabs_eq_le.
  pose proof (Qopp_le_compat x 0 H) as H2.
  replace (- 0)%Q with 0 in H2 by reflexivity. exact H2.
Qed.

(* the absolute value of a difference whose first summand is smaller
   is the flipped difference *)
Lemma eir_abs_opp_diff : forall x y : Q, (x <= y)%Q -> Qabs (x - y) == y - x.
Proof.
  intros x y H.
  assert (Hle0 : (x - y <= 0)%Q).
  { apply (Qle_trans _ (y - y)).
    - apply Qplus_le_compat; [exact H | apply Qle_refl].
    - apply eir_qeq_le. ring. }
  apply (Qeq_trans (Qabs (x - y)) (- (x - y)) (y - x)).
  - apply eir_Qabs_eq_ge. exact Hle0.
  - ring.
Qed.

(* small order lemmas used by the separation argument *)
Lemma eir_qz_mono : forall x y : Z, (x <= y)%Z -> (eir_qz x <= eir_qz y)%Q.
Proof. intros x y H. unfold Qle, eir_qz. cbn [Qnum Qden]. lia. Qed.

Lemma eir_qz_pos : forall z : Z, (0 < z)%Z -> (0 < eir_qz z)%Q.
Proof.
  intros z Hz. unfold Qlt, eir_qz. destruct z as [|p|p];
    cbn [Qnum Qden]; lia.
Qed.

Lemma eir_qz_ge1 : forall z : Z, (0 < eir_qz z)%Q -> (1 <= z)%Z.
Proof.
  intros z H. unfold Qlt, eir_qz in H. destruct z as [|p|p];
    cbn [Qnum Qden] in H; lia.
Qed.

Lemma eir_qinvz_nonneg : forall z : Z, (0 < z)%Z -> (0 <= eir_qinvz z)%Q.
Proof.
  intros z Hz. apply Qlt_le_weak. apply eir_qltb_elim.
  apply eir_qinvz_posb. exact Hz.
Qed.

Lemma eir_qlt_mul_pos : forall x y : Q, (0 < x)%Q -> (0 < y)%Q -> (0 < x * y)%Q.
Proof.
  intros x y Hx Hy.
  apply (eir_qlt_transport_l (0 * y) 0 (x * y)).
  - ring.
  - apply Qmult_lt_compat_r; assumption.
Qed.

Lemma eir_qlt_double : forall x : Q, (0 < x)%Q -> (x < x + x)%Q.
Proof.
  intros x H. pose proof (proj2 (Qplus_lt_r 0 x x) H) as H1.
  apply (eir_qlt_transport_l (x + 0) x (x + x)).
  - ring.
  - exact H1.
Qed.

Lemma eir_qsub_pos : forall x y : Q, (y < x)%Q -> (0 < x - y)%Q.
Proof.
  intros x y H.
  assert (Hs : (- y + x == x - y)%Q) by ring.
  apply (eir_qlt_transport_r _ _ _ Hs).
  apply (eir_qlt_transport_l (- y + y) 0 (- y + x)).
  - ring.
  - apply (proj2 (Qplus_lt_r y x (- y)) H).
Qed.

Lemma eir_qle_sub_r0 : forall x c : Q, (0 <= c)%Q -> (x - c <= x)%Q.
Proof.
  intros x c H.
  assert (Hc0 : (- c <= 0)%Q).
  { pose proof (Qopp_le_compat 0 c H) as H2.
    replace (- 0)%Q with 0 in H2 by reflexivity. exact H2. }
  apply (Qle_trans _ (x + 0)).
  - apply Qplus_le_compat; [apply Qle_refl | exact Hc0].
  - apply eir_qeq_le. ring.
Qed.

Lemma eir_qle_sub_l : forall x c d : Q, (d <= c)%Q -> (x - c <= x - d)%Q.
Proof.
  intros x c d H.
  assert (Hs : x - c == (x - d) + (d - c)) by ring.
  assert (Hle0 : (d - c <= 0)%Q).
  { apply (Qle_trans _ (c + - c)).
    - apply Qplus_le_compat; [exact H | apply Qle_refl].
    - apply eir_qeq_le. ring. }
  apply (Qle_trans _ ((x - d) + (d - c))).
  - apply eir_qeq_le. exact Hs.
  - apply (Qle_trans _ ((x - d) + 0)).
    + apply Qplus_le_compat; [apply Qle_refl | exact Hle0].
    + apply eir_qeq_le. ring.
Qed.

Lemma eir_qlt_neq0 : forall c : Q, (0 < c)%Q -> ~ (c == 0)%Q.
Proof.
  intros c Hc Heq.
  pose proof (eir_qlt_transport_r c 0 0 Heq Hc) as H0.
  unfold Qlt in H0. cbn [Qnum Qden] in H0. lia.
Qed.

Lemma eir_two_qinvz : 2 * eir_qinvz 2 == 1.
Proof. unfold Qeq, eir_qinvz. reflexivity. Qed.

(* ============ §4 the integer numerator of the distance ============ *)

(* W_n = sum_{k<=n} n!/k!, the numerator of n! * s_n, given by the
   recurrence W_0 = 1, W_{n+1} = (n+1) W_n + 1 (Fourier 1815). *)
Fixpoint eir_Wnum (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S k => (Z.of_nat (Datatypes.S k) * eir_Wnum k + 1)%Z
  end.

Lemma eir_qfacZ_succ : forall n : nat,
  eir_qfacZ (Datatypes.S n) = (Z.of_nat (Datatypes.S n) * eir_qfacZ n)%Z.
Proof.
  intro n. unfold eir_qfacZ. rewrite eir_efac_succ. apply Nat2Z.inj_mul.
Qed.

Lemma eir_qz_plus : forall x y : Z, eir_qz x + eir_qz y == eir_qz (x + y).
Proof.
  intros x y. unfold Qeq, eir_qz. cbn. ring.
Qed.

Lemma eir_qz_qinvz_mul_one : forall p : positive,
  eir_qz (Zpos p) * eir_qinvz (Zpos p) == 1.
Proof.
  intro p. unfold Qeq, eir_qz, eir_qinvz. cbn [Qnum Qden Qmult].
  rewrite !Z.mul_1_r, !Z.mul_1_l. reflexivity.
Qed.

Lemma eir_qz_qinvz_mul_one_gen : forall z : Z, (0 < z)%Z ->
  eir_qz z * eir_qinvz z == 1.
Proof.
  intros z Hz. destruct z as [|p|p]; try lia.
  apply eir_qz_qinvz_mul_one.
Qed.

(* 1/M = c * (1/(c*M)) for positive integers c, M *)
Lemma eir_qinvz_scale : forall c M : Z, (0 < c)%Z -> (0 < M)%Z ->
  eir_qinvz M == eir_qz c * eir_qinvz (c * M).
Proof.
  intros c M Hc HM.
  setoid_rewrite <- (eir_qinvz_mul c M Hc HM).
  assert (Hci : eir_qz c * eir_qinvz c == 1)
    by (apply eir_qz_qinvz_mul_one_gen; exact Hc).
  setoid_rewrite Qmult_assoc.
  setoid_rewrite Hci.
  ring.
Qed.

(* (1/u) * (u*v) = v as rationals carried by integer witnesses *)
Lemma eir_qinvz_mul_qz : forall u v : Z, (0 < u)%Z -> (0 < v)%Z ->
  eir_qinvz u * eir_qz (u * v) == eir_qz v.
Proof.
  intros u v Hu Hv.
  setoid_rewrite <- (eir_qz_mul u v).
  setoid_rewrite Qmult_assoc.
  setoid_rewrite (Qmult_comm (eir_qinvz u) (eir_qz u)).
  setoid_rewrite (eir_qz_qinvz_mul_one_gen u Hu).
  ring.
Qed.

Lemma eir_qpair_mul_den : forall (x : Z) (d : positive),
  (x # d)%Q * eir_qz (Z.pos d) == eir_qz x.
Proof.
  intros x d. unfold Qeq, eir_qz. cbn [Qnum Qden Qmult].
  rewrite !Z.mul_1_r, Pos.mul_1_r. reflexivity.
Qed.

(* scaling a fraction by its own denominator times any integer *)
Lemma eir_qz_scale_den : forall (x : Z) (d : positive) (M : Z),
  eir_qz (Z.pos d * M) * (x # d)%Q == eir_qz (x * M).
Proof.
  intros x d M.
  setoid_rewrite <- (eir_qz_mul (Z.pos d) M).
  setoid_rewrite <- Qmult_assoc.
  setoid_rewrite <- (eir_qz_mul x M).
  setoid_rewrite <- (eir_qpair_mul_den x d).
  ring.
Qed.

(* factorial times one term is 1 *)
Lemma eir_qfac_mul_inv : forall n : nat,
  eir_qz (eir_qfacZ n) * eir_eterm n == 1.
Proof.
  intro n. unfold eir_eterm. pose proof (eir_qfacZ_pos n) as Hp.
  destruct (eir_qfacZ n) as [|p|p] eqn:Ef; try lia.
  apply eir_qz_qinvz_mul_one.
Qed.

(* the scaled partial sum:  (m!) * s_m is the integer W_m over 1 *)
Lemma eir_esum_scaled : forall n : nat,
  eir_qz (eir_qfacZ n) * eir_esum n == eir_qz (eir_Wnum n).
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - cbn [eir_Wnum]. rewrite eir_esum_succ. rewrite eir_qfacZ_succ.
    setoid_rewrite Qmult_plus_distr_r.
    assert (H1 : eir_qz (Z.of_nat (Datatypes.S n) * eir_qfacZ n) * eir_esum n
                 == eir_qz (Z.of_nat (Datatypes.S n) * eir_Wnum n)).
    { setoid_rewrite <- (eir_qz_mul (Z.of_nat (Datatypes.S n)) (eir_qfacZ n)).
      setoid_rewrite <- Qmult_assoc.
      setoid_rewrite IHn.
      setoid_rewrite (eir_qz_mul (Z.of_nat (Datatypes.S n)) (eir_Wnum n)).
      apply Qeq_refl. }
    pose proof (eir_qfac_mul_inv (Datatypes.S n)) as H2raw.
    rewrite eir_qfacZ_succ in H2raw.
    setoid_rewrite H1. setoid_rewrite H2raw.
    assert (Hqp : eir_qz 1 == 1) by reflexivity.
    setoid_rewrite <- Hqp.
    setoid_rewrite eir_qz_plus.
    apply Qeq_refl.
Qed.

(* the scaled distance identity: for q = a/b and every m,
   b * m! * (q - s_m) is exactly the integer a * m! - b * W_m *)
Lemma eir_dist_scaled : forall (a : Z) (b : positive) (m : nat),
  eir_qz (Z.pos b * eir_qfacZ m) * ((a # b)%Q - eir_esum m)
  == eir_qz (a * eir_qfacZ m - Z.pos b * eir_Wnum m).
Proof.
  intros a b m.
  assert (Hsub : ((a # b)%Q - eir_esum m
                  == (a # b)%Q + (- 1) * eir_esum m)%Q) by ring.
  assert (H1 : eir_qz (Z.pos b * eir_qfacZ m) * (a # b)%Q == eir_qz (a * eir_qfacZ m))
    by (apply eir_qz_scale_den).
  assert (H2 : eir_qz (Z.pos b * eir_qfacZ m) * eir_esum m
               == eir_qz (Z.pos b * eir_Wnum m)).
  { assert (Hsplit : eir_qz (Z.pos b * eir_qfacZ m)
                     == eir_qz (Z.pos b) * eir_qz (eir_qfacZ m)).
    { exact (Qeq_sym _ _ (eir_qz_mul (Z.pos b) (eir_qfacZ m))). }
    apply (Qeq_trans (eir_qz (Z.pos b * eir_qfacZ m) * eir_esum m)
                     ((eir_qz (Z.pos b) * eir_qz (eir_qfacZ m)) * eir_esum m)
                     (eir_qz (Z.pos b * eir_Wnum m))).
    - apply (Qmult_comp (eir_qz (Z.pos b * eir_qfacZ m))
               (eir_qz (Z.pos b) * eir_qz (eir_qfacZ m)) Hsplit
               (eir_esum m) (eir_esum m) (Qeq_refl (eir_esum m))).
    - apply (Qeq_trans ((eir_qz (Z.pos b) * eir_qz (eir_qfacZ m)) * eir_esum m)
                       (eir_qz (Z.pos b) * (eir_qz (eir_qfacZ m) * eir_esum m))
                       (eir_qz (Z.pos b * eir_Wnum m))).
      + apply (Qeq_sym _ _ (Qmult_assoc (eir_qz (Z.pos b))
                              (eir_qz (eir_qfacZ m)) (eir_esum m))).
      + apply (Qeq_trans (eir_qz (Z.pos b) * (eir_qz (eir_qfacZ m) * eir_esum m))
                         (eir_qz (Z.pos b) * eir_qz (eir_Wnum m))
                         (eir_qz (Z.pos b * eir_Wnum m))).
        * apply (Qmult_comp (eir_qz (Z.pos b)) (eir_qz (Z.pos b))
                   (Qeq_refl (eir_qz (Z.pos b)))
                   (eir_qz (eir_qfacZ m) * eir_esum m) (eir_qz (eir_Wnum m))
                   (eir_esum_scaled m)).
        * apply eir_qz_mul. }
  assert (Hneg : eir_qz (Z.pos b * eir_qfacZ m) * ((- 1) * eir_esum m)
                 == - (eir_qz (Z.pos b * eir_qfacZ m) * eir_esum m)) by ring.
  apply (Qeq_trans (eir_qz (Z.pos b * eir_qfacZ m) * ((a # b)%Q - eir_esum m))
                   (eir_qz (Z.pos b * eir_qfacZ m)
                    * ((a # b)%Q + (- 1) * eir_esum m))
                   (eir_qz (a * eir_qfacZ m - Z.pos b * eir_Wnum m))).
  - apply (Qmult_comp (eir_qz (Z.pos b * eir_qfacZ m))
             (eir_qz (Z.pos b * eir_qfacZ m))
             (Qeq_refl (eir_qz (Z.pos b * eir_qfacZ m)))
             ((a # b)%Q - eir_esum m) ((a # b)%Q + (- 1) * eir_esum m) Hsub).
  - apply (Qeq_trans (eir_qz (Z.pos b * eir_qfacZ m)
                      * ((a # b)%Q + (- 1) * eir_esum m))
                     (eir_qz (Z.pos b * eir_qfacZ m) * (a # b)%Q
                      + eir_qz (Z.pos b * eir_qfacZ m) * ((- 1) * eir_esum m))
                     (eir_qz (a * eir_qfacZ m - Z.pos b * eir_Wnum m))).
    + exact (Qmult_plus_distr_r (eir_qz (Z.pos b * eir_qfacZ m))
               (a # b)%Q ((- 1) * eir_esum m)).
    + apply (Qeq_trans (eir_qz (Z.pos b * eir_qfacZ m) * (a # b)%Q
                        + eir_qz (Z.pos b * eir_qfacZ m) * ((- 1) * eir_esum m))
                       (eir_qz (a * eir_qfacZ m) + - eir_qz (Z.pos b * eir_Wnum m))
                       (eir_qz (a * eir_qfacZ m - Z.pos b * eir_Wnum m))).
      * apply (Qplus_comp (eir_qz (Z.pos b * eir_qfacZ m) * (a # b)%Q)
                 (eir_qz (a * eir_qfacZ m)) H1
                 (eir_qz (Z.pos b * eir_qfacZ m) * ((- 1) * eir_esum m))
                 (- eir_qz (Z.pos b * eir_Wnum m))
                 (Qeq_trans (eir_qz (Z.pos b * eir_qfacZ m) * ((- 1) * eir_esum m))
                    (- (eir_qz (Z.pos b * eir_qfacZ m) * eir_esum m))
                    (- eir_qz (Z.pos b * eir_Wnum m))
                    Hneg
                    (Qopp_comp (eir_qz (Z.pos b * eir_qfacZ m) * eir_esum m)
                       (eir_qz (Z.pos b * eir_Wnum m)) H2))).
      * apply eir_qz_sub.
Qed.

(* a nonzero scaled distance dominates the unit fraction:
   if M times x is a positive integer d >= 1 and M > 0, then x >= 1/M *)
Lemma eir_scaled_lower : forall (M d : Z) (x : Q), (0 < M)%Z -> (1 <= d)%Z ->
  eir_qz M * x == eir_qz d -> (eir_qinvz M <= x)%Q.
Proof.
  intros M d x HM Hd Heq.
  assert (Hcomm : x * eir_qz M == eir_qz M * x) by ring.
  assert (HKM : eir_qinvz M * eir_qz M == 1).
  { apply (Qeq_trans (eir_qinvz M * eir_qz M) (eir_qz M * eir_qinvz M) 1).
    - apply Qmult_comm.
    - apply eir_qz_qinvz_mul_one_gen. exact HM. }
  assert (Hx : x == eir_qz d * eir_qinvz M).
  { apply (eir_cancel_r _ _ (eir_qz M)); [apply eir_qz_neq; lia |].
    apply (Qeq_trans (x * eir_qz M) (eir_qz d)
                     ((eir_qz d * eir_qinvz M) * eir_qz M)).
    - apply (Qeq_trans (x * eir_qz M) (eir_qz M * x) (eir_qz d)).
      + exact Hcomm.
      + exact Heq.
    - apply (Qeq_trans (eir_qz d) (eir_qz d * (eir_qinvz M * eir_qz M))
                       ((eir_qz d * eir_qinvz M) * eir_qz M)).
      + apply (Qeq_sym _ _ (Qeq_trans (eir_qz d * (eir_qinvz M * eir_qz M))
                              (eir_qz d * 1) (eir_qz d)
                              (Qmult_comp (eir_qz d) (eir_qz d)
                                 (Qeq_refl (eir_qz d))
                                 (eir_qinvz M * eir_qz M) 1 HKM)
                              (Qmult_1_r (eir_qz d)))).
      + ring. }
  apply (Qle_trans (eir_qinvz M) (eir_qz 1 * eir_qinvz M) x).
  - apply eir_qeq_le.
    assert (Hz1 : eir_qz 1 == 1) by reflexivity.
    apply (Qeq_sym _ _ (Qeq_trans (eir_qz 1 * eir_qinvz M)
                       (1 * eir_qinvz M) (eir_qinvz M)
             (Qmult_comp (eir_qz 1) 1 Hz1 (eir_qinvz M) (eir_qinvz M)
                (Qeq_refl (eir_qinvz M)))
             (Qmult_1_l (eir_qinvz M)))).
  - apply (Qle_trans (eir_qz 1 * eir_qinvz M) (eir_qz d * eir_qinvz M) x).
    + apply Qmult_le_compat_r; [apply eir_qz_mono; lia | apply eir_qinvz_nonneg; lia].
    + apply eir_qeq_le. apply (Qeq_sym _ _ Hx).
Qed.

(* strict doubling: x < 2 * x for positive x *)
Lemma eir_qlt_twice : forall x : Q, (0 < x)%Q -> (x < 2 * x)%Q.
Proof.
  intros x Hx.
  assert (Hr : x + x == 2 * x) by ring.
  apply (eir_qlt_transport_r (x + x) (2 * x) x Hr).
  apply eir_qlt_double. exact Hx.
Qed.

(* ============ §5 the irrationality of e as an apartness modulus ============ *)

(* decidable comparison of a rational against a partial sum *)
Lemma eir_Qcompare_lt : forall x y : Q, Qcompare x y = Lt -> (x < y)%Q.
Proof. intros x y H. unfold Qlt, Qcompare in *. exact H. Qed.

Lemma eir_Qcompare_eq : forall x y : Q, Qcompare x y = Eq -> x == y.
Proof.
  intros x y H. unfold Qcompare in H. apply Z.compare_eq_iff in H.
  unfold Qeq. cbn [Qnum Qden]. lia.
Qed.

Lemma eir_Qcompare_gt : forall x y : Q, Qcompare x y = Gt -> (y < x)%Q.
Proof.
  intros x y H. unfold Qcompare in H. apply Z.compare_gt_iff in H.
  unfold Qlt. exact H.
Qed.

(* Main theorem.  For every rational q = a/b the partial sums of the
   exponential series are eventually, uniformly and computably apart
   from q: the delivered index n and margin eps are explicit rational
   data, and every partial sum from index n on stays at distance > eps
   from q.  Since the partial sums converge (Cauchy with the explicit
   modulus below), no rational number can be their limit: e is not a
   quotient of integers.  This is Fourier's 1815 argument rendered as
   a computable witness: the scaled distance b * m! * (q - s_m) is the
   integer a * m! - b * W_m, which cannot both stay positive and tend
   to 0 faster than 1/(b * m!). *)
Theorem eir_e_irrational :
  forall (a : Z) (b : positive),
    sigT (fun n : nat => sigT (fun eps : Q =>
      ((eir_QltT 0 eps) *
       (forall j : nat, eir_QltT eps (Qabs ((a # b)%Q - eir_esum (n + j)%nat))))%type)).
Proof.
  intros a b.
  pose (n0 := (2 * Z.to_nat (Z.pos b))%nat).
  pose proof (eir_qfacZ_pos n0) as HpF.
  assert (HpB : (0 < Z.pos b)%Z) by (apply Pos2Z.is_pos).
  assert (HbFpos : (0 < Z.pos b * eir_qfacZ n0)%Z)
    by (apply Z.mul_pos_pos; assumption).
  destruct (Qle_bool ((a # b)%Q) (eir_esum n0)) eqn:Hqb.
  destruct (Qeq_dec ((a # b)%Q) (eir_esum n0)) as [Heq | Hne].
  - (* q equals s_n0: the next partial sum already carries a gap *)
    exists (Datatypes.S n0). exists (eir_qinvz 2 * eir_eterm (Datatypes.S n0)).
    split.
    + apply eir_QltT_intro. apply eir_qlt_mul_pos.
      * apply eir_qltb_elim. apply eir_qinvz_posb. lia.
      * apply eir_eterm_pos.
    + intros j.
      assert (Hmono : (eir_esum (Datatypes.S n0)
                       <= eir_esum (Datatypes.S n0 + j)%nat)%Q)
        by (apply eir_esum_mono; lia).
      assert (Hseq : eir_esum (Datatypes.S n0)
                     == (a # b)%Q + eir_eterm (Datatypes.S n0)).
      { rewrite eir_esum_succ.
        apply (Qplus_comp (eir_esum n0) (a # b)%Q
                 (Qeq_sym _ _ Heq)
                 (eir_eterm (Datatypes.S n0)) (eir_eterm (Datatypes.S n0))
                 (Qeq_refl (eir_eterm (Datatypes.S n0)))). }
      assert (Hr : eir_esum (Datatypes.S n0) - (a # b)%Q
                   == eir_eterm (Datatypes.S n0)).
      { apply (Qeq_trans (eir_esum (Datatypes.S n0) - (a # b)%Q)
                         ((a # b)%Q + eir_eterm (Datatypes.S n0) - (a # b)%Q)
                         (eir_eterm (Datatypes.S n0))).
        - apply (Qplus_comp (eir_esum (Datatypes.S n0))
                   ((a # b)%Q + eir_eterm (Datatypes.S n0)) Hseq
                   (- (a # b)%Q) (- (a # b)%Q) (Qeq_refl (- (a # b)%Q))).
        - ring. }
      assert (Hge : (eir_eterm (Datatypes.S n0)
                     <= eir_esum (Datatypes.S n0 + j)%nat - (a # b)%Q)%Q).
      { apply (Qle_trans _ (eir_esum (Datatypes.S n0) - (a # b)%Q)).
        - apply eir_qeq_le. apply (Qeq_sym _ _ Hr).
        - apply eir_qle_sub_r. exact Hmono. }
      assert (H2e : (2 * (eir_qinvz 2 * eir_eterm (Datatypes.S n0))
                     == eir_eterm (Datatypes.S n0))%Q).
      { apply (Qeq_trans (2 * (eir_qinvz 2 * eir_eterm (Datatypes.S n0)))
                         ((2 * eir_qinvz 2) * eir_eterm (Datatypes.S n0))
                         (eir_eterm (Datatypes.S n0))).
        - ring.
        - apply (Qeq_trans ((2 * eir_qinvz 2) * eir_eterm (Datatypes.S n0))
                           (1 * eir_eterm (Datatypes.S n0))
                           (eir_eterm (Datatypes.S n0))).
          + apply (Qmult_comp (2 * eir_qinvz 2) 1 eir_two_qinvz
                     (eir_eterm (Datatypes.S n0)) (eir_eterm (Datatypes.S n0))
                     (Qeq_refl (eir_eterm (Datatypes.S n0)))).
          + apply Qmult_1_l. }
      assert (Hmain : (eir_qinvz 2 * eir_eterm (Datatypes.S n0)
                       < eir_esum (Datatypes.S n0 + j)%nat - (a # b)%Q)%Q).
      { apply (Qlt_le_trans _ (eir_eterm (Datatypes.S n0))).
        - apply (eir_qlt_transport_r _ _ _ H2e).
          + apply eir_qlt_twice. apply eir_qlt_mul_pos.
            * apply eir_qltb_elim. apply eir_qinvz_posb. lia.
            * apply eir_eterm_pos.
        - exact Hge. }
      assert (Habseq : Qabs ((a # b)%Q - eir_esum (Datatypes.S n0 + j)%nat)
                       == eir_esum (Datatypes.S n0 + j)%nat - (a # b)%Q).
      { apply eir_abs_opp_diff.
        apply (Qle_trans _ ((a # b)%Q + eir_eterm (Datatypes.S n0))).
        - apply (Qle_trans _ ((a # b)%Q + 0)).
          + apply eir_qeq_le. apply (Qeq_sym _ _ (Qplus_0_r (a # b)%Q)).
          + apply Qlt_le_weak.
            apply (proj2 (Qplus_lt_r 0 (eir_eterm (Datatypes.S n0)) (a # b)%Q)).
            apply eir_eterm_pos.
        - apply (Qle_trans _ (eir_esum (Datatypes.S n0))).
          + apply eir_qeq_le. apply (Qeq_sym _ _ Hseq).
          + apply eir_esum_mono. lia. }
      apply eir_QltT_intro.
      apply (eir_qlt_transport_r _ _ _ (Qeq_sym _ _ Habseq) Hmain).
  - (* q lies below s_n0: the margin is half the current gap *)
    assert (Hlt : ((a # b)%Q < eir_esum n0)%Q).
    { apply Qle_bool_iff in Hqb.
      destruct (Qle_lt_or_eq _ _ Hqb) as [Hlt1 | Heq1];
        [exact Hlt1 | exfalso; apply Hne; exact Heq1]. }
    exists n0. exists (eir_qinvz 2 * (eir_esum n0 - (a # b)%Q)).
    split.
    + apply eir_QltT_intro. apply eir_qlt_mul_pos.
      * apply eir_qltb_elim. apply eir_qinvz_posb. lia.
      * apply eir_qsub_pos. exact Hlt.
    + intros j.
      assert (Hmono : (eir_esum n0 <= eir_esum (n0 + j)%nat)%Q)
        by (apply eir_esum_mono; lia).
      assert (Hge : (eir_esum n0 - (a # b)%Q
                     <= eir_esum (n0 + j)%nat - (a # b)%Q)%Q)
        by (apply eir_qle_sub_r; exact Hmono).
      assert (H0e : (0 < eir_qinvz 2 * (eir_esum n0 - (a # b)%Q))%Q)
        by (apply eir_qlt_mul_pos;
            [apply eir_qltb_elim; apply eir_qinvz_posb; lia
            | apply eir_qsub_pos; exact Hlt]).
      assert (H2e : (2 * (eir_qinvz 2 * (eir_esum n0 - (a # b)%Q))
                     == eir_esum n0 - (a # b)%Q)%Q).
      { apply (Qeq_trans (2 * (eir_qinvz 2 * (eir_esum n0 - (a # b)%Q)))
                         ((2 * eir_qinvz 2) * (eir_esum n0 - (a # b)%Q))
                         (eir_esum n0 - (a # b)%Q)).
        - ring.
        - apply (Qeq_trans ((2 * eir_qinvz 2) * (eir_esum n0 - (a # b)%Q))
                           (1 * (eir_esum n0 - (a # b)%Q))
                           (eir_esum n0 - (a # b)%Q)).
          + apply (Qmult_comp (2 * eir_qinvz 2) 1 eir_two_qinvz
                     (eir_esum n0 - (a # b)%Q) (eir_esum n0 - (a # b)%Q)
                     (Qeq_refl (eir_esum n0 - (a # b)%Q))).
          + apply Qmult_1_l. }
      assert (Hmain : (eir_qinvz 2 * (eir_esum n0 - (a # b)%Q)
                       < eir_esum (n0 + j)%nat - (a # b)%Q)%Q).
      { apply (Qlt_le_trans _ (2 * (eir_qinvz 2 * (eir_esum n0 - (a # b)%Q)))).
        - apply eir_qlt_twice. exact H0e.
        - apply (Qle_trans _ (eir_esum n0 - (a # b)%Q)).
          + apply eir_qeq_le. exact H2e.
          + exact Hge. }
      assert (Habseq : Qabs ((a # b)%Q - eir_esum (n0 + j)%nat)
                       == eir_esum (n0 + j)%nat - (a # b)%Q).
      { apply eir_abs_opp_diff.
        apply (Qle_trans _ (eir_esum n0)).
        - apply Qlt_le_weak. exact Hlt.
        - apply eir_esum_mono. lia. }
      apply eir_QltT_intro.
      apply (eir_qlt_transport_r _ _ _ (Qeq_sym _ _ Habseq) Hmain).
  - (* q lies above s_n0: the scaled integer argument applies *)
    assert (Hnle : ~ ((a # b)%Q <= eir_esum n0)%Q).
    { intros Hle. apply Qle_bool_iff in Hle. rewrite Hqb in Hle. discriminate. }
    assert (Hs0q : (eir_esum n0 < (a # b)%Q)%Q)
      by (apply Qnot_le_lt; exact Hnle).
    assert (Hn1 : Z.of_nat (Datatypes.S n0) = (2 * Z.pos b + 1)%Z).
    { replace (Datatypes.S n0) with (n0 + 1)%nat by (unfold n0; lia).
      rewrite Nat2Z.inj_add. unfold n0. rewrite Nat2Z.inj_mul.
      assert (HBZ : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b)
        by (apply Z2Nat.id; lia).
      rewrite HBZ. reflexivity. }
    assert (Hn1pos : (0 < Z.of_nat (Datatypes.S n0))%Z) by lia.
    assert (HposNF : (0 < Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)%Z)
      by (apply Z.mul_pos_pos; assumption).
    assert (HposK : (0 < 2 * (Z.of_nat (Datatypes.S n0)
                                * (Z.pos b * eir_qfacZ n0)))%Z).
    { assert (HposP : (0 < Z.of_nat (Datatypes.S n0) * (Z.pos b * eir_qfacZ n0))%Z)
        by (apply Z.mul_pos_pos; assumption).
      lia. }
    assert (Hdist : eir_qz (Z.pos b * eir_qfacZ n0) * ((a # b)%Q - eir_esum n0)
                    == eir_qz (a * eir_qfacZ n0 - Z.pos b * eir_Wnum n0))
      by (apply eir_dist_scaled).
    assert (Hlower : (eir_qinvz (Z.pos b * eir_qfacZ n0)
                      <= (a # b)%Q - eir_esum n0)%Q).
    { apply (eir_scaled_lower (Z.pos b * eir_qfacZ n0)
               (a * eir_qfacZ n0 - Z.pos b * eir_Wnum n0)
               ((a # b)%Q - eir_esum n0)); [exact HbFpos | | exact Hdist].
      apply eir_qz_ge1.
      assert (HposM : (0 < eir_qz (Z.pos b * eir_qfacZ n0))%Q)
        by (apply eir_qz_pos; exact HbFpos).
      apply (eir_qlt_transport_r _ _ _ Hdist).
      apply eir_qlt_mul_pos.
      - exact HposM.
      - apply eir_qsub_pos. exact Hs0q. }
    exists n0.
    exists (eir_qinvz (2 * (Z.of_nat (Datatypes.S n0) * (Z.pos b * eir_qfacZ n0)))).
    split.
    + apply eir_QltT_intro. apply eir_qltb_elim. apply eir_qinvz_posb.
      exact HposK.
    + assert (Hmargin : (eir_qinvz (Z.pos b * eir_qfacZ n0)
                          - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                          == 2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                * (Z.pos b * eir_qfacZ n0))))%Q).
      { assert (Hz2 : eir_qz 2 == 2) by reflexivity.
        assert (Hz1 : eir_qz 1 == 1) by reflexivity.
        assert (HK2 : eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                        * (Z.pos b * eir_qfacZ n0)))
                      * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                        * (Z.pos b * eir_qfacZ n0))) == 1).
        { apply (Qeq_trans (eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                           * (Z.pos b * eir_qfacZ n0)))
                            * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                 * (Z.pos b * eir_qfacZ n0))))
                           (eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                 * (Z.pos b * eir_qfacZ n0)))
                            * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                  * (Z.pos b * eir_qfacZ n0))))
                           1).
          - ring.
          - apply (eir_qz_qinvz_mul_one_gen _ HposK). }
        assert (HA : eir_qinvz (Z.pos b * eir_qfacZ n0)
                     * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                        * (Z.pos b * eir_qfacZ n0)))
                     == eir_qz (2 * Z.of_nat (Datatypes.S n0))).
        { assert (HKK : (2 * (Z.of_nat (Datatypes.S n0) * (Z.pos b * eir_qfacZ n0))
                         = (Z.pos b * eir_qfacZ n0)
                           * (2 * Z.of_nat (Datatypes.S n0)))%Z) by ring.
          rewrite HKK.
          apply eir_qinvz_mul_qz; [exact HbFpos | lia]. }
        assert (HB : eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                     * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                        * (Z.pos b * eir_qfacZ n0)))
                     == eir_qz (2 * Z.pos b)).
        { assert (HKK : (2 * (Z.of_nat (Datatypes.S n0) * (Z.pos b * eir_qfacZ n0))
                         = (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                           * (2 * Z.pos b))%Z) by ring.
          rewrite HKK.
          apply eir_qinvz_mul_qz; [exact HposNF | lia]. }
        assert (HZ2big : eir_qz (2 * Z.of_nat (Datatypes.S n0))
                         == 2 * eir_qz (2 * Z.pos b) + 2 * 1).
        { assert (Hmid : eir_qz (2 * Z.of_nat (Datatypes.S n0))
                         == eir_qz (2 * (2 * Z.pos b) + 2 * 1)).
          { rewrite Hn1.
            replace (2 * (2 * Z.pos b + 1))%Z
              with (2 * (2 * Z.pos b) + 2 * 1)%Z by ring.
            apply Qeq_refl. }
          apply (Qeq_trans (eir_qz (2 * Z.of_nat (Datatypes.S n0)))
                           (eir_qz (2 * (2 * Z.pos b) + 2 * 1))
                           (2 * eir_qz (2 * Z.pos b) + 2 * 1)).
          - exact Hmid.
          - apply (Qeq_trans (eir_qz (2 * (2 * Z.pos b) + 2 * 1))
                             (eir_qz (2 * (2 * Z.pos b)) + eir_qz (2 * 1))
                             (2 * eir_qz (2 * Z.pos b) + 2 * 1)).
            + apply (Qeq_sym _ _ (eir_qz_plus (2 * (2 * Z.pos b)) (2 * 1))).
            + apply (Qplus_comp (eir_qz (2 * (2 * Z.pos b)))
                       (2 * eir_qz (2 * Z.pos b))
                       (Qeq_trans (eir_qz (2 * (2 * Z.pos b)))
                          (eir_qz 2 * eir_qz (2 * Z.pos b))
                          (2 * eir_qz (2 * Z.pos b))
                          (Qeq_sym _ _ (eir_qz_mul 2 (2 * Z.pos b)))
                          (Qmult_comp (eir_qz 2) 2 Hz2 (eir_qz (2 * Z.pos b))
                             (eir_qz (2 * Z.pos b))
                             (Qeq_refl (eir_qz (2 * Z.pos b)))))
                       (eir_qz (2 * 1)) (2 * 1)
                       (Qeq_trans (eir_qz (2 * 1)) (eir_qz 2 * eir_qz 1) (2 * 1)
                          (Qeq_sym _ _ (eir_qz_mul 2 1))
                          (Qmult_comp (eir_qz 2) 2 Hz2 (eir_qz 1) 1 Hz1))). }
        apply (eir_cancel_r (eir_qinvz (Z.pos b * eir_qfacZ n0)
                             - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                * eir_qfacZ n0))
                            (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                  * (Z.pos b * eir_qfacZ n0))))
                            (eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                             * (Z.pos b * eir_qfacZ n0))))).
        - apply eir_qz_neq. lia.
        - apply (Qeq_trans ((eir_qinvz (Z.pos b * eir_qfacZ n0)
                              - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                * eir_qfacZ n0))
                             * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                  * (Z.pos b * eir_qfacZ n0))))
                            (eir_qz (2 * Z.of_nat (Datatypes.S n0))
                             - 2 * eir_qz (2 * Z.pos b))
                            (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0)))
                             * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                  * (Z.pos b * eir_qfacZ n0))))).
          + apply (Qeq_trans ((eir_qinvz (Z.pos b * eir_qfacZ n0)
                                - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                  * eir_qfacZ n0))
                               * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                    * (Z.pos b * eir_qfacZ n0))))
                              ((eir_qinvz (Z.pos b * eir_qfacZ n0)
                               * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                    * (Z.pos b * eir_qfacZ n0))))
                              - 2 * (eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                       * eir_qfacZ n0)
                                      * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                           * (Z.pos b * eir_qfacZ n0)))))
                              (eir_qz (2 * Z.of_nat (Datatypes.S n0))
                               - 2 * eir_qz (2 * Z.pos b))).
            * ring.
            * apply (Qplus_comp (eir_qinvz (Z.pos b * eir_qfacZ n0)
                                 * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                      * (Z.pos b * eir_qfacZ n0))))
                     (eir_qz (2 * Z.of_nat (Datatypes.S n0))) HA
                     (- (2 * (eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                              * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0))))))
                     (- (2 * eir_qz (2 * Z.pos b)))
                     (Qopp_comp (2 * (eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                      * eir_qfacZ n0)
                                        * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                     * (Z.pos b * eir_qfacZ n0)))))
                        (2 * eir_qz (2 * Z.pos b))
                        (Qmult_comp 2 2 (Qeq_refl 2)
                           (eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                            * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                 * (Z.pos b * eir_qfacZ n0))))
                           (eir_qz (2 * Z.pos b)) HB))).
          + apply (Qeq_trans (eir_qz (2 * Z.of_nat (Datatypes.S n0))
                             - 2 * eir_qz (2 * Z.pos b))
                             (2 * eir_qz (2 * Z.pos b) + 2 * 1
                              - 2 * eir_qz (2 * Z.pos b))
                             (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0)))
                              * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0))))).
            * apply (Qplus_comp (eir_qz (2 * Z.of_nat (Datatypes.S n0)))
                       (2 * eir_qz (2 * Z.pos b) + 2 * 1) HZ2big
                       (- (2 * eir_qz (2 * Z.pos b)))
                       (- (2 * eir_qz (2 * Z.pos b)))
                       (Qeq_refl (- (2 * eir_qz (2 * Z.pos b))))).
            * apply (Qeq_trans (2 * eir_qz (2 * Z.pos b) + 2 * 1
                                - 2 * eir_qz (2 * Z.pos b))
                               (2 * 1)
                               (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                     * (Z.pos b * eir_qfacZ n0)))
                                * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                     * (Z.pos b * eir_qfacZ n0))))).
              -- ring.
              -- apply (Qeq_trans (2 * 1)
                         (2 * (eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                * (Z.pos b * eir_qfacZ n0)))
                                 * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                      * (Z.pos b * eir_qfacZ n0)))))
                         (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                * (Z.pos b * eir_qfacZ n0)))
                          * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                       * (Z.pos b * eir_qfacZ n0))))).
                 ++ apply (Qeq_sym _ _
                       (Qmult_comp 2 2 (Qeq_refl 2)
                          (eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                 * (Z.pos b * eir_qfacZ n0)))
                           * eir_qz (2 * (Z.of_nat (Datatypes.S n0)
                                                        * (Z.pos b * eir_qfacZ n0))))
                          1 HK2)).
                 ++ ring. }
      intros j. destruct j as [|k].
      * replace (n0 + 0)%nat with n0 by lia.
        apply eir_QltT_intro.
        apply (Qabs_gt _ _).
        apply (Qlt_le_trans _ (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0))))).
        -- apply eir_qlt_twice. apply eir_qltb_elim. apply eir_qinvz_posb.
           exact HposK.
        -- apply (Qle_trans _ (eir_qinvz (Z.pos b * eir_qfacZ n0)
                               - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                 * eir_qfacZ n0))).
           ++ apply eir_qeq_le. apply (Qeq_sym _ _ Hmargin).
           ++ apply (Qle_trans _ (eir_qinvz (Z.pos b * eir_qfacZ n0))).
              ** apply eir_qle_sub_r0. apply Qlt_le_weak. apply eir_qlt_mul_pos.
                 --- apply eir_qltb_elim. reflexivity.
                 --- apply eir_qltb_elim. apply eir_qinvz_posb. exact HposNF.
              ** exact Hlower.
      * assert (Htl : (eir_esum (n0 + Datatypes.S k)%nat - eir_esum n0
                       <= 2 * eir_eterm (Datatypes.S n0))%Q).
        { apply (Qle_trans _ (eir_etail n0 k)).
          - apply eir_qeq_le. apply (eir_etail_eq n0 k).
          - apply eir_etail_le. unfold n0. lia. }
        assert (Hchain : ((a # b)%Q - eir_esum (n0 + Datatypes.S k)%nat)
                         == ((a # b)%Q - eir_esum n0)
                            - (eir_esum (n0 + Datatypes.S k)%nat
                               - eir_esum n0)) by ring.
        assert (HtF : eir_eterm (Datatypes.S n0)
                      == eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)).
        { unfold eir_eterm. rewrite eir_qfacZ_succ. apply Qeq_refl. }
        assert (Heq2 : eir_qinvz (Z.pos b * eir_qfacZ n0)
                       - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)
                       == eir_qinvz (Z.pos b * eir_qfacZ n0)
                          - 2 * eir_eterm (Datatypes.S n0)).
        { apply (Qplus_comp (eir_qinvz (Z.pos b * eir_qfacZ n0))
                   (eir_qinvz (Z.pos b * eir_qfacZ n0))
                   (Qeq_refl (eir_qinvz (Z.pos b * eir_qfacZ n0)))
                   (- (2 * eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0)))
                   (- (2 * eir_eterm (Datatypes.S n0)))
                   (Qopp_comp (2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                   * eir_qfacZ n0))
                      (2 * eir_eterm (Datatypes.S n0))
                      (Qmult_comp 2 2 (Qeq_refl 2)
                         (eir_qinvz (Z.of_nat (Datatypes.S n0) * eir_qfacZ n0))
                         (eir_eterm (Datatypes.S n0)) (Qeq_sym _ _ HtF)))). }
        apply eir_QltT_intro.
        apply (Qabs_gt _ _).
        apply (Qlt_le_trans _ (2 * eir_qinvz (2 * (Z.of_nat (Datatypes.S n0)
                                                   * (Z.pos b * eir_qfacZ n0))))).
        -- apply eir_qlt_twice. apply eir_qltb_elim. apply eir_qinvz_posb.
           exact HposK.
        -- apply (Qle_trans _ (eir_qinvz (Z.pos b * eir_qfacZ n0)
                               - 2 * eir_qinvz (Z.of_nat (Datatypes.S n0)
                                                 * eir_qfacZ n0))).
           ++ apply eir_qeq_le. apply (Qeq_sym _ _ Hmargin).
           ++ apply (Qle_trans _ (eir_qinvz (Z.pos b * eir_qfacZ n0)
                                  - 2 * eir_eterm (Datatypes.S n0))).
              ** apply eir_qeq_le. exact Heq2.
              ** apply (Qle_trans _ ((a # b)%Q - eir_esum n0
                                     - 2 * eir_eterm (Datatypes.S n0))).
                 --- apply eir_qle_sub_r. exact Hlower.
                 --- apply (Qle_trans _ ((a # b)%Q - eir_esum n0
                                         - (eir_esum (n0 + Datatypes.S k)%nat
                                            - eir_esum n0))).
                     +++ apply eir_qle_sub_l. exact Htl.
                     +++ apply eir_qeq_le. exact (Qeq_sym _ _ Hchain).
Qed.

(* Constructive convergence rate: the partial sums form a Cauchy
   sequence with the explicit modulus 2/(n+1)!: after the first two
   partial sums, any two of them differ by at most 2 * (1/2!) = 1. *)
Theorem eir_esum_cauchy_modulus :
  forall j j' : nat,
    eir_QleT (Qabs (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat))
             (2 * eir_eterm 2)%Q.
Proof.
  intros j j'.
  destruct (Qle_bool (eir_esum (1 + j)%nat) (eir_esum (1 + j')%nat))
    eqn:Hqb.
  - assert (Hle : (eir_esum (1 + j)%nat <= eir_esum (1 + j')%nat)%Q)
      by (apply Qle_bool_iff; exact Hqb).
    apply eir_QleT_intro.
    apply (Qle_trans _ (- (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat))).
    + apply eir_qeq_le.
      apply (Qeq_trans (Qabs (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat))
                       (eir_esum (1 + j')%nat - eir_esum (1 + j)%nat)
                       (- (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat))).
      * apply eir_abs_opp_diff. exact Hle.
      * ring.
    + apply (Qle_trans _ (eir_esum (1 + j')%nat - eir_esum (1 + j)%nat)).
      * apply eir_qeq_le. ring.
      * apply (Qle_trans _ (eir_esum (1 + j')%nat - eir_esum 1)).
        -- apply eir_qle_sub_l. apply eir_esum_mono. lia.
        -- destruct j' as [|k].
           ++ replace (1 + 0)%nat with (1%nat) by lia.
              apply (Qle_trans _ 0).
              ** apply eir_qeq_le. ring.
              ** apply Qlt_le_weak. apply eir_qlt_mul_pos.
                 --- apply eir_qltb_elim. reflexivity.
                 --- apply eir_eterm_pos.
           ++ apply (Qle_trans _ (eir_etail 1 k)).
              --- apply eir_qeq_le. apply (eir_etail_eq 1 k).
              --- apply eir_etail_le. lia.
  - assert (Hgt : (eir_esum (1 + j')%nat < eir_esum (1 + j)%nat)%Q).
    { assert (Hnle : ~ (eir_esum (1 + j)%nat <= eir_esum (1 + j')%nat)%Q).
      { intros Hc. apply Qle_bool_iff in Hc. rewrite Hqb in Hc. discriminate. }
      apply Qnot_le_lt. exact Hnle. }
    apply eir_QleT_intro.
    assert (Hgt0 : (0 < eir_esum (1 + j)%nat - eir_esum (1 + j')%nat)%Q)
      by (apply eir_qsub_pos; exact Hgt).
    assert (Hab : Qabs (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat)
                  == eir_esum (1 + j)%nat - eir_esum (1 + j')%nat)
      by (apply eir_Qabs_eq_le; apply Qlt_le_weak; exact Hgt0).
    apply (Qle_trans _ (eir_esum (1 + j)%nat - eir_esum (1 + j')%nat)).
    + apply eir_qeq_le. exact Hab.
    + apply (Qle_trans _ (eir_esum (1 + j)%nat - eir_esum 1)).
      * apply eir_qle_sub_l. apply eir_esum_mono. lia.
      * destruct j as [|k].
        -- replace (1 + 0)%nat with (1%nat) by lia.
           apply (Qle_trans _ 0).
           ** apply eir_qeq_le. ring.
           ** apply Qlt_le_weak. apply eir_qlt_mul_pos.
              --- apply eir_qltb_elim. reflexivity.
              --- apply eir_eterm_pos.
        -- apply (Qle_trans _ (eir_etail 1 k)).
           --- apply eir_qeq_le. apply (eir_etail_eq 1 k).
           --- apply eir_etail_le. lia.
Qed.

Print Assumptions eir_etail_le.
Print Assumptions eir_esum_scaled.
Print Assumptions eir_dist_scaled.
Print Assumptions eir_esum_cauchy_modulus.
Print Assumptions eir_e_irrational.
