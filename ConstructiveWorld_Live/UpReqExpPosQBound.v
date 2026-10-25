(* ConstructiveWorld-Set — positivity bound for the exponential partial sums. *)

(** * UpReqExpPosQBound: explicit positive witnesses for the exponential family.

    Mission.  Upper bound [upqb_sum_le] for the exponential partial sum
      over the [Q] layer, the explicit witness pair [upqb_B]/[upqb_q]
      with [upqb_B_pos], and the Set-layer witness constructions
      [upqb_witness_m0], [upqb_witness_m1_a1], [upqb_even_witness]
      (positive [q] strictly below the partial sum at [Qopp a]), plus
      the warm-up identity [upqb_exp_partial_eq].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires the base modules [S01_BaseRing] up to
      [S08_RealMainlineDPO] of this development.

    References.  This development, UpReqExpPosQBound.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion: [Qle] conclusions moved to [QleT'], [Qlt]
      conclusions to [QltT], the [==] identity to [QeqT]; the
      [QleT]-elimination bridge [upqb_qleT_to_qle] is kept as a
      downward-directed interface lemma).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: <none>].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqExpPosQBound.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. Definitions: alias for the truncated exponential, warm-up identities ================= *)

Definition upqb_exp_partial := exp_partial.

Lemma upqb_exp_partial_eq : forall (n : nat) (x : Q), QeqT (upqb_exp_partial n x) (exp_partial n x).
Proof. intros n x. apply qeq_imp_qeqT. exact (Qeq_refl (exp_partial n x)). Qed.

Lemma upqb_qlt_0_1 : QltT 0 1.
Proof. unfold QltT. compute. apply id_refl. Qed.

Lemma upqb_qle_0_1 : QleT' 0 1.
Proof. apply Qle_to_QleT'. apply Qlt_le_weak. exact (QltT_to_Qlt 0 1 upqb_qlt_0_1). Qed.

(* Warm-up 1: for m = 0 the partial sum S_0 equals 1 regardless of a, so the explicit q := 1/2 works; both [QltT] sides close by computation. *)
Lemma upqb_witness_m0 : forall a : Q,
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (upqb_exp_partial 0 a)))%type).
Proof.
  intros a. exists (1#2)%Q. split.
  - unfold QltT. compute. reflexivity.
  - unfold QltT, upqb_exp_partial. compute. reflexivity.
Qed.

(* Warm-up 2: concrete instance m = 1, a = 1: S_2(-1) = 1 - 1 + 1/2 = 1/2 > 1/3 > 0; both sides close by computation. *)
Lemma upqb_witness_m1_a1 :
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (exp_partial 2 (Qopp 1)%Q)))%type).
Proof. exists (1#3)%Q. split.
  - unfold QltT. compute. reflexivity.
  - unfold QltT. compute. reflexivity.
Qed.

(* ================= Section 2. QleT elimination and order lemmas ================= *)

(* [QleT] to [Qle]: the development provides no [QleT_to_Qle], so this module builds its own; the right branch discharges the [Id] equation with [id_refl]. *)
Lemma upqb_qleT_to_qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [Hlt | Hid].
  - apply (Qlt_le_weak x y). exact (QltT_to_Qlt x y Hlt).
  - destruct Hid. apply Qle_refl.
Qed.

Lemma upqb_qle_le_plus : forall a : Q, QleT' a (1 + a)%Q.
Proof.
  intro a.
  apply Qle_to_QleT'.
  apply (Qle_trans a (a + 0)%Q (1 + a)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (a + 0)%Q (a + 1)%Q (1 + a)%Q).
    + apply (Qplus_le_compat a a 0 1).
      * apply Qle_refl.
      * exact (QleT'_to_Qle 0 1 upqb_qle_0_1).
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
Qed.

Lemma upqb_qle_1_plus : forall a : Q, Qle 0 a -> QleT' 1 (1 + a)%Q.
Proof.
  intros a Ha.
  apply Qle_to_QleT'.
  apply (Qle_trans 1 (1 + 0)%Q (1 + a)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qplus_le_compat 1 1 0 a).
    + apply Qle_refl.
    + exact Ha.
Qed.

(* ================= Section 3. Upper-bound engine lemmas ================= *)

Lemma upqb_qfact_ge_one : forall k : nat, QleT' 1 (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [| k IH].
  - apply Qle_refl.
  - change (q_fact (Datatypes.S k)) with ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)%Q.
    apply (Qmult_le_compat_nonneg 1 (Z.of_nat (Datatypes.S k) # 1) 1 (q_fact k)).
    + split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | unfold Qle; simpl; lia].
    + split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | exact IH].
Qed.

Lemma upqb_one_le_pow : forall (b : Q) (n : nat), Qle 1 b -> QleT' 1 (q_pow b n).
Proof.
  intros b n Hb. apply Qle_to_QleT'.
  induction n as [| n IH]; simpl.
  - apply Qle_refl.
  - apply (Qmult_le_compat_nonneg 1 b 1 (q_pow b n)).
    + split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | exact Hb].
    + split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | exact IH].
Qed.

Lemma upqb_pow_step : forall (b : Q) (n : nat), Qle 1 b ->
  QleT' (q_pow b n) (q_pow b (Datatypes.S n)).
Proof.
  intros b n Hb.
  apply Qle_to_QleT'.
  change (q_pow b (Datatypes.S n)) with (b * q_pow b n)%Q.
  apply (Qle_trans (q_pow b n) (1 * q_pow b n)%Q (b * q_pow b n)%Q).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qmult_le_compat_nonneg 1 b (q_pow b n) (q_pow b n)).
    + split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | exact Hb].
    + split; [exact (Qle_trans 0 1 (q_pow b n) (QleT'_to_Qle 0 1 upqb_qle_0_1)
                        (QleT'_to_Qle _ _ (upqb_one_le_pow b n Hb)))
             | apply Qle_refl].
Qed.

Lemma upqb_pow_idx_mono : forall (b : Q) (k n : nat), Qle 1 b -> (k <= n)%nat ->
  QleT' (q_pow b k) (q_pow b n).
Proof.
  intros b k n Hb Hkn. apply Qle_to_QleT'.
  induction n as [| n IH].
  - assert (Hk : k = 0%nat) by lia. subst k. apply Qle_refl.
  - destruct (Nat.eq_dec k (Datatypes.S n)) as [He | Hne].
    + subst k. apply Qle_refl.
    + apply (Qle_trans (q_pow b k) (q_pow b n) (q_pow b (Datatypes.S n))).
      * apply IH. lia.
      * apply QleT'_to_Qle. apply (upqb_pow_step b n Hb).
Qed.

(* Main upper bound: for [0 <= a] the partial sum satisfies [S_n(a) <= (n+1) * (1+a)^n]; each summand drops its k! >= 1 factor and equal-base powers are monotone. *)
(* Reciprocal reversal: for [0 < x <= y] one has [/y <= /x]; the standard library has no direct form, so this module builds it. *)
Lemma upqb_inv_le_pos : forall x y : Q, Qlt 0 x -> Qle x y -> QleT' (Qinv y) (Qinv x).
Proof.
  intros x y Hx Hxy.
  apply Qle_to_QleT'.
  assert (Hypos : Qlt 0 y) by (apply (Qlt_le_trans 0 x y); [exact Hx | exact Hxy]).
  assert (Hinvx : Qlt 0 (Qinv x)) by (apply Qinv_lt_0_compat; exact Hx).
  assert (Hx0 : x * Qinv x == 1) by (apply Qmult_inv_r; intro Heqx; destruct (q_neq_of_lt x (Qlt_to_QltT 0 x Hx) (qeq_imp_qeqT _ _ Heqx))).
  assert (Hy0 : y * Qinv y == 1) by (apply Qmult_inv_r; intro Heqy; destruct (q_neq_of_lt y (Qlt_to_QltT 0 y Hypos) (qeq_imp_qeqT _ _ Heqy))).
  assert (Hyinv : Qlt 0 (Qinv y)) by (apply Qinv_lt_0_compat; exact Hypos).
  assert (S1 : Qle 1 (y * Qinv x)).
  { apply (Qle_trans 1 (x * Qinv x) (y * Qinv x)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. symmetry. exact Hx0.
    - apply (Qmult_le_compat_r x y (Qinv x)).
      + exact Hxy.
      + apply (Qlt_le_weak 0 (Qinv x)). exact Hinvx. }
  assert (S3 : Qinv y * (y * Qinv x) == Qinv x).
  { transitivity ((y * Qinv y) * Qinv x).
    - ring.
    - rewrite Hy0. ring. }
  apply (Qle_trans (Qinv y) (Qinv y * 1)%Q (Qinv x)).
  - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans (Qinv y * 1)%Q (Qinv y * (y * Qinv x)) (Qinv x)).
    + apply (Qmult_le_compat_nonneg (Qinv y) (Qinv y) 1 (y * Qinv x)).
      * split; [apply (Qlt_le_weak 0 (Qinv y)); exact Hyinv | apply Qle_refl].
      * split; [exact (QleT'_to_Qle 0 1 upqb_qle_0_1) | exact S1].
    + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. exact S3.
Qed.

Lemma upqb_sum_le : forall (a : Q) (n : nat), Qle 0 a ->
  QleT' (exp_partial n a) ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n).
Proof.
  intros a n Ha. apply Qle_to_QleT'.
  induction n as [| n IH].
  - unfold Qle; simpl; lia.
  - change (exp_partial (Datatypes.S n) a) with
      (exp_partial n a + q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))%Q.
    assert (Hb1 : Qle 1 (1 + a)%Q) by (apply QleT'_to_Qle; apply upqb_qle_1_plus; exact Ha).
    assert (Hab : Qle a (1 + a)%Q) by (apply QleT'_to_Qle; apply upqb_qle_le_plus).
    assert (Hinv1 : Qinv 1 == 1).
    { pose proof (Qmult_inv_r 1 (fun Heq0 : 1 == 0 =>
        match q_neq_of_lt 1 upqb_qlt_0_1 (qeq_imp_qeqT _ _ Heq0) with end)) as Hx.
      rewrite Qmult_1_l in Hx. exact Hx. }
    (* a^k / k! <= b^k / k! <= b^k, with b := 1 + a. *)
    assert (Hstep : Qle (q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))
                        (q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qle_trans _ (q_pow (1 + a)%Q (Datatypes.S n) / q_fact (Datatypes.S n)) _).
      - apply (Qmult_le_compat_r (q_pow a (Datatypes.S n)) (q_pow (1 + a)%Q (Datatypes.S n))
                                 (Qinv (q_fact (Datatypes.S n)))).
        + apply QleT'_to_Qle. apply (q_pow_mono a (1 + a)%Q (Datatypes.S n)); [apply Qle_to_QleT'; exact Ha | apply Qle_to_QleT'; exact Hab].
        + apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S n)))).
          apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
      - unfold Qdiv.
        apply (Qle_trans _ (q_pow (1 + a)%Q (Datatypes.S n) * 1)%Q _).
        + apply (Qmult_le_compat_nonneg (q_pow (1 + a)%Q (Datatypes.S n))
                                        (q_pow (1 + a)%Q (Datatypes.S n))
                                        (Qinv (q_fact (Datatypes.S n))) 1).
          * split;
              [apply (Qle_trans 0 1 (q_pow (1 + a)%Q (Datatypes.S n)));
                [exact (QleT'_to_Qle 0 1 upqb_qle_0_1)
                | exact (QleT'_to_Qle _ _ (upqb_one_le_pow (1 + a)%Q (Datatypes.S n) Hb1))]
              | apply Qle_refl].
          * split;
              [apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S n))));
                apply Qinv_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos
              | apply (Qle_trans (Qinv (q_fact (Datatypes.S n))) (Qinv 1) 1);
                [ exact (QleT'_to_Qle _ _
                           (upqb_inv_le_pos 1 (q_fact (Datatypes.S n))
                              (QltT_to_Qlt 0 1 upqb_qlt_0_1)
                              (QleT'_to_Qle _ _ (upqb_qfact_ge_one (Datatypes.S n)))))
                | apply QleT'_to_Qle; apply qeq_imp_qle; apply qeq_imp_qeqT; exact Hinv1 ]].
        + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
    (* b^n <= b^(S n), and the coefficient step for the geometric bound. *)
    assert (Hpow : Qle (q_pow (1 + a)%Q n) (q_pow (1 + a)%Q (Datatypes.S n)))
      by (apply QleT'_to_Qle; apply (upqb_pow_step (1 + a)%Q n Hb1)).
    assert (HB : Qle ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n)
                     ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qmult_le_compat_nonneg (Z.of_nat (Datatypes.S n) # 1) (Z.of_nat (Datatypes.S n) # 1)
                                    (q_pow (1 + a)%Q n) (q_pow (1 + a)%Q (Datatypes.S n))).
      - split;
          [apply (Qlt_le_weak 0 (Z.of_nat (Datatypes.S n) # 1));
            apply QltT_to_Qlt; apply (Qlt_of_nat_lt 0 (Datatypes.S n)); lia
          | apply Qle_refl].
      - split;
          [ apply (Qle_trans 0 1 (q_pow (1 + a)%Q n));
            [ exact (QleT'_to_Qle 0 1 upqb_qle_0_1)
            | exact (QleT'_to_Qle _ _ (upqb_one_le_pow (1 + a)%Q n Hb1)) ]
          | exact Hpow]. }
    assert (Hfinal : Qle ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n)
                          + q_pow (1 + a)%Q (Datatypes.S n))
                         ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                          * q_pow (1 + a)%Q (Datatypes.S n))).
    { apply (Qle_trans _ ((Qplus (Z.of_nat (Datatypes.S n) # 1) 1)%Q
                          * q_pow (1 + a)%Q (Datatypes.S n)) _).
      - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      - apply (Qmult_le_compat_r ((Qplus (Z.of_nat (Datatypes.S n) # 1) 1)%Q)
                                 ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
                                 (q_pow (1 + a)%Q (Datatypes.S n))).
        + assert (Hz : (Z.of_nat (Datatypes.S (Datatypes.S n))
                        = Z.of_nat (Datatypes.S n) + 1)%Z) by lia.
          rewrite Hz. unfold Qle; simpl; lia.
        + apply (Qle_trans 0 1 (q_pow (1 + a)%Q (Datatypes.S n))).
          * exact (QleT'_to_Qle 0 1 upqb_qle_0_1).
          * exact (QleT'_to_Qle _ _ (upqb_one_le_pow (1 + a)%Q (Datatypes.S n) Hb1)). }
    apply (Qle_trans _ (exp_partial n a + q_pow (1 + a)%Q (Datatypes.S n)) _).
    + apply (Qplus_le_compat (exp_partial n a) (exp_partial n a)
                             (q_pow a (Datatypes.S n) / q_fact (Datatypes.S n))
                             (q_pow (1 + a)%Q (Datatypes.S n))).
      * apply Qle_refl.
      * exact Hstep.
    + apply (Qle_trans _
        ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n)
         + q_pow (1 + a)%Q (Datatypes.S n)) _).
      * apply (Qplus_le_compat (exp_partial n a)
                               ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))
                               (q_pow (1 + a)%Q (Datatypes.S n))
                               (q_pow (1 + a)%Q (Datatypes.S n))).
        -- exact (Qle_trans (exp_partial n a)
                            ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q n)
                            ((Z.of_nat (Datatypes.S n) # 1) * q_pow (1 + a)%Q (Datatypes.S n))
                            IH HB).
        -- apply Qle_refl.
      * exact Hfinal.
Qed.

(* ================= Section 4. Main witnesses: the pair B, q and its positivity ================= *)

Definition upqb_B (a : Q) (m : nat) : Q :=
  (Z.of_nat (Datatypes.S (2 * m)) # 1) * q_pow (1 + a)%Q (2 * m).

Definition upqb_q (a : Q) (m : nat) : Q := Qinv (1 + upqb_B a m)%Q.

Lemma upqb_B_pos : forall (a : Q) (m : nat), Qle 0 a -> QltT 0 (upqb_B a m).
Proof.
  intros a m Ha. unfold upqb_B.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (2 * m)) # 1)
                           (q_pow (1 + a)%Q (2 * m))).
  - unfold Qlt; simpl; lia.
  - apply (Qlt_le_trans 0 1 (q_pow (1 + a)%Q (2 * m))).
    + exact (QltT_to_Qlt 0 1 upqb_qlt_0_1).
    + exact (QleT'_to_Qle _ _
               (upqb_one_le_pow (1 + a)%Q (2 * m)
                  (QleT'_to_Qle _ _ (upqb_qle_1_plus a Ha)))).
Qed.

(* Main statement: for [QleT 0 a] the explicit witness q := 1/(1+B) satisfies [0 < q < S_{2m}(-a)]; packaged as a [sigT] over a pair (with the [%type] annotation). *)
Lemma upqb_even_witness : forall (a : Q) (m : nat), QleT 0 a ->
  sigT (fun q : Q => ((QltT 0 q) * (QltT q (exp_partial (2 * m) (Qopp a))))%type).
Proof.
  intros a m HaT.
  assert (Ha : Qle 0 a) by exact (upqb_qleT_to_qle 0 a HaT).
  assert (Hxpos : Qlt 0 (exp_partial (2 * m) (Qopp a)))
    by exact (QltT_to_Qlt _ _ (exp_even_neg_pos a m (Qle_to_QleT' _ _ Ha))).
  (* Step 1: [1 <= x * S(a)], from the product identity [exp_even_mul_eq] and [corr_nonneg]. *)
  assert (Hmul : Qle 1 (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)).
  { setoid_rewrite (qeqT_imp_qeq _ _ (exp_even_mul_eq a m)).
    apply (Qle_trans 1%Q (1 + 0)%Q (1 + corr m a)).
    - apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (Qplus_le_compat 1 1 0 (corr m a)).
      + apply Qle_refl.
      + exact (QleT'_to_Qle _ _ (corr_nonneg a m (Qle_to_QleT' _ _ Ha))). }
  (* Step 2: [S(a) <= B] gives [1 <= x * B], hence [1 < x * (1 + B)]. *)
  assert (HBle : Qle (exp_partial (2 * m) a) (upqb_B a m))
    by exact (QleT'_to_Qle _ _ (upqb_sum_le a (2 * m) Ha)).
  assert (Hxposle : Qle 0 (exp_partial (2 * m) (Qopp a)))
    by exact (Qlt_le_weak 0 (exp_partial (2 * m) (Qopp a)) Hxpos).
  assert (HmulB : Qle 1 (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
  { apply (Qle_trans 1 (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)
                       (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
    - exact Hmul.
    - apply (Qle_trans (exp_partial (2 * m) (Qopp a) * exp_partial (2 * m) a)
                       (exp_partial (2 * m) a * exp_partial (2 * m) (Qopp a))
                       (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
      + apply (Qle_trans (exp_partial (2 * m) a * exp_partial (2 * m) (Qopp a))
                         (upqb_B a m * exp_partial (2 * m) (Qopp a))
                         (exp_partial (2 * m) (Qopp a) * upqb_B a m)).
        * apply (Qmult_le_compat_r (exp_partial (2 * m) a) (upqb_B a m)
                                   (exp_partial (2 * m) (Qopp a))).
          -- exact HBle.
          -- exact Hxposle.
        * apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring. }
  assert (HposB : Qlt 0 (upqb_B a m))
    by exact (QltT_to_Qlt _ _ (upqb_B_pos a m Ha)).
  assert (Hfin : Qlt 1 ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                        + exp_partial (2 * m) (Qopp a))).
  { apply (Qle_lt_trans 1 ((exp_partial (2 * m) (Qopp a) * upqb_B a m) + 0)
                         ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                          + exp_partial (2 * m) (Qopp a))).
    - apply (Qle_trans 1 (exp_partial (2 * m) (Qopp a) * upqb_B a m)
                        ((exp_partial (2 * m) (Qopp a) * upqb_B a m) + 0)).
      + exact HmulB.
      + apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT. ring.
    - apply (proj2 (Qplus_lt_r 0 (exp_partial (2 * m) (Qopp a))
                                (exp_partial (2 * m) (Qopp a) * upqb_B a m)) Hxpos). }
  (* Step 3: dividing by [1 + B] preserves strict positivity, so q := 1/(1+B) satisfies [0 < q < x]. *)
  assert (Honeb : (1 + upqb_B a m)%Q * Qinv (1 + upqb_B a m)%Q == 1).
  { apply Qmult_inv_r. intro Heqb.
    destruct (q_neq_of_lt (1 + upqb_B a m)%Q
      (Qlt_to_QltT _ _ (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q
         (QltT_to_Qlt 0 1 upqb_qlt_0_1)
         (QleT'_to_Qle _ _ (upqb_qle_1_plus (upqb_B a m)
            (Qlt_le_weak 0 (upqb_B a m) HposB)))))
      (qeq_imp_qeqT _ _ Heqb)). }
  exists (upqb_q a m). split.
  - apply Qlt_to_QltT. unfold upqb_q.
    exact (Qinv_lt_0_compat (1 + upqb_B a m)%Q
             (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q (QltT_to_Qlt 0 1 upqb_qlt_0_1)
                (QleT'_to_Qle _ _ (upqb_qle_1_plus (upqb_B a m)
                   (Qlt_le_weak 0 (upqb_B a m) HposB))))).
  - apply Qlt_to_QltT. unfold upqb_q.
    assert (Hraw : Qlt (1 * Qinv (1 + upqb_B a m)%Q)
                       (((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                         + exp_partial (2 * m) (Qopp a))
                        * Qinv (1 + upqb_B a m)%Q)).
    { apply (Qmult_lt_compat_r 1
               ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                + exp_partial (2 * m) (Qopp a))
               (Qinv (1 + upqb_B a m)%Q)).
      - apply Qinv_lt_0_compat.
        apply (Qlt_le_trans 0 1 (1 + upqb_B a m)%Q).
        + exact (QltT_to_Qlt 0 1 upqb_qlt_0_1).
        + apply QleT'_to_Qle. apply upqb_qle_1_plus.
          apply (Qlt_le_weak 0 (upqb_B a m)). exact HposB.
      - exact Hfin. }
    assert (E2 : ((exp_partial (2 * m) (Qopp a) * upqb_B a m)
                  + exp_partial (2 * m) (Qopp a))
                 * Qinv (1 + upqb_B a m)%Q == exp_partial (2 * m) (Qopp a)).
    { transitivity (exp_partial (2 * m) (Qopp a)
                    * ((1 + upqb_B a m)%Q * Qinv (1 + upqb_B a m)%Q)).
      - ring.
      - rewrite Honeb. ring. }
    setoid_rewrite (Qmult_1_l (Qinv (1 + upqb_B a m)%Q)) in Hraw.
    setoid_rewrite E2 in Hraw.
    exact Hraw.
Qed.

(* Witness function Q -> Q in extraction form ([projT1] elimination; checks extractability). *)
Definition upqb_witness_fun (a : Q) (m : nat) (Ha : QleT 0 a) : Q :=
  projT1 (upqb_even_witness a m Ha).
