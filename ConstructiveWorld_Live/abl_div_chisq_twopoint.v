(* ConstructiveWorld-Set -- two-point chi-square divergence algebra bridge. *)

(** * abl_div_chisq_twopoint: two-point chi-square divergence carrier.

    Mission.  Carrier [div2_cs] = (p−q)²/q + (p−q)²/(1−q) with a closed-form
      identity (pure ring), Bishop-form nonnegativity, an unconditional lower
      arm (four·TV² ≤ χ²) and a conditional upper arm (χ² ≤ two·TV²/m under a
      minimum mass m); no logarithms, no exponentials, no case splits.

    Dependencies.  [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [PinskerTwoPoint] ([p2_tvsq], [p2_one_minus],
      [p2_diff], [p2_ring_eq]), [UpRealLeB] ([real_le_b] and the square
      nonnegativity finisher), [UpRealLeB2] (Bishop sum compatibility),
      [UpRealLeB3] (Bishop transport family).

    References.  This development, abl_div_chisq_twopoint.v, the baseline
      module in ConstructiveWorld-Main whose statement names and proof bodies
      are carried over verbatim; this edition is a comment-face English wash.

    Constructivity.  All exits stay at the Set layer; the non-strict order is
      the Bishop-form [real_le_b] (same exit style as the in-service
      [pnk2_pinsker_one], no Or-form square-nonnegativity slot); zero
      admission-style statements, zero classical axioms, all closed by [Qed];
      positivity certificates carried explicitly alongside.

    Build.  [source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s
      65532 && cd <pool> && nice -19 rocq c -native-compiler no -Q <cache-root>
      "" abl_div_chisq_twopoint.v] compiles cleanly (exit 0); the artifact
      starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import PinskerTwoPoint.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ---- 0. numeric constants: two and four, built by explicit accumulation of one ---- *)

Definition d2_two : Real := real_plus real_one real_one.
Definition d2_four : Real := real_plus d2_two d2_two.

Lemma d2_two_pos : real_lt real_zero d2_two.
Proof.
  exact (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.

Lemma d2_four_pos : real_lt real_zero d2_four.
Proof.
  exact (real_plus_positive d2_two d2_two d2_two_pos d2_two_pos).
Qed.

(* ---- 1. carrier definition: χ²(P‖Q) := (p−q)²/q + (p−q)²/(1−q) ---- *)

Definition div2_cs (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
            (real_mult (p2_tvsq p q) (real_inv_pos (p2_one_minus q) Hq1)).

(* ---- 2. cancellation and doubling helpers (shared throughout) ---- *)

(* x·y·inv(y) == x (right cancellation by real_inv_pos_correct, chained in real_eq) *)
Lemma d2_mult_inv_r : forall (x y : Real) (Hy : real_lt real_zero y),
  real_eq (real_mult (real_mult x y) (real_inv_pos y Hy)) x.
Proof.
  intros x y Hy.
  apply (real_eq_trans (real_mult (real_mult x y) (real_inv_pos y Hy))
                       (real_mult x (real_mult y (real_inv_pos y Hy))) x).
  - apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans (real_mult x (real_mult y (real_inv_pos y Hy)))
             (real_mult x real_one) x).
    + apply (RealSetoid.real_eq_mult_compat x
               (real_mult y (real_inv_pos y Hy)) x real_one).
      * apply real_eq_refl.
      * exact (real_inv_pos_correct y Hy).
    + apply real_mult_one.
Qed.

(* doubling identity for arbitrary X: X+X == two·X (pointwise pure ring;
   X may hold any opaque term) *)
Lemma d2_double : forall X : Real,
  real_eq (real_plus X X) (real_mult (real_plus real_one real_one) X).
Proof.
  intros X.
  apply real_eq_of_zero_diff. intro n0.
  apply qeq_imp_qeqT.
  repeat match goal with [ x : Real |- _ ] => destruct x end.
  cbn [projT1 real_plus real_mult real_one real_zero].
  ring.
Qed.

(* ---- 3. partial fractions and the closed-form identity (piece 1a) ---- *)

(* multiplicative regrouping: (a·b)·c == b·(a·c) (pure ring chain) *)
Lemma d2_swap_assoc : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult b (real_mult a c)).
Proof.
  intros a b c.
  apply (real_eq_trans (real_mult (real_mult a b) c)
                       (real_mult a (real_mult b c))
                       (real_mult b (real_mult a c))).
  - apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans (real_mult a (real_mult b c))
                         (real_mult (real_mult b a) c)
                         (real_mult b (real_mult a c))).
    + apply (real_eq_trans (real_mult a (real_mult b c))
                           (real_mult (real_mult a b) c)
                           (real_mult (real_mult b a) c)).
      * apply real_mult_assoc.
      * apply (RealSetoid.real_eq_mult_compat (real_mult a b) c
                 (real_mult b a) c).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* partial-fraction kernel: inv(q·(1−q)) == inv(q)+inv(1−q).
   route: real_inv_unique, with q·(1−q) as common multiplier; both sides
   multiply out to one. *)
Lemma d2_inv_split : forall (q : Real) (Hq : real_lt real_zero q)
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
          (real_plus (real_inv_pos q Hq)
                     (real_inv_pos (p2_one_minus q) Hq1)).
Proof.
  intros q Hq Hq1 Hqq1.
  apply (real_inv_unique (real_mult q (p2_one_minus q))
           (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
           (real_plus (real_inv_pos q Hq)
                      (real_inv_pos (p2_one_minus q) Hq1))).
  - apply real_inv_pos_correct.
  - apply (real_eq_trans
             (real_mult (real_mult q (p2_one_minus q))
                (real_plus (real_inv_pos q Hq)
                           (real_inv_pos (p2_one_minus q) Hq1)))
             (real_plus
                (real_mult (p2_one_minus q)
                           (real_mult q (real_inv_pos q Hq)))
                (real_mult q
                   (real_mult (p2_one_minus q)
                              (real_inv_pos (p2_one_minus q) Hq1))))
             real_one).
    + apply (real_eq_trans
               (real_mult (real_mult q (p2_one_minus q))
                  (real_plus (real_inv_pos q Hq)
                             (real_inv_pos (p2_one_minus q) Hq1)))
               (real_plus
                  (real_mult (real_mult q (p2_one_minus q))
                             (real_inv_pos q Hq))
                  (real_mult (real_mult q (p2_one_minus q))
                             (real_inv_pos (p2_one_minus q) Hq1)))
               (real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult q (real_inv_pos q Hq)))
                  (real_mult q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))))).
      * apply real_distrib.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_mult q (p2_one_minus q)) (real_inv_pos q Hq))
                 (real_mult (real_mult q (p2_one_minus q))
                            (real_inv_pos (p2_one_minus q) Hq1))
                 (real_mult (p2_one_minus q) (real_mult q (real_inv_pos q Hq)))
                 (real_mult q
                    (real_mult (p2_one_minus q)
                               (real_inv_pos (p2_one_minus q) Hq1)))).
        -- exact (d2_swap_assoc q (p2_one_minus q) (real_inv_pos q Hq)).
        -- apply real_eq_sym. apply real_mult_assoc.
    + apply (real_eq_trans
               (real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult q (real_inv_pos q Hq)))
                  (real_mult q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))))
               (real_plus (p2_one_minus q) q)
               real_one).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (p2_one_minus q) (real_mult q (real_inv_pos q Hq)))
                 (real_mult q
                    (real_mult (p2_one_minus q)
                               (real_inv_pos (p2_one_minus q) Hq1)))
                 (p2_one_minus q) q).
        -- apply (real_eq_trans
                     (real_mult (p2_one_minus q)
                                (real_mult q (real_inv_pos q Hq)))
                     (real_mult (p2_one_minus q) real_one)
                     (p2_one_minus q)).
        ++ apply (RealSetoid.real_eq_mult_compat (p2_one_minus q)
                     (real_mult q (real_inv_pos q Hq))
                     (p2_one_minus q) real_one).
        ** apply real_eq_refl.
        ** exact (real_inv_pos_correct q Hq).
        ++ apply real_mult_one.
        -- apply (real_eq_trans
                     (real_mult q
                        (real_mult (p2_one_minus q)
                                   (real_inv_pos (p2_one_minus q) Hq1)))
                     (real_mult q real_one)
                     q).
        ++ apply (RealSetoid.real_eq_mult_compat q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))
                     q real_one).
        ** apply real_eq_refl.
        ** exact (real_inv_pos_correct (p2_one_minus q) Hq1).
        ++ apply real_mult_one.
      * p2_ring_eq.
Qed.

(* piece 1a: closed-form identity div2_cs == (p−q)²·inv(q·(1−q))
   (pure distributivity plus partial fractions) *)
Theorem div2_cs_closed : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (div2_cs p q Hq Hq1)
          (real_mult (p2_tvsq p q)
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
Proof.
  intros p q Hq Hq1 Hqq1.
  unfold div2_cs.
  apply (real_eq_trans
           (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                      (real_mult (p2_tvsq p q)
                                 (real_inv_pos (p2_one_minus q) Hq1)))
           (real_mult (p2_tvsq p q)
              (real_plus (real_inv_pos q Hq)
                         (real_inv_pos (p2_one_minus q) Hq1)))
           (real_mult (p2_tvsq p q)
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
  - apply real_eq_sym. apply real_distrib.
  - apply (RealSetoid.real_eq_mult_compat (p2_tvsq p q)
             (real_plus (real_inv_pos q Hq)
                        (real_inv_pos (p2_one_minus q) Hq1))
             (p2_tvsq p q)
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (d2_inv_split q Hq Hq1 Hqq1).
Qed.

(* ---- 4. the Bishop scaling lemma and piece 1b (nonnegativity) ---- *)

(* Bishop-form scaling lemma: Or-form a≤b with Bishop-form 0≤c gives
   c·a ≤_B c·b.  equality branch: multiplication compatibility plus strict
   translation; strict branch: b−a>0 makes c·(b−a) Bishop-nonnegative, and
   instantiating its pointwise margin directly at the strict term e gives
   c·(b−a)+e>0, closing by translation of shape; no Or-form
   square-nonnegativity slot and no strictness demand on c anywhere. *)
Lemma d2_scaled_le_b : forall (a b c : Real),
  real_le a b -> real_le_b real_zero c ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab HC. unfold real_le_b. intros e He.
  destruct Hab as [Hlt | Heq].
  - (* strict branch *)
    assert (Hgpos : real_lt real_zero (real_plus b (real_opp a))).
    { exact (p2_diff_pos_of_lt a b Hlt). }
    assert (HA : real_lt real_zero
                   (real_plus (real_mult c (real_plus b (real_opp a))) e)).
    { apply (RealSetoid.real_lt_id_l real_zero
               (real_mult real_zero (real_plus b (real_opp a)))
               (real_plus (real_mult c (real_plus b (real_opp a))) e)).
      - exact (real_eq_sym
                 (real_mult real_zero (real_plus b (real_opp a))) real_zero
                 (real_eq_trans
                    (real_mult real_zero (real_plus b (real_opp a)))
                    (real_mult (real_plus b (real_opp a)) real_zero)
                    real_zero
                    (real_mult_comm real_zero (real_plus b (real_opp a)))
                    (real_mult_zero (real_plus b (real_opp a))))).
      - exact (leb3_le_b_pos_scale real_zero c (real_plus b (real_opp a))
                 HC Hgpos e He). }
    assert (Heqc : real_eq (real_mult c b)
                   (real_plus (real_mult c a)
                              (real_mult c (real_plus b (real_opp a))))).
    { apply (real_eq_trans (real_mult c b)
               (real_mult c (real_plus a (real_plus b (real_opp a))))
               (real_plus (real_mult c a)
                          (real_mult c (real_plus b (real_opp a))))).
      - apply real_eq_of_zero_diff. intro n0.
        apply qeq_imp_qeqT.
        repeat match goal with [ x : Real |- _ ] => destruct x end.
        cbn [projT1 real_plus real_mult real_opp real_one real_zero].
        ring.
      - exact (real_distrib c a (real_plus b (real_opp a))). }
    apply (RealSetoid.real_lt_id_r (real_mult c a)
             (real_plus
                (real_plus (real_mult c a)
                           (real_mult c (real_plus b (real_opp a)))) e)
             (real_plus (real_mult c b) e)).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult c a)
                          (real_mult c (real_plus b (real_opp a))))
               e (real_mult c b) e).
      * exact (real_eq_sym (real_mult c b)
                 (real_plus (real_mult c a)
                            (real_mult c (real_plus b (real_opp a))))
                 Heqc).
      * apply real_eq_refl.
    + apply (RealSetoid.real_lt_id_l (real_mult c a)
               (real_plus (real_mult c a) real_zero)
               (real_plus
                  (real_plus (real_mult c a)
                             (real_mult c (real_plus b (real_opp a)))) e)).
      * exact (real_eq_sym (real_plus (real_mult c a) real_zero)
                 (real_mult c a) (real_plus_zero (real_mult c a))).
      * apply (RealSetoid.real_lt_id_r
                 (real_plus (real_mult c a) real_zero)
                 (real_plus (real_mult c a)
                            (real_plus
                               (real_mult c (real_plus b (real_opp a))) e))
                 (real_plus
                    (real_plus (real_mult c a)
                               (real_mult c (real_plus b (real_opp a)))) e)).
        -- apply real_plus_assoc.
        -- apply (real_lt_plus_translate (real_mult c a) real_zero
                     (real_plus (real_mult c (real_plus b (real_opp a))) e)).
           exact HA.
  - (* equality branch: reshape by a==b plus strict translation *)
    apply (RealSetoid.real_lt_id_l (real_mult c a) (real_mult c b)
             (real_plus (real_mult c b) e)).
    + exact (RealSetoid.real_eq_mult_compat c a c b (real_eq_refl c) Heq).
    + apply (real_lt_plus_r_zero (real_mult c b) e). exact He.
Qed.

(* piece 1b: the χ² carrier is Bishop-form nonnegative -- scale the
   square-nonnegativity finisher pointwise, then add *)
Theorem div2_cs_nonneg : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b real_zero (div2_cs p q Hq Hq1).
Proof.
  intros p q Hq Hq1.
  assert (HD : real_le_b real_zero (p2_tvsq p q)).
  { exact (real_square_nonneg_B (p2_diff p q)). }
  assert (HT1 : real_le_b real_zero
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
  { apply (leb3_le_b_eq_l (real_mult real_zero (real_inv_pos q Hq))
             real_zero (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
    - exact (real_eq_trans
               (real_mult real_zero (real_inv_pos q Hq))
               (real_mult (real_inv_pos q Hq) real_zero)
               real_zero
               (real_mult_comm real_zero (real_inv_pos q Hq))
               (real_mult_zero (real_inv_pos q Hq))).
    - apply (leb3_le_b_pos_scale real_zero (p2_tvsq p q)
               (real_inv_pos q Hq) HD (real_inv_pos_pos q Hq)). }
  assert (HT2 : real_le_b real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))).
  { apply (leb3_le_b_eq_l
             (real_mult real_zero (real_inv_pos (p2_one_minus q) Hq1))
             real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))).
    - exact (real_eq_trans
               (real_mult real_zero (real_inv_pos (p2_one_minus q) Hq1))
               (real_mult (real_inv_pos (p2_one_minus q) Hq1) real_zero)
               real_zero
               (real_mult_comm real_zero
                  (real_inv_pos (p2_one_minus q) Hq1))
               (real_mult_zero (real_inv_pos (p2_one_minus q) Hq1))).
    - apply (leb3_le_b_pos_scale real_zero (p2_tvsq p q)
               (real_inv_pos (p2_one_minus q) Hq1) HD
               (real_inv_pos_pos (p2_one_minus q) Hq1)). }
  apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero
           (div2_cs p q Hq Hq1)).
  - apply real_plus_zero.
  - exact (real_le_b_plus_compat real_zero
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
             real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))
             HT1 HT2).
Qed.

(* ---- 5. piece 1c: unconditional lower arm four·TV² ≤_B χ² ---- *)

(* this piece dissolves by pure polynomial identities (d2 constant
   unfoldings included) *)
Ltac d2_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  apply qeq_imp_qeqT;
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  cbn [projT1 p2_diff p2_one_minus p2_tvsq d2_two d2_four
       real_plus real_mult real_opp real_one real_zero];
  ring.

(* Bishop right-addition lemma: x ≤_B y with 0 ≤_B z gives x ≤_B y+z
   (real_le_b_plus_compat reshaped by right addition of zero; z is taken
   Bishop-form to allow square terms) *)
Lemma d2_le_b_add_r : forall (x y z : Real),
  real_le_b x y -> real_le_b real_zero z ->
  real_le_b x (real_plus y z).
Proof.
  intros x y z H HZ.
  apply (leb3_le_b_eq_l (real_plus x real_zero) x (real_plus y z)).
  - apply real_plus_zero.
  - exact (real_le_b_plus_compat x y real_zero z H HZ).
Qed.

(* right distributivity: (x+y)·z == x·z + y·z (comm-distrib-comm chain) *)
Lemma d2_left_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z)
          (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z.
  apply (real_eq_trans (real_mult (real_plus x y) z)
                       (real_mult z (real_plus x y))
                       (real_plus (real_mult x z) (real_mult y z))).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult z (real_plus x y))
                         (real_plus (real_mult z x) (real_mult z y))
                         (real_plus (real_mult x z) (real_mult y z))).
    + apply real_distrib.
    + apply (RealSetoid.real_eq_plus_compat (real_mult z x)
               (real_mult z y) (real_mult x z) (real_mult y z)).
      * apply real_mult_comm.
      * apply real_mult_comm.
Qed.

(* key algebraic identity: (p−q)² == (q·(1−q))·four·(p−q)²
   + ((p−q)·(two·q−one))²  (a pointwise polynomial identity, the square
   rearrangement of (two·q−one)² == one−four·q·(one−q)) *)
Lemma d2_split_core : forall p q : Real,
  real_eq (p2_tvsq p q)
          (real_plus
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_mult
                (real_mult (p2_diff p q)
                           (real_plus (real_plus q q) (real_opp real_one)))
                (real_mult (p2_diff p q)
                           (real_plus (real_plus q q)
                                      (real_opp real_one))))).
Proof.
  intros p q. d2_ring_eq.
Qed.

(* quadrupling cancellation: (qq1·four·D)·inv(qq1) == four·D
   (ring rearrangement plus right inv cancellation) *)
Lemma d2_quad_scale : forall (p q : Real)
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (real_mult
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
          (real_mult d2_four (p2_tvsq p q)).
Proof.
  intros p q Hqq1.
  apply (real_eq_trans
           (real_mult
              (real_mult
                 (real_mult (real_mult q (p2_one_minus q)) d2_four)
                 (p2_tvsq p q))
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
           (real_mult
              (real_mult (real_mult d2_four (p2_tvsq p q))
                         (real_mult q (p2_one_minus q)))
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
           (real_mult d2_four (p2_tvsq p q))).
  - apply (RealSetoid.real_eq_mult_compat
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
             (real_mult (real_mult d2_four (p2_tvsq p q))
                        (real_mult q (p2_one_minus q)))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
    + apply real_eq_of_zero_diff. intro n0.
      apply qeq_imp_qeqT.
      repeat match goal with [ x : Real |- _ ] => destruct x end.
      cbn [projT1 p2_diff p2_one_minus p2_tvsq d2_two d2_four
           real_plus real_mult real_opp real_one real_zero].
      ring.
    + apply real_eq_refl.
  - exact (d2_mult_inv_r
             (real_mult d2_four (p2_tvsq p q))
             (real_mult q (p2_one_minus q)) Hqq1).
Qed.

(* piece 1c: unconditional lower arm four·TV² ≤_B χ².
   route: the closed-form identity plus the square-rearrangement kernel
   d2_split_core ((two·q−one)² == one−four·qq1) give
   χ² == four·D + ((p−q)·(two·q−one))²·inv(qq1); the remainder is a square
   term scaled by the strictly positive inv, hence Bishop-nonnegative, and
   right addition closes; no log, no case splits, no Or-form square slot. *)
Theorem div2_cs_ge_four_tvsq : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_le_b (real_mult d2_four (p2_tvsq p q)) (div2_cs p q Hq Hq1).
Proof.
  intros p q Hq Hq1 Hqq1.
  assert (HEQ : real_eq (div2_cs p q Hq Hq1)
                   (real_plus (real_mult d2_four (p2_tvsq p q))
                              (real_mult
                                 (real_mult
                                    (real_mult (p2_diff p q)
                                               (real_plus (real_plus q q)
                                                          (real_opp real_one)))
                                    (real_mult (p2_diff p q)
                                               (real_plus (real_plus q q)
                                                          (real_opp real_one))))
                                 (real_inv_pos (real_mult q (p2_one_minus q))
                                               Hqq1)))).
  { apply (real_eq_trans (div2_cs p q Hq Hq1)
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
             (real_plus (real_mult d2_four (p2_tvsq p q))
                        (real_mult
                           (real_mult
                              (real_mult (p2_diff p q)
                                         (real_plus (real_plus q q)
                                                    (real_opp real_one)))
                              (real_mult (p2_diff p q)
                                         (real_plus (real_plus q q)
                                                    (real_opp real_one))))
                           (real_inv_pos (real_mult q (p2_one_minus q))
                                         Hqq1)))).
    - exact (div2_cs_closed p q Hq Hq1 Hqq1).
    - apply (real_eq_trans
               (real_mult (p2_tvsq p q)
                          (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult
                  (real_plus
                     (real_mult
                        (real_mult (real_mult q (p2_one_minus q)) d2_four)
                        (p2_tvsq p q))
                     (real_mult
                        (real_mult (p2_diff p q)
                                   (real_plus (real_plus q q)
                                              (real_opp real_one)))
                        (real_mult (p2_diff p q)
                                   (real_plus (real_plus q q)
                                              (real_opp real_one)))))
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_plus (real_mult d2_four (p2_tvsq p q))
                          (real_mult
                             (real_mult
                                (real_mult (p2_diff p q)
                                           (real_plus (real_plus q q)
                                                      (real_opp real_one)))
                                (real_mult (p2_diff p q)
                                           (real_plus (real_plus q q)
                                                      (real_opp real_one))))
                             (real_inv_pos (real_mult q (p2_one_minus q))
                                           Hqq1)))).
      + apply (RealSetoid.real_eq_mult_compat (p2_tvsq p q)
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                 (real_plus
                    (real_mult
                       (real_mult (real_mult q (p2_one_minus q)) d2_four)
                       (p2_tvsq p q))
                    (real_mult
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
        * apply (d2_split_core p q).
        * apply real_eq_refl.
      + apply (real_eq_trans
                 (real_mult
                    (real_plus
                       (real_mult
                          (real_mult (real_mult q (p2_one_minus q)) d2_four)
                          (p2_tvsq p q))
                       (real_mult
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))))
                    (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                 (real_plus
                    (real_mult
                       (real_mult
                          (real_mult (real_mult q (p2_one_minus q)) d2_four)
                          (p2_tvsq p q))
                       (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                    (real_mult
                       (real_mult
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one))))
                       (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)))
                 (real_plus (real_mult d2_four (p2_tvsq p q))
                            (real_mult
                               (real_mult
                                  (real_mult (p2_diff p q)
                                             (real_plus (real_plus q q)
                                                        (real_opp real_one)))
                                  (real_mult (p2_diff p q)
                                             (real_plus (real_plus q q)
                                                        (real_opp real_one))))
                               (real_inv_pos (real_mult q (p2_one_minus q))
                                             Hqq1)))).
        * exact (d2_left_distrib_r
                   (real_mult
                      (real_mult (real_mult q (p2_one_minus q)) d2_four)
                      (p2_tvsq p q))
                   (real_mult
                      (real_mult (p2_diff p q)
                                 (real_plus (real_plus q q)
                                            (real_opp real_one)))
                      (real_mult (p2_diff p q)
                                 (real_plus (real_plus q q)
                                            (real_opp real_one))))
                   (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult
                      (real_mult
                         (real_mult (real_mult q (p2_one_minus q)) d2_four)
                         (p2_tvsq p q))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                   (real_mult
                      (real_mult
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one)))
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one))))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                   (real_mult d2_four (p2_tvsq p q))
                   (real_mult
                      (real_mult
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one)))
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one))))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
          -- exact (d2_quad_scale p q Hqq1).
          -- apply real_eq_refl. }
  assert (HR : real_le_b real_zero
                 (real_mult
                    (real_mult
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one))))
                    (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
  { apply (leb3_le_b_eq_l
             (real_mult real_zero
                (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
             real_zero
             (real_mult
                (real_mult
                   (real_mult (p2_diff p q)
                              (real_plus (real_plus q q)
                                         (real_opp real_one)))
                   (real_mult (p2_diff p q)
                              (real_plus (real_plus q q)
                                         (real_opp real_one))))
                (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
    - exact (real_eq_trans
               (real_mult real_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                          real_zero)
               real_zero
               (real_mult_comm real_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
    - exact (leb3_le_b_pos_scale real_zero
                 (real_mult
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one)))
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                 (real_square_nonneg_B
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos_pos (real_mult q (p2_one_minus q)) Hqq1)). }
  exact (leb3_le_b_eq_r (real_mult d2_four (p2_tvsq p q))
           (real_plus (real_mult d2_four (p2_tvsq p q))
                      (real_mult
                         (real_mult
                            (real_mult (p2_diff p q)
                                       (real_plus (real_plus q q)
                                                  (real_opp real_one)))
                            (real_mult (p2_diff p q)
                                       (real_plus (real_plus q q)
                                                  (real_opp real_one))))
                         (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)))
           (div2_cs p q Hq Hq1)
           (d2_le_b_add_r (real_mult d2_four (p2_tvsq p q))
              (real_mult d2_four (p2_tvsq p q))
              (real_mult
                 (real_mult
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one)))
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
              (leb3_le_b_refl (real_mult d2_four (p2_tvsq p q))) HR)
           (real_eq_sym (div2_cs p q Hq Hq1)
              (real_plus (real_mult d2_four (p2_tvsq p q))
                         (real_mult
                            (real_mult
                               (real_mult (p2_diff p q)
                                          (real_plus (real_plus q q)
                                                     (real_opp real_one)))
                               (real_mult (p2_diff p q)
                                          (real_plus (real_plus q q)
                                                     (real_opp real_one))))
                            (real_inv_pos (real_mult q (p2_one_minus q))
                                          Hqq1)))
              HEQ)).
Qed.

(* ---- 6. piece 1d: conditional upper arm χ² ≤_B two·TV²/m ---- *)

(* inv antitone (Or-form le exit): 0<a, 0<b and a≤b give inv(b) ≤ inv(a).
   strict branch takes the in-service inv antitone lemma; equality branch
   closes by real_inv_unique with b as common multiplier. *)
Lemma d2_inv_antitone_le : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_inv_pos b Hb) (real_inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab. unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - left. exact (real_inv_pos_lt_contra a b Ha Hb Hlt).
  - right.
    apply (real_inv_unique b (real_inv_pos b Hb) (real_inv_pos a Ha)).
    + apply real_inv_pos_correct.
    + apply (real_eq_trans (real_mult b (real_inv_pos a Ha))
                           (real_mult a (real_inv_pos a Ha))
                           real_one).
      * exact (RealSetoid.real_eq_mult_compat b (real_inv_pos a Ha) a
                 (real_inv_pos a Ha)
                 (real_eq_sym a b Heq) (real_eq_refl (real_inv_pos a Ha))).
      * exact (real_inv_pos_correct a Ha).
Qed.

(* piece 1d: conditional upper arm m≤q ∧ m≤(1−q) ∧ 0<m give
   χ² ≤_B two·TV²/m.  route: both branches of the inv antitone lemma plus
   pointwise closure by the Bishop scaling lemma, then addition; the right
   side reshapes to two·(D·inv m) by the doubling identity; no log, no case
   splits, no Or-form square slot. *)
Theorem div2_cs_le_tvsq_over_m : forall (p q m : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hm : real_lt real_zero m)
  (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q)),
  real_le_b (div2_cs p q Hq Hq1)
            (real_mult d2_two
               (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
Proof.
  intros p q m Hq Hq1 Hm Hmq Hmq1.
  assert (HC : real_le_b real_zero (p2_tvsq p q)).
  { exact (real_square_nonneg_B (p2_diff p q)). }
  assert (Hleq : real_le (real_inv_pos q Hq) (real_inv_pos m Hm)).
  { exact (d2_inv_antitone_le m q Hm Hq Hmq). }
  assert (Hleq1 : real_le (real_inv_pos (p2_one_minus q) Hq1)
                          (real_inv_pos m Hm)).
  { exact (d2_inv_antitone_le m (p2_one_minus q) Hm Hq1 Hmq1). }
  assert (T1 : real_le_b
                 (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                 (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
  { exact (d2_scaled_le_b (real_inv_pos q Hq) (real_inv_pos m Hm)
             (p2_tvsq p q) Hleq HC). }
  assert (T2 : real_le_b
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos (p2_one_minus q) Hq1))
                 (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
  { exact (d2_scaled_le_b (real_inv_pos (p2_one_minus q) Hq1)
             (real_inv_pos m Hm) (p2_tvsq p q) Hleq1 HC). }
  apply (leb3_le_b_eq_l
           (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                      (real_mult (p2_tvsq p q)
                                 (real_inv_pos (p2_one_minus q) Hq1)))
           (div2_cs p q Hq Hq1)
           (real_mult d2_two
              (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).
  - apply real_eq_refl.
  - exact (leb3_le_b_eq_r
             (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                        (real_mult (p2_tvsq p q)
                                   (real_inv_pos (p2_one_minus q) Hq1)))
             (real_plus (real_mult (p2_tvsq p q) (real_inv_pos m Hm))
                        (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))
             (real_mult d2_two
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))
             (real_le_b_plus_compat
                (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm))
                (real_mult (p2_tvsq p q)
                           (real_inv_pos (p2_one_minus q) Hq1))
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm)) T1 T2)
             (d2_double (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).
Qed.

(* ---- 7. Q-layer closed-form slot (piece 1e, first stage: identity and
   nonnegativity, no analytic layer) ---- *)

(* Q-layer χ² closed form: (p−q)²·inv(q·(1−q)) -- a pure rational
   expression, no log, no limits *)
Definition cs2q (p q : Q) : Q := (p - q) * (p - q) * / (q * (1 - q)).

(* piece 1e-i: Q-layer termwise closed-form identity
   cs2q == (p−q)²·inv(q) + (p−q)²·inv(1−q)
   (one field-solver step; the nonzero-denominator certificates carried
   explicitly alongside) *)
Theorem cs2q_split : forall p q : Q,
  (q == 0 -> False) -> ((1 - q)%Q == 0 -> False) ->
  cs2q p q == (p - q) * (p - q) * (/ q)
            + (p - q) * (p - q) * (/ (1 - q))%Q.
Proof.
  intros p q Hq Hq1. unfold cs2q.
  field.
  split.
  - exact Hq1.
  - exact Hq.
Qed.

(* piece 1e-ii: Q-layer nonnegativity -- squares are nonnegative and
   scaling by a positive inv preserves the order, combined directly *)
Theorem cs2q_nonneg : forall p q : Q,
  Qlt 0 (q * (1 - q)) -> Qle 0 (cs2q p q).
Proof.
  intros p q Hmass. unfold cs2q.
  apply Qmult_le_0_compat.
  - exact (QleT'_to_Qle _ _ (Qsquare_nonneg (p - q))).
  - exact (Qlt_le_weak _ _ (Qinv_lt_0_compat (q * (1 - q)) Hmass)).
Qed.

(* ---- 99. tail checks ---- *)
Print Assumptions div2_cs_closed.
Print Assumptions div2_cs_nonneg.
Print Assumptions div2_cs_ge_four_tvsq.
Print Assumptions div2_cs_le_tvsq_over_m.
Print Assumptions cs2q_split.
Print Assumptions cs2q_nonneg.
