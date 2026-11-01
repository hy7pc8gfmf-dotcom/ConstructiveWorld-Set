(* ConstructiveWorld-Set -- gcl_famsym: symmetrized truncation family Fam-slot supply piece (constructive, Set-carried). *)
(** * gcl_famsym: symmetrized truncation family with premise-free slot closure.
    Mission.  Inherit the group-structure coefficient layer: gcl_coefficient's
    named slot gcl_sep_generic takes a family fam under two premises
    (nonnegativity, and fam m <= (1/4) * (1/12)^m).  This file forges the
    symmetrized truncation family -- the T-denominator truncation family of
    the V4 orbit average -- and discharges both premises by machine proof,
    reaching the premise-free closure gcl_famseq_sep.
    Mathematics.  Family carrier (Set-carried; Defined, hence extractable):
    gcl_famv m M x y = (1/2) * [T^(m+2) * F(x,y) + Tbar^(m+2) * F(1-x,1-y)],
    F the pointwise evaluation of the zb2 segment list, T = 1 - x*y and
    Tbar = x + y - x*y (the two orbit points of the DIG double-shape sup
    certificate); the A-side closed form gives gcl_famv <= N^(m+1) with
    N = x * (1-x) * y * (1-y); decay runs through gcl_avg_cert,
    12N <= Tavg <= 1, so N^(m+1) <= (1/4) * (1/12)^m = gcl_weight_G m; the
    named sequence gcl_famseq m = gcl_famv m m (1/2,1/2) (tau fixed-point
    anchor) is strictly positive, so the separation d^2 * gcl_famseq m < 1
    holds without premises.
    Dependencies.  Stdlib QArith/ZArith/Arith/Lia/Setoid; S01_BaseRing,
    S02_CauchyComplete, S03_QExp, BeukersLists; abl_z2_truncfam,
    abl_z2_itg_carrier, abl_dmw2_pointwise_sharp, dig_machine, gcl_coefficient
    (gcl_sep_generic, gcl_avg_cert, gcl_weight_G, gcl_copl_invol_x).
    References.  Rhin-Viola group-structure permutation method for zeta(2)
    (double-integral method core), symmetrized truncation layer.
    Constructivity.  All statements Set-carried; Print Assumptions closed
    under the global context throughout; Separate Extraction with Obj.magic
    count 0; no real numbers, no classical logic, nothing left open.
    Build.  [rocq c -native-compiler no -q -Q . "" gcl_famsym.v] on Rocq
    9.1.0 (-Q root holds the S01/S02 .vo). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier abl_dmw2_pointwise_sharp dig_machine.
Require Import gcl_coefficient.

Open Scope Q_scope.

(* Implementation note.  QltT is the bool wrapper Id (Qlt_bool ...) true; under
   this wrapper there is no setoid-rewrite lifting instance for Qlt_bool, so
   every Qlt / QltT layer is handled rewrite-free: cbn [q_pow] iota reduction,
   literal lia goals, and Qlt_le_trans chains.  Rewriting stays on the bare
   Q / Qle / QleT' faces. *)

(* ============================================================ *)
(* Sec 0. Q power and order toolkit: positivity, monotonicity, contraction bound, Tavg square faces, swap faces *)
(* ============================================================ *)

(* Power strict positivity: 0 < a implies 0 < a^k (Qlt layer; rewrite-free; cbn iota direct reduction) *)
Lemma gcl_q_pow_pos : forall (a : Q) (k : nat),
  QltT 0 a -> QltT 0 (q_pow a k).
Proof.
  intros a k H. pose proof (QltT_to_Qlt _ _ H) as Hq.
  induction k as [| k IH].
  - cbn [q_pow]. apply Qlt_to_QltT. unfold Qlt; cbn [Qnum Qden]; lia.
  - cbn [q_pow]. pose proof (QltT_to_Qlt _ _ IH) as IHq.
    apply Qlt_to_QltT. apply Qmult_lt_0_compat; assumption.
Qed.

(* Power monotonicity: 0 <= a <= b implies a^k <= b^k *)
Lemma gcl_q_pow_mono : forall (a b : Q) (k : nat),
  QleT' 0 a -> QleT' a b -> QleT' (q_pow a k) (q_pow b k).
Proof.
  intros a b k Ha Hab.
  pose proof (QleT'_to_Qle _ _ Ha) as Haq.
  pose proof (QleT'_to_Qle _ _ Hab) as Habq.
  apply Qle_to_QleT'.
  induction k as [| k IH].
  - cbn [q_pow]. apply Qle_refl.
  - cbn [q_pow].
    assert (Hb : 0 <= b) by (apply (Qle_trans 0 a b); assumption).
    assert (Hpa : 0 <= q_pow a k) by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact Haq).
    apply (Qle_trans _ (b * q_pow a k)).
    + apply (Qmult_le_compat_r a b (q_pow a k) Habq Hpa).
    + assert (H2 : q_pow a k * b <= q_pow b k * b)
        by (apply (Qmult_le_compat_r (q_pow a k) (q_pow b k) b IH Hb)).
      assert (Hc1 : b * q_pow a k == q_pow a k * b) by ring.
      assert (Hc2 : b * q_pow b k == q_pow b k * b) by ring.
      rewrite Hc1, Hc2. exact H2.
Qed.

(* Contraction bound: 0 <= u <= 1 and 0 <= a imply (a * u)^k <= a^k *)
Lemma gcl_q_pow_scale_le : forall (u a : Q) (k : nat),
  QleT' 0 u -> QleT' u 1 -> QleT' 0 a -> QleT' (q_pow (a * u) k) (q_pow a k).
Proof.
  intros u a k Hu Hua Ha.
  pose proof (QleT'_to_Qle _ _ Hu) as Huq.
  pose proof (QleT'_to_Qle _ _ Hua) as Huaq.
  pose proof (QleT'_to_Qle _ _ Ha) as Haq.
  apply Qle_to_QleT'.
  induction k as [| k IH].
  - cbn [q_pow]. apply Qle_refl.
  - cbn [q_pow].
    assert (Hp0 : 0 <= q_pow (a * u) k)
      by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT';
          apply Qmult_le_0_compat; assumption).
    apply (Qle_trans _ (a * q_pow (a * u) k)).
    + apply (Qmult_le_compat_r (a * u) a (q_pow (a * u) k)).
      * assert (Hau0 : u * a <= 1 * a) by (apply (Qmult_le_compat_r u 1 a Huaq Haq)).
        assert (Hau : a * u <= a).
        { assert (E1 : a * u == u * a) by ring. rewrite E1.
          assert (E2 : 1 * a == a) by ring. rewrite E2 in Hau0.
          exact Hau0. }
        exact Hau.
      * exact Hp0.
    + assert (H2 : q_pow (a * u) k * a <= q_pow a k * a)
        by (apply (Qmult_le_compat_r (q_pow (a * u) k) (q_pow a k) a IH Haq)).
      assert (Hc1 : a * q_pow (a * u) k == q_pow (a * u) k * a) by ring.
      assert (Hc2 : a * q_pow a k == q_pow a k * a) by ring.
      rewrite Hc1, Hc2. exact H2.
Qed.

(* Swap faces: 0 <= x implies 1 - x <= 1; x <= 1 implies 0 <= 1 - x (Gco generators preserve the square) *)
Lemma gcl_le1_swap : forall x : Q, QleT' 0 x -> QleT' (1 - x) 1.
Proof.
  intros x H.
  apply (dmw2_sub_ge0 (1 - x) 1).
  rewrite gcl_copl_invol_x. apply QleT'_to_Qle. exact H.
Qed.

Lemma gcl_ge0_swap : forall x : Q, QleT' x 1 -> QleT' 0 (1 - x).
Proof.
  intros x H.
  apply (dmw2_le_sub x 1). apply QleT'_to_Qle. exact H.
Qed.

(* Bare Qle reshaping bridge: x == y and z <= x imply z <= y (crossing without rewrite) *)
Lemma gcl_qle_wd : forall x y z : Q, QeqT x y -> QleT' z x -> QleT' z y.
Proof.
  intros x y z Hxy Hz. apply Qle_to_QleT'.
  apply (Qle_trans z x y).
  - exact (QleT'_to_Qle _ _ Hz).
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ Hxy)).
Qed.

(* Tavg nonnegative: 1 + x + y - 2*x*y = 1 + x * (1 - y) + y * (1 - x) >= 0 on the square *)
Lemma gcl_Tavg_ge0 : forall x y : Q,
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 -> QleT' 0 (gcl_Tavg x y).
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hx2) as Hx2q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  pose proof (QleT'_to_Qle _ _ Hy2) as Hy2q.
  apply Qle_to_QleT'. unfold gcl_Tavg.
  assert (E : 1 + x + y - 2 * x * y == 1 + x * (1 - y) + y * (1 - x)) by ring.
  rewrite E.
  assert (HA : 0 <= x * (1 - y)).
  { apply Qmult_le_0_compat.
    - exact Hx1q.
    - apply QleT'_to_Qle. apply (dmw2_le_sub y 1). exact Hy2q. }
  assert (HB : 0 <= y * (1 - x)).
  { apply Qmult_le_0_compat.
    - exact Hy1q.
    - apply QleT'_to_Qle. apply (dmw2_le_sub x 1). exact Hx2q. }
  assert (Ec : (1#2) * (1 + x * (1 - y) + y * (1 - x))
            == (1 + x * (1 - y) + y * (1 - x)) * (1#2)) by ring.
  rewrite Ec.
  assert (H1' : 1 <= 1 + x * (1 - y) + y * (1 - x)).
  { assert (E4 : 1 + x * (1 - y) + y * (1 - x)
              == 1 + (x * (1 - y) + y * (1 - x))) by ring.
    rewrite E4.
    apply QleT'_to_Qle.
    apply (dmw2_add_ge0_le 1 (x * (1 - y) + y * (1 - x))).
    apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
    - exact HA.
    - apply QleT'_to_Qle. apply (dmw2_add_ge0_le (x * (1 - y)) (y * (1 - x))). exact HB. }
  apply Qmult_le_0_compat.
  - apply (Qle_trans 0 1 (1 + x * (1 - y) + y * (1 - x))).
    + unfold Qle. simpl. lia.
    + exact H1'.
  - unfold Qle. simpl. lia.
Qed.

(* Tavg <= 1: 1 - Tavg = ((1 - x) * (1 - y) + x * y) / 2 >= 0 *)
Lemma gcl_Tavg_le_1 : forall x y : Q,
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 -> QleT' (gcl_Tavg x y) 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  unfold gcl_Tavg.
  apply (dmw2_sub_ge0 (gcl_Tavg x y) 1).
  assert (E : 1 - (1#2) * (1 + x + y - 2 * x * y)
           == ((1 - x) * (1 - y) + x * y) * (1#2)) by ring.
  rewrite E. apply Qmult_le_0_compat.
  - apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
    + apply Qmult_le_0_compat.
      * apply QleT'_to_Qle. apply (gcl_ge0_swap x Hx2).
      * apply QleT'_to_Qle. apply (gcl_ge0_swap y Hy2).
    + apply QleT'_to_Qle. apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)).
      apply Qmult_le_0_compat; assumption.
  - unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* Sec 1. Segment-list evaluation order face: partial-sum order faces and anchor strict positivity *)
(* ============================================================ *)

(* Partial sums nonnegative: termwise C(n+k, n) * t^k >= 0 (0 <= t) *)
Lemma gcl_ps_ge0 : forall n M t, QleT' 0 t -> QleT' 0 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply (zb2_qleT'_wd_r 1 (zb2_ps n 0 t) 0).
    + apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (zb2_ps_zero n t))).
    + apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply (zb2_qleT'_wd_r (zb2_ps n M t
                             + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                               * q_pow t (Datatypes.S M))
                          (zb2_ps n (Datatypes.S M) t) 0).
    + apply (Qeq_sym _ _ (zb2_ps_unfold n M t)).
    + apply Qle_to_QleT'.
      assert (Hterm : 0 <= (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                           * q_pow t (Datatypes.S M)).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        - apply QleT'_to_Qle. apply q_pow_nonneg. exact Ht. }
      apply (Qle_trans 0 (zb2_ps n M t)
               (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                                * q_pow t (Datatypes.S M))).
      * apply QleT'_to_Qle. exact IH.
      * apply QleT'_to_Qle. apply (dmw2_add_ge0_le _ _ Hterm).
Qed.

(* Partial sums bounded below by 1: leading term C(n, n) = 1 (0 <= t keeps every tail term nonnegative) *)
Lemma gcl_ps_ge1 : forall n M t, QleT' 0 t -> QleT' 1 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply (zb2_qleT'_wd_r 1 (zb2_ps n 0 t) 1).
    + apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ (zb2_ps_zero n t))).
    + apply Qle_to_QleT'. apply Qle_refl.
  - apply (zb2_qleT'_wd_r (zb2_ps n M t
                             + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                               * q_pow t (Datatypes.S M))
                          (zb2_ps n (Datatypes.S M) t) 1).
    + apply (Qeq_sym _ _ (zb2_ps_unfold n M t)).
    + apply Qle_to_QleT'.
      assert (Htail : 0 <= (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                        * q_pow t (Datatypes.S M)).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        - apply QleT'_to_Qle. apply q_pow_nonneg. exact Ht. }
      pose proof (QleT'_to_Qle _ _ IH) as IHq.
      apply (Qle_trans 1 (zb2_ps n M t)
               (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                                * q_pow t (Datatypes.S M))).
      * exact IHq.
      * apply QleT'_to_Qle. apply (dmw2_add_ge0_le _ _ Htail).
Qed.

(* Segment-list evaluation nonnegative: Nx^n * Ny^n * ps >= 0 on the whole square *)
Lemma gcl_beval_seg_ge0 : forall n M x y,
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 ->
  QleT' 0 (zb2_beval_l (zb2_segl n M) x y).
Proof.
  intros n M x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hx2) as Hx2q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  pose proof (QleT'_to_Qle _ _ Hy2) as Hy2q.
  pose proof (zb2_beval_segl n M x y) as Hseg.
  apply (gcl_qle_wd _ _ 0 (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hseg)))).
  assert (Hxb : 0 <= 1 - x)
    by (apply QleT'_to_Qle; exact (gcl_ge0_swap x Hx2)).
  assert (Hyb : 0 <= 1 - y)
    by (apply QleT'_to_Qle; exact (gcl_ge0_swap y Hy2)).
  assert (HNx : 0 <= x * (1 - x)) by (apply Qmult_le_0_compat; assumption).
  assert (HNy : 0 <= y * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact HNx.
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact HNy.
  - apply QleT'_to_Qle. apply gcl_ps_ge0. apply Qle_to_QleT'. exact Hxy0.
Qed.

(* Anchor segment-list evaluation lower bound: F(1/2, 1/2) >= ((1/4) * (1/4))^n = (1/16)^n *)
Lemma gcl_beval_seg_anchor_ge : forall n M,
  QleT' (q_pow ((1#4)*(1#4)) n) (zb2_beval_l (zb2_segl n M) (1#2) (1#2)).
Proof.
  intros n M.
  assert (Hq2 : (1#2)*(1#2) == (1#4)) by reflexivity.
  assert (Ht4 : 0 <= (1#2)*(1#2)) by (rewrite Hq2; unfold Qle; cbn [Qnum Qden]; lia).
  pose proof (QleT'_to_Qle _ _
                (gcl_ps_ge1 n M ((1#2)*(1#2)) (Qle_to_QleT' _ _ Ht4))) as HP.
  assert (Hps0 : 0 <= zb2_ps n M ((1#2)*(1#2))).
  { apply (Qle_trans 0 1 _).
    - unfold Qle. simpl. lia.
    - exact HP. }
  pose proof (zb2_beval_segl n M (1#2) (1#2)) as Hseg.
  apply (gcl_qle_wd _ (zb2_beval_l (zb2_segl n M) (1#2) (1#2))
           (q_pow ((1#4)*(1#4)) n) (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hseg)))).
  apply Qle_to_QleT'.
  assert (Hr1 : q_pow ((1#4)*(1#4)) n == q_pow ((1#4)*(1#4)) n * 1) by ring.
  apply (Qle_trans _ (q_pow ((1#4)*(1#4)) n * 1)).
  - apply QleT'_to_Qle.
    apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n) (q_pow ((1#4)*(1#4)) n * 1)
                      (q_pow ((1#4)*(1#4)) n) (qeq_imp_qeqT _ _ Hr1)).
    apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hq : (1#2) * (1 - (1#2)) == (1#4)) by reflexivity.
    rewrite Hq.
    assert (HX4 : 0 <= q_pow (1#4) n)
      by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; unfold Qle; simpl; lia).
    assert (HXX0 : 0 <= q_pow (1#4) n * q_pow (1#4) n)
      by (apply Qmult_le_0_compat; exact HX4).
    assert (Ht2 : 1 * (q_pow (1#4) n * q_pow (1#4) n)
               <= zb2_ps n M ((1#2)*(1#2)) * (q_pow (1#4) n * q_pow (1#4) n))
      by (apply (Qmult_le_compat_r 1 (zb2_ps n M ((1#2)*(1#2)))
                   (q_pow (1#4) n * q_pow (1#4) n))
           ; [ exact HP | exact HXX0 ]).
    assert (E5 : 1 * (q_pow (1#4) n * q_pow (1#4) n)
              == q_pow (1#4) n * q_pow (1#4) n * 1) by ring.
    assert (E6 : zb2_ps n M ((1#2)*(1#2)) * (q_pow (1#4) n * q_pow (1#4) n)
              == q_pow (1#4) n * q_pow (1#4) n * zb2_ps n M ((1#2)*(1#2))) by ring.
    rewrite E5, E6 in Ht2.
    assert (Hle1 : q_pow ((1#4)*(1#4)) n * 1 <= q_pow ((1#4)*(1#4)) n).
    { apply QleT'_to_Qle.
      apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n * 1)
                        (q_pow ((1#4)*(1#4)) n)
                        (q_pow ((1#4)*(1#4)) n * 1)
             (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hr1))).
      apply Qle_to_QleT'. apply Qle_refl. }
    assert (Hax : q_pow ((1#4)*(1#4)) n
               == q_pow (1#4) n * q_pow (1#4) n * 1).
    { pose proof (zb2_q_pow_mul (1#4) (1#4) n) as Hpm.
      rewrite (qeqT_imp_qeq _ _ Hpm). ring. }
    apply (Qle_trans _ (q_pow (1#4) n * q_pow (1#4) n * 1)).
    + apply QleT'_to_Qle.
      apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n)
                        (q_pow (1#4) n * q_pow (1#4) n * 1)
                        (q_pow ((1#4)*(1#4)) n * 1)
             (qeq_imp_qeqT _ _ Hax) (Qle_to_QleT' _ _ Hle1)).
    + exact Ht2.
Qed.

(* Anchor segment-list evaluation strictly positive: F(1/2, 1/2) > 0 *)
Lemma gcl_beval_seg_anchor_pos : forall n M,
  QltT 0 (zb2_beval_l (zb2_segl n M) (1#2) (1#2)).
Proof.
  intros n M.
  assert (Hpos : Qlt 0 (q_pow ((1#4)*(1#4)) n))
    by (apply QltT_to_Qlt; apply gcl_q_pow_pos; apply Qlt_to_QltT;
        unfold Qlt; cbn [Qnum Qden Qmult Pos.mul]; lia).
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (q_pow ((1#4)*(1#4)) n)).
  - exact Hpos.
  - apply QleT'_to_Qle. apply gcl_beval_seg_anchor_ge.
Qed.

(* ============================================================ *)
(* Sec 2. A-side closed form: the two orbit representatives of the truncation master identity (the T slot and the Tbar slot) *)
(* ============================================================ *)

(* Main representative: T^(m+2) * F(x, y) <= N^(m+1) (zb2_ps_bound at t = x*y) *)
Lemma gcl_famv_A : forall (m M : nat) (x y : Q),
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 ->
  QleT' (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
    (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hx2) as Hx2q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  pose proof (QleT'_to_Qle _ _ Hy2) as Hy2q.
  apply Qle_to_QleT'.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; exact (gcl_ge0_swap x Hx2)).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; exact (gcl_ge0_swap y Hy2)).
  rewrite (qeqT_imp_qeq _ _ (zb2_beval_segl (Datatypes.S m) M x y)).
  assert (HN : x*(1-x)*y*(1-y) == (x*(1-x))*(y*(1-y))) by ring.
  rewrite HN.
  rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul (x*(1-x)) (y*(1-y)) (Datatypes.S m))).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x*y)
        (conj (Qmult_le_0_compat x y Hx1q Hy1q)
              (QleT'_to_Qle _ _ (dmw2_xy_le_1 x y Hx1q Hx2q Hy1q Hy2q)))) as Hps.
  pose proof (QleT'_to_Qle _ _ Hps) as Hpsq.
  assert (HN0 : 0 <= q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)).
  { apply QleT'_to_Qle.
    apply q_pow_nonneg.
    assert (HNn : 0 <= x*(1-x)*y*(1-y))
      by (apply QleT'_to_Qle; apply (dmw2_mult4_ge0 x (1-x) y (1-y)); assumption).
    apply (gcl_qle_wd (x*(1-x)*y*(1-y)) ((x*(1-x))*(y*(1-y))) 0
                      (qeq_imp_qeqT _ _ HN)).
    apply Qle_to_QleT'. exact HNn. }
  assert (E : q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                * (q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
                   * zb2_ps (Datatypes.S m) M (x*y))
           == (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                * zb2_ps (Datatypes.S m) M (x*y))
              * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)) by ring.
  rewrite E.
  apply (Qle_trans _ (1 * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))).
  - apply (Qmult_le_compat_r (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                                * zb2_ps (Datatypes.S m) M (x*y))
                             1
                             (q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))
                          Hpsq HN0).
  - assert (H1 : 1 * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
              == q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)) by ring.
    rewrite H1. apply Qle_refl.
Qed.

(* Conjugate representative: Tbar^(m+2) * F(1-x, 1-y) <= N^(m+1) (the main representative instantiated at (1-x, 1-y)) *)
Lemma gcl_famv_A_copl : forall (m M : nat) (x y : Q),
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 ->
  QleT' (q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
    * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
    (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hx' : QleT' 0 (1 - x)) by (apply (gcl_ge0_swap x Hx2)).
  assert (Hx'1 : QleT' (1 - x) 1) by (apply (gcl_le1_swap x Hx1)).
  assert (Hy' : QleT' 0 (1 - y)) by (apply (gcl_ge0_swap y Hy2)).
  assert (Hy'1 : QleT' (1 - y) 1) by (apply (gcl_le1_swap y Hy1)).
  pose proof (gcl_famv_A m M (1-x) (1-y) Hx' Hx'1 Hy' Hy'1) as H.
  pose proof (QleT'_to_Qle _ _ H) as Hq.
  assert (E2 : q_pow ((1-x)*(1-(1-x))*(1-y)*(1-(1-y))) (Datatypes.S m)
            == q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))
    by (apply qeqT_imp_qeq, q_pow_wd, qeq_imp_qeqT; ring).
  rewrite E2 in Hq.
  assert (E3 : q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
            == q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
    by (apply qeqT_imp_qeq, q_pow_wd, qeq_imp_qeqT; ring).
  rewrite E3 in Hq. apply Qle_to_QleT'. exact Hq.
Qed.

(* ============================================================ *)
(* Sec 3. Family definition and family-bound main theorem (slot premise II) *)
(* ============================================================ *)

(* Symmetrized truncation family carrier (Set-carried; Defined, hence
   extractable): the T-denominator truncation family instance of the V4 orbit
   average (the two Gsw orbit points coinciding). *)
Definition gcl_famv (m M : nat) (x y : Q) : Q :=
  (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
             * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
           + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
             * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y)).

(* Named instance sequence: the tau-fixed-point anchor slot (1/2, 1/2) (the Fam
   supply form of gcl_sep_generic).  Honesty boundary: gcl_famseq is the
   family's instance-value sequence at the tau fixed point; the family integral
   value sequence (Isum^sym) and the denominator-chain assembly are not in this
   file -- mu_lib records the pointwise and anchor-shaped instances. *)
Definition gcl_famseq (m : nat) : Q := gcl_famv m m (1#2) (1#2).

(* Family-bound main theorem: gcl_famv <= (1/4) * (1/12)^m on the whole square.
   Chain: the mean <= N^(m+1) (A-side two representatives) <= (1/12)^(m+1)
   (12N <= Tavg, Tavg <= 1) <= (1/4) * (1/12)^m. *)
Theorem gcl_famv_le_weight : forall (m M : nat) (x y : Q),
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 ->
  QleT' (gcl_famv m M x y) (gcl_weight_G m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hx2) as Hx2q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  pose proof (QleT'_to_Qle _ _ Hy2) as Hy2q.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; exact (gcl_ge0_swap x Hx2)).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; exact (gcl_ge0_swap y Hy2)).
  unfold gcl_famv.
  pose proof (gcl_famv_A m M x y Hx1 Hx2 Hy1 Hy2) as HA.
  pose proof (QleT'_to_Qle _ _ HA) as HAq.
  pose proof (gcl_famv_A_copl m M x y Hx1 Hx2 Hy1 Hy2) as HB.
  pose proof (QleT'_to_Qle _ _ HB) as HBq.
(* the mean <= N^(m+1) *)
  assert (Havg : (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                              * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                            + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                              * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
              <= q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)).
  { apply (Qle_trans _
             ((1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                       + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)))).
    - assert (H2 : (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                         * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                       + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                         * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                     * (1#2)
                  <= (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                      + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) * (1#2))
        by (apply (Qmult_le_compat_r
                     (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                        * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                      + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                        * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                     (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                      + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) (1#2))
          ; [ apply Qplus_le_compat; assumption | unfold Qle; simpl; lia ]).
      assert (Hc1 : (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                                * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                              + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                                * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                 == (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                       * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                       * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                      * (1#2)) by ring.
      assert (Hc2 : (1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                             + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
                 == (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                     + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) * (1#2)) by ring.
      rewrite Hc1, Hc2. exact H2.
    - assert (Hr : (1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                            + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
              == q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) by ring.
      rewrite Hr. apply Qle_refl. }
(* decay side: 12N <= Tavg implies N <= Tavg * (1/12) *)
  pose proof (gcl_avg_cert x y (conj Hx1q Hx2q) (conj Hy1q Hy2q)) as Hcert.
  assert (Hcert' : QleT' (12 * (x*(1-x)*y*(1-y))) (gcl_Tavg x y)).
  { pose proof (QleT'_to_Qle _ _ Hcert) as HCq.
    assert (E0 : 12 * x * (1 - x) * y * (1 - y) == 12 * (x*(1-x)*y*(1-y))) by ring.
    rewrite E0 in HCq.
    apply Qle_to_QleT'. exact HCq. }
  pose proof (QleT'_to_Qle _ _ Hcert') as Hcq.
  assert (HNle : x*(1-x)*y*(1-y) <= gcl_Tavg x y * (1#12)).
  { pose proof (Qmult_le_compat_r (12 * (x*(1-x)*y*(1-y))) (gcl_Tavg x y) (1#12)
                  Hcq ltac:(unfold Qle; simpl; lia)) as Hm.
    assert (E : (12 * (x*(1-x)*y*(1-y))) * (1#12) == x*(1-x)*y*(1-y)) by ring.
    rewrite E in Hm. exact Hm. }
(* power chain: N^(m+1) <= ((1/12) * Tavg)^(m+1) <= (1/12)^(m+1) = (1/12) * (1/12)^m *)
  assert (Ern : gcl_Tavg x y * (1#12) == (1#12) * gcl_Tavg x y) by ring.
  rewrite Ern in HNle.
  assert (Hpow : q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
              <= (1#12) * q_pow (1#12) m).
  { apply (Qle_trans _ (q_pow ((1#12) * gcl_Tavg x y) (Datatypes.S m))).
    - apply QleT'_to_Qle. apply gcl_q_pow_mono.
      + apply (dmw2_mult4_ge0 x (1-x) y (1-y)); assumption.
      + apply Qle_to_QleT'. exact HNle.
    - apply (Qle_trans _ (q_pow (1#12) (Datatypes.S m))).
      + apply QleT'_to_Qle. apply gcl_q_pow_scale_le.
        * apply gcl_Tavg_ge0; assumption.
        * apply gcl_Tavg_le_1; assumption.
        * apply Qle_to_QleT'. unfold Qle. simpl. lia.
      + rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1#12) m)). apply Qle_refl. }
  unfold gcl_weight_G. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))).
  - exact Havg.
  - apply (Qle_trans _ ((1#12) * q_pow (1#12) m)).
    + exact Hpow.
    + apply Qmult_le_compat_r.
      * unfold Qle. simpl. lia.
      * apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* Slot premise I: the family is nonnegative *)
Theorem gcl_famv_ge0 : forall (m M : nat) (x y : Q),
  QleT' 0 x -> QleT' x 1 -> QleT' 0 y -> QleT' y 1 ->
  QleT' 0 (gcl_famv m M x y).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  pose proof (QleT'_to_Qle _ _ Hx1) as Hx1q.
  pose proof (QleT'_to_Qle _ _ Hx2) as Hx2q.
  pose proof (QleT'_to_Qle _ _ Hy1) as Hy1q.
  pose proof (QleT'_to_Qle _ _ Hy2) as Hy2q.
  unfold gcl_famv.
  apply Qle_to_QleT'.
  assert (HA0 : 0 <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                  * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
  { apply Qmult_le_0_compat.
    - apply QleT'_to_Qle.
      apply q_pow_nonneg.
      apply (gcl_ge0_swap (x*y)
               (dmw2_xy_le_1 x y Hx1q Hx2q Hy1q Hy2q)).
    - apply QleT'_to_Qle. apply gcl_beval_seg_ge0; assumption. }
  assert (HB0 : 0 <= q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                  * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y)).
  { apply Qmult_le_0_compat.
    - apply QleT'_to_Qle.
      apply q_pow_nonneg.
      apply (gcl_ge0_swap ((1-x)*(1-y))
               (dmw2_xy_le_1 (1-x) (1-y)
                  (QleT'_to_Qle _ _ (gcl_ge0_swap x Hx2))
                  (QleT'_to_Qle _ _ (gcl_le1_swap x Hx1))
                  (QleT'_to_Qle _ _ (gcl_ge0_swap y Hy2))
                  (QleT'_to_Qle _ _ (gcl_le1_swap y Hy1)))).
    - apply QleT'_to_Qle. apply gcl_beval_seg_ge0
        ; [ exact (gcl_ge0_swap x Hx2) | exact (gcl_le1_swap x Hx1)
          | exact (gcl_ge0_swap y Hy2) | exact (gcl_le1_swap y Hy1) ]. }
  apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply (Qle_trans 0 (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                       (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                         + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M)
                               (1-x) (1-y))).
    + exact HA0.
    + apply QleT'_to_Qle. apply (dmw2_add_ge0_le _ _ HB0).
Qed.

(* ============================================================ *)
(* Sec 4. Named sequence: tau-fixed-point anchor slot strict positivity + slot closure *)
(* ============================================================ *)

(* Named-sequence strict positivity: the A slot (3/4)^(m+2) * F_anchor > 0
   (gcl_q_pow_pos at 3/4 combined with gcl_beval_seg_anchor_pos through
   Qmult_lt_0_compat), the B slot >= 0, hence the sum > 0. *)
Theorem gcl_famseq_pos : forall m : nat, QltT 0 (gcl_famseq m).
Proof.
  intro m. unfold gcl_famseq, gcl_famv.
  assert (HhT : QleT' 0 (1 - (1#2)))
    by (apply Qle_to_QleT'; exact (proj1 (Qle_bool_iff 0 (1 - (1#2))) eq_refl)).
  assert (Hh1T : QleT' (1 - (1#2)) 1) by (apply (gcl_le1_swap (1 - (1#2)) HhT)).
  assert (HA : 0 < q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) m) (1#2) (1#2)).
  { apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply gcl_q_pow_pos.
      apply Qlt_to_QltT.
      apply (Qlt_le_trans 0 (3#4)).
      + apply QltT_to_Qlt.
        exact (id_refl (A:=bool) (x:=Qlt_bool 0 (3#4))).
      + assert (Hq3 : (1 - (1#2)*(1#2)) == (3#4)) by reflexivity.
        rewrite Hq3. apply Qle_refl.
    - apply QltT_to_Qlt. apply gcl_beval_seg_anchor_pos. }
  assert (HB : 0 <= q_pow (1 - (1 - (1#2))*(1 - (1#2))) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                     (1 - (1#2)) (1 - (1#2))).
  { apply Qmult_le_0_compat.
    - apply QleT'_to_Qle.
      apply q_pow_nonneg.
      apply Qle_to_QleT'.
      exact (proj1 (Qle_bool_iff 0 (1 - (1 - (1#2))*(1 - (1#2)))) eq_refl).
    - apply QleT'_to_Qle. apply gcl_beval_seg_ge0; assumption. }
  assert (Hsum : 0 < q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                   * zb2_beval_l (zb2_segl (Datatypes.S m) m) (1#2) (1#2)
                 + q_pow (1 - (1 - (1#2))*(1 - (1#2))) (Datatypes.S (Datatypes.S m))
                   * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                       (1 - (1#2)) (1 - (1#2))).
  { apply (Qlt_le_trans 0 (q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                             * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                                 (1#2) (1#2))).
    - exact HA.
    - apply QleT'_to_Qle. apply (dmw2_add_ge0_le _ _ HB). }
  apply Qlt_to_QltT. apply Qmult_lt_0_compat.
  - unfold Qlt; cbn [Qnum Qden]; lia.
  - exact Hsum.
Qed.

(* Slot closure (main theorem): gcl_sep_generic instantiated with
   Fam := gcl_famseq -- both premises discharged by the Sec 3 / Sec 4 supplies;
   the separation conclusion becomes premise-free. *)
Theorem gcl_famseq_sep : forall (m : nat) (d : Q),
  NatLe 3 m -> QleT' 0 d -> QleT' d (q_pow 3 (Datatypes.S m)) ->
  QltT (d * d * gcl_famseq m) 1.
Proof.
  intros m d Hm Hd0 Hd.
  apply (gcl_sep_generic (fun m0 : nat => gcl_famseq m0) m d
           (NatLe_drop _ _ Hm) Hd0 Hd).
  - unfold gcl_famseq. apply gcl_famv_ge0
      ; [ apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia ].
  - unfold gcl_famseq. apply gcl_famv_le_weight
      ; [ apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia
        | apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia ].
Qed.

(* Numerical anchors (independent recomputation (5) agrees; vm_compute
   literals): gcl_famseq 3 = 58077/4294967296 and
   81^2 * gcl_famseq 3 = 381059397/4294967296 < 1. *)
Lemma gcl_famseq_val0 : QeqT (gcl_famseq 0) (9#256).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_famseq_val3 : QeqT (gcl_famseq 3) (58077#4294967296).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_famseq_sep_concrete : QltT (81 * 81 * gcl_famseq 3) 1.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Sec 5. Extraction and assumption audit *)
(* ============================================================ *)

Separate Extraction gcl_famv gcl_famseq.

Print Assumptions gcl_famv_le_weight.
Print Assumptions gcl_famv_ge0.
Print Assumptions gcl_famseq_pos.
Print Assumptions gcl_famseq_sep.
Print Assumptions gcl_famseq_val3.
Print Assumptions gcl_famseq_sep_concrete.
