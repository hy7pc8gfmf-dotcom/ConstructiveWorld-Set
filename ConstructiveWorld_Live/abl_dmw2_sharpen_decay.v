(* abl_dmw2_sharpen_decay.v -- sharpened family bound, competition      *)
(* verdict and conditional separation for the zeta(2) double integral.  *)
(** * abl_dmw2_sharpen_decay: sharpened-decay layer of the zeta(2) family.
    Mission.  Load the pointwise sharpening layer (abl_dmw2_pointwise_sharp:
    11*N <= 1-xy and 4*11^n*N^(n+1) <= (1-xy)^(n+2)) onto the truncated
    integrand family's sharpened-weight bound and growth competition: (1)
    family bound F_{m+1,M}(x,y) <= (1/4)*(1/11)^m (source face abl_z2_decay
    Sec B was (1/4)*(1/10)^m; sharpened recast); (2) competition verdict
    9^(m+1)*(1/4)*(1/11)^m = (9/4)*(9/11)^m < 1 for m >= 5 (source 1/10
    gear needed m >= 8; the 8->5 shift is on record), with sharpness
    anchors (9/4)*(9/11)^4 >= 1, (9/4)*(9/10)^8 < 1, (9/4)*(9/10)^7 >= 1,
    all computable literal decision anchors; (3) conditional separation:
    d <= 3^(m+1) and sum <= (1/4)*(1/11)^m imply d^2*Isum < 1 for m >= 5
    (premise II' explicit in the statement).  Quantitative note (faithful):
    implied measure gear ~21.85 (1/10) -> ~11.95 (1/11), true optimal limit
    ~11.52; the Rhin-Viola type bound is classical on record; this piece is
    the precondition layer and claims no "first" or "stronger-than".
    Dependencies.  Stdlib (QArith, ZArith, Arith, Lia, Setoid); S01, S02,
    S03, BeukersLists; abl_z2_truncfam (zb2_ps family); abl_z2_itg_carrier
    (zb2_beval_segl, zb2_q_pow_mul, zb2_Isum family); abl_dmw2_pointwise_sharp.
    No external certificate checker, no real-number layer, no classical logic.
    Constructivity.  Purely constructive, zero declared assumptions, zero
    admission-style statements; main statement conclusions take Set-level
    witnesses QleT' / QltT; the nonlinear endgame is carried by the upstream
    square-decomposition certificate.
    References.  Beukers 1979 (Bull. London Math. Soc. 11): decay estimate
    and the lcm^2 growth competition step (Hanson 1972: lcm(1..,n) <= 3^n),
    constant-sharpening recast.
    Build.  rocq c -native-compiler no -q -Q <world> "" abl_dmw2_sharpen_decay.v
    (Rocq 9.1.0, thermal-guard wrapped, same-tree dependency .vo chain). *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier.
Require Import abl_dmw2_pointwise_sharp.

Open Scope Q_scope.

(* ============================================================ *)
(* Sec 0: base gear -- positivity of powers, unit power,          *)
(* positive-factor elimination                                    *)
(* ============================================================ *)

Lemma dmw2_dc_qp_ge0 : forall (k : nat) (z : Q), 0 <= z -> QleT' 0 (q_pow z k).
Proof.
  intros k z Hz. apply q_pow_nonneg. apply Qle_to_QleT'. exact Hz.
Qed.

Lemma dmw2_dc_qp_pos : forall (k : nat) (z : Q), 0 < z -> QltT 0 (q_pow z k).
Proof.
  intros k z Hz. induction k as [| k IH].
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - apply Qlt_to_QltT. cbn [q_pow].
    apply (Qmult_lt_0_compat z (q_pow z k) Hz (QltT_to_Qlt _ _ IH)).
Qed.

Lemma dmw2_dc_qp_one : forall k : nat, q_pow 1 k == 1.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qmult_1_l. exact IH.
Qed.

Lemma dmw2_dc_cancel_one : forall a p : Q, 0 < p -> a * p <= p -> a <= 1.
Proof.
  intros a p Hp H.
  destruct (Qlt_le_dec 1 a) as [Hgt | Hle].
  - exfalso.
    assert (Hlt : 1 * p < a * p) by (apply (Qmult_lt_compat_r 1 a p); assumption).
    assert (Hcon : a * p <= 1 * p).
    { assert (H1 : p == 1 * p) by ring.
      apply (Qle_trans (a * p) p (1 * p)).
      - exact H.
      - exact (QleT'_to_Qle _ _ (dmw2_le_eq p (1 * p) H1)). }
    exact (Qlt_not_le (1 * p) (a * p) Hlt Hcon).
  - exact Hle.
Qed.

(* ============================================================ *)
(* Sec A: positivity face -- nonnegativity of the partial sums    *)
(* and of the truncated integrand family                          *)
(* ============================================================ *)

Lemma dmw2_dc_ps_ge0 : forall (n M : nat) (t : Q), 0 <= t -> QleT' 0 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (zb2_ps_zero n t)).
    exact (QleT'_to_Qle _ _ dmw2_0_le_1).
  - apply Qle_to_QleT'. rewrite zb2_ps_unfold.
    apply (Qle_trans 0 (0 + 0)
             (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))).
    + rewrite Qplus_0_l. apply Qle_refl.
    + apply (Qplus_le_compat 0 (zb2_ps n M t) 0
               ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))).
      * exact (QleT'_to_Qle _ _ IH).
      * apply Qmult_le_0_compat.
        -- exact (QleT'_to_Qle _ _ (zb2_bkC_Q_nonneg (n + Datatypes.S M) n)).
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Ht.
Qed.

Lemma dmw2_dc_carrier_ge0 : forall (n M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' 0 (zb2_beval_l (zb2_segl n M) x y).
Proof.
  intros n M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (HA : 0 <= q_pow (x * (1 - x)) n)
    by (apply QleT'_to_Qle; apply q_pow_nonneg;
        apply (dmw2_mult2_ge0 x (1 - x)); assumption).
  assert (HB : 0 <= q_pow (y * (1 - y)) n)
    by (apply QleT'_to_Qle; apply q_pow_nonneg;
        apply (dmw2_mult2_ge0 y (1 - y)); assumption).
  assert (HC : 0 <= zb2_ps n M (x * y)).
  { pose proof (dmw2_dc_ps_ge0 n M (x * y)
                  (QleT'_to_Qle _ _ (dmw2_mult2_ge0 x y Hx1 Hy1))) as HCt.
    exact (QleT'_to_Qle _ _ HCt). }
  pose proof (qeqT_imp_qeq _ _ (zb2_beval_segl n M x y)) as Hseg.
  apply Qle_to_QleT'. rewrite Hseg.
  assert (HAB : 0 <= q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
    by (apply Qmult_le_0_compat; assumption).
  apply (Qmult_le_0_compat (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
                           (zb2_ps n M (x * y)) HAB HC).
Qed.

(* Weight nonnegative: 0 <= (1/4)*(1/11)^m *)
Lemma dmw2_dc_weight_ge0 : forall m : nat, QleT' 0 ((1#4) * q_pow (1#11) m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
    unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* Sec B: sharpened-weight face -- pointwise upper bound          *)
(* (1/4)(1/11)^m for the truncated integrand family              *)
(* ============================================================ *)

(* Main theorem (sharpened-weight face): at exponent gear n = m+1 and for
   all x y in [0,1]^2, the truncated integrand F_{m+1,M}(x,y)
   <= (1/4)*(1/11)^m.
   Proof chain: the partial-sum upper-bound lemma ((1-t)^(m+2)*sum <= 1)
   and the power merge give T^(m+2)*F <= N^(m+1) (T := 1-xy,
   N := x(1-x)y(1-y)); the sharpened pointwise decay 4*11^m*N^(m+1)
   <= T^(m+2); multiplying both through by 4*11^m and chaining, then
   case-splitting on the sign of T: for T > 0 the positive-factor
   cancellation law yields 4*11^m*F <= 1, then multiplying by the weight
   (1/4)(1/11)^m closes F <= (1/4)(1/11)^m; for T = 0, combining xy <= 1
   gives x = y = 1 and F = 0. *)
Theorem dmw2_dc_carrier_decay : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y) ((1#4) * q_pow (1#11) m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy1 : x * y <= 1) by (apply QleT'_to_Qle; apply (dmw2_xy_le_1 x y); assumption).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x * y) (conj Hxy0 Hxy1)) as HpsT.
  pose proof (QleT'_to_Qle _ _ HpsT) as Hps.
  pose proof (qeqT_imp_qeq _ _ (zb2_beval_segl (Datatypes.S m) M x y)) as Hseg.
  assert (Hmerge : q_pow (x * (1 - x)) (Datatypes.S m) * q_pow (y * (1 - y)) (Datatypes.S m)
                == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul (x * (1 - x)) (y * (1 - y)) (Datatypes.S m))).
    assert (Hrg : (x * (1 - x)) * (y * (1 - y)) == x * (1 - x) * y * (1 - y)) by ring.
    exact (qeqT_imp_qeq _ _ (q_pow_wd _ _ _ (qeq_imp_qeqT _ _ Hrg))). }
  rewrite Hmerge in Hseg.
  assert (HN0 : 0 <= x * (1 - x) * y * (1 - y))
    by (apply QleT'_to_Qle; apply (dmw2_mult4_ge0 x (1 - x) y (1 - y)); assumption).
  assert (HK0 : 0 <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact HN0).
  (* (A): T^(m+2)*F <= N^(m+1) *)
  assert (HA : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
            <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { assert (Hrw : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
               == (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_ps (Datatypes.S m) M (x * y))
                  * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
      by (rewrite Hseg; ring).
    rewrite Hrw.
    apply (Qle_trans _ (1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_ps (Datatypes.S m) M (x * y))
                               1 (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) Hps HK0).
    - assert (H1K : 1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                 == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) by ring.
      rewrite H1K. apply Qle_refl. }
  (* (B): 4*11^m*N^(m+1) <= T^(m+2) (sharpened pointwise decay, power
     notation unified to q_pow) *)
  assert (Hcv : forall (t : Q) (k : nat), dmw2_pow t k == q_pow t k).
  { intros t k. induction k as [| k IH].
    - reflexivity.
    - cbn [dmw2_pow q_pow]. rewrite IH. ring. }
  pose proof (dmw2_pointwise_decay m x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as HdecT.
  pose proof (dmw2_qle_to_Qle _ _ HdecT) as Hdec0.
  rewrite (Hcv 11 m) in Hdec0.
  rewrite (Hcv (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) in Hdec0.
  rewrite (Hcv (1 - x * y) (Datatypes.S (Datatypes.S m))) in Hdec0.
  assert (HK111 : 0 <= 4 * q_pow 11 m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
      unfold Qle. simpl. lia. }
  (* Combination: chain (A) right-multiplied by 4*11^m with (B) *)
  assert (HC : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
               * (4 * q_pow 11 m) <= q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))).
  { apply (Qle_trans _ (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) * (4 * q_pow 11 m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                               (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               (4 * q_pow 11 m) HA HK111).
    - assert (Hcomm : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) * (4 * q_pow 11 m)
                   == 4 * q_pow 11 m * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
        by ring.
      rewrite Hcomm. exact Hdec0. }
  (* Case split on the sign of T = 1-xy *)
  destruct (Qlt_le_dec 0 (1 - x * y)) as [Hpos | Hneg].
  - (* Main case: T > 0, cancel the positive factor, then multiply by the weight *)
    pose proof (QltT_to_Qlt _ _ (dmw2_dc_qp_pos (Datatypes.S (Datatypes.S m)) (1 - x * y) Hpos)) as HPpos.
    assert (Hrg : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                  * (4 * q_pow 11 m)
               == (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 11 m))
                  * q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) by ring.
    rewrite Hrg in HC.
    pose proof (dmw2_dc_cancel_one (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 11 m))
                                  (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) HPpos HC) as H1.
    pose proof (QleT'_to_Qle _ _ (dmw2_dc_weight_ge0 m)) as HW0.
    pose proof (Qmult_le_compat_r (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 11 m))
                                  1 ((1#4) * q_pow (1#11) m) H1 HW0) as Hmult.
    assert (Hunit : (4 * q_pow 11 m) * ((1#4) * q_pow (1#11) m) == 1).
    { assert (Hpm : q_pow 11 m * q_pow (1#11) m == 1).
      { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 11 (1#11) m)).
        assert (H1111 : 11 * (1#11) == 1) by ring.
        rewrite H1111. apply dmw2_dc_qp_one. }
      assert (Hre : (4 * q_pow 11 m) * ((1#4) * q_pow (1#11) m)
                 == (4 * (1#4)) * (q_pow 11 m * q_pow (1#11) m)) by ring.
      rewrite Hre, Hpm. ring. }
    assert (Hlhs : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 11 m))
                   * ((1#4) * q_pow (1#11) m)
                == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
    { assert (Hre2 : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 11 m))
                     * ((1#4) * q_pow (1#11) m)
                  == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * ((4 * q_pow 11 m) * ((1#4) * q_pow (1#11) m))) by ring.
      rewrite Hre2, Hunit. ring. }
    assert (Hrhs : 1 * ((1#4) * q_pow (1#11) m) == (1#4) * q_pow (1#11) m) by ring.
    rewrite Hrhs in Hmult. rewrite Hlhs in Hmult.
    apply Qle_to_QleT'. exact Hmult.
  - (* Boundary case: T <= 0 together with xy <= 1 gives T = 0, hence
       x = y = 1 and F = 0 *)
    assert (HT0 : 0 <= 1 - x * y) by (apply QleT'_to_Qle; apply (dmw2_le_sub (x * y) 1); exact Hxy1).
    assert (HTeq : 1 - x * y == 0) by (apply Qle_antisym; [ exact Hneg | exact HT0 ]).
    assert (Hxyeq : x * y == 1).
    { assert (Ha : 1 - (1 - x * y) == 1 - 0) by (rewrite HTeq; ring).
      assert (Hb : 1 - (1 - x * y) == x * y) by ring.
      assert (Hc : 1 - 0 == 1) by ring.
      rewrite Hb, Hc in Ha. exact Ha. }
    assert (Hle1 : x * y <= x).
    { pose proof (Qmult_le_compat_r y 1 x Hy2 Hx1) as Hq.
      assert (Hd1 : y * x == x * y) by ring. assert (Hd2 : 1 * x == x) by ring.
      rewrite Hd1, Hd2 in Hq. exact Hq. }
    assert (Hle2 : x * y <= y).
    { pose proof (Qmult_le_compat_r x 1 y Hx2 Hy1) as Hq.
      assert (Hd2 : 1 * y == y) by ring. rewrite Hd2 in Hq. exact Hq. }
    assert (Hx1e : x == 1).
    { apply Qle_antisym.
      - exact Hx2.
      - apply (Qle_trans 1 (x * y) x).
        + apply QleT'_to_Qle. apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle1. }
    assert (Hy1e : y == 1).
    { apply Qle_antisym.
      - exact Hy2.
      - apply (Qle_trans 1 (x * y) y).
        + apply QleT'_to_Qle. apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle2. }
    assert (HN0e : x * (1 - x) * y * (1 - y) == 0) by (rewrite Hx1e, Hy1e; ring).
    assert (Hq0 : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) == 0)
      by (rewrite HN0e; cbn [q_pow]; apply Qmult_0_l).
    assert (Hc0 : zb2_beval_l (zb2_segl (Datatypes.S m) M) x y == 0)
      by (rewrite Hseg, Hq0; apply Qmult_0_l).
    apply Qle_to_QleT'. rewrite Hc0.
    apply QleT'_to_Qle. apply dmw2_dc_weight_ge0.
Qed.

(* Numeric anchor: exact value of the weight gear at m=1, (1/4)*(1/11) = 1/44
   (sharpening contrast: the source face has 1/40 at the same gear; this anchor
   together with the sharpness-contrast anchors forms the machine-checkable
   sharpening record of the family-bound constant layer) *)
Lemma dmw2_dc_anchor_weight : (1#4) * q_pow (1#11) 1 == (1#44).
Proof. vm_compute. reflexivity. Qed.

(* Sharpness-contrast anchor: new weight 1/44 <= old weight 1/40 (Qle_bool
   decidable) *)
Lemma dmw2_dc_anchor_sharpen : QleT' (1#44) (1#40).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool (1#44) (1#40))).
Qed.

(* ============================================================ *)
(* Sec C: competition face -- 9^(m+1)*(1/4)(1/11)^m = (9/4)(9/11)^m *)
(* < 1 for m >= 5                                                 *)
(* ============================================================ *)

(* Competition identity: 9^(m+1)*(1/4)*(1/11)^m = (9/4)*(9/11)^m *)
Lemma dmw2_dc_comp_id : forall m : nat,
  q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#11) m) == (9#4) * q_pow (9#11) m.
Proof.
  intro m.
  assert (Hpm : q_pow 9 m * q_pow (1#11) m == q_pow (9#11) m).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 9 (1#11) m)).
    assert (H911 : 9 * (1#11) == (9#11)) by ring.
    rewrite H911. reflexivity. }
  assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#11) m)
             == (9 * (1#4)) * (q_pow 9 m * q_pow (1#11) m)).
  { rewrite (qeqT_imp_qeq _ _ (q_pow_succ 9 m)). ring. }
  rewrite Hre, Hpm. ring.
Qed.

(* Competition base gear: (9/4)*(9/11)^5 = 531441/644204 < 1 (literal
   rational, Qlt_bool decision) *)
Lemma dmw2_dc_comp_base : QltT ((9#4) * q_pow (9#11) 5) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (9#11) 5) 1)).
Qed.

(* Threshold sharpness anchor (new gear): (9/4)*(9/11)^4 = 59049/58564 >= 1,
   i.e. m=4 falls short, so the decision threshold m >= 5 is sharp
   (Qle_bool decidable) *)
Lemma dmw2_dc_comp_base4_ge : QleT' 1 ((9#4) * q_pow (9#11) 4).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (9#11) 4))).
Qed.

(* Old-gear contrast anchor 1: (9/4)*(9/10)^8 = 387420489/400000000 < 1
   (source-face base gear recomputed) *)
Lemma dmw2_dc_old_base : QltT ((9#4) * q_pow (9#10) 8) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (9#10) 8) 1)).
Qed.

(* Old-gear contrast anchor 2: (9/4)*(9/10)^7 = 43046721/40000000 >= 1 -- the
   old-gear threshold 8 is sharp *)
Lemma dmw2_dc_old_seven_ge : QleT' 1 ((9#4) * q_pow (9#10) 7).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (9#10) 7))).
Qed.

(* Competition step: (9/4)*(9/11)^(m+1) <= (9/4)*(9/11)^m (both sides
   multiplied by (9/11) <= 1) *)
Lemma dmw2_dc_comp_step : forall m : nat,
  QleT' ((9#4) * q_pow (9#11) (Datatypes.S m)) ((9#4) * q_pow (9#11) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (9#11) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'.
      unfold Qle. simpl. lia. }
  assert (H911 : (9#11) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (9#11) (Datatypes.S m)
             == (9#11) * ((9#4) * q_pow (9#11) m))
    by (rewrite (qeqT_imp_qeq _ _ (q_pow_succ (9#11) m)); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (9#11) 1 ((9#4) * q_pow (9#11) m) H911 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (9#11) m) == (9#4) * q_pow (9#11) m) by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* Competition shift: (9/4)*(9/11)^(m+d) <= (9/4)*(9/11)^m (induction on the
   shift d) *)
Lemma dmw2_dc_comp_drop : forall (d m : nat),
  QleT' ((9#4) * q_pow (9#11) (m + d)) ((9#4) * q_pow (9#11) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat) by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (9#11) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (9#11) (m + d))
                       ((9#4) * q_pow (9#11) m)).
    + apply dmw2_dc_comp_step.
    + apply IH.
Qed.

(* Competition verdict: m >= 5 implies (9/4)*(9/11)^m < 1
   (decidable case split via le_lt_dec: for m > 5, step down to the base
    gear; for m <= 5, the premise forces m+1 = 5, landing directly on the
    base gear) *)
Lemma dmw2_dc_comp_verdict : forall m : nat, (5 <= m)%nat -> QltT ((9#4) * q_pow (9#11) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 5 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (9#11) (Datatypes.S m))
                           ((9#4) * q_pow (9#11) m) 1).
      * apply dmw2_dc_comp_step.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 5)%nat) by lia.
      rewrite Heq. exact dmw2_dc_comp_base.
Qed.

(* ============================================================ *)
(* Sec D: conditional separation face -- d^2*I_{m+1} < 1          *)
(* (explicit-premise form, sharpened gear)                        *)
(* ============================================================ *)

(* Squared weight: 0 <= d <= 3^n implies d^2 <= 9^n (= 3^n*3^n, power merge) *)
Lemma dmw2_dc_weight_sq : forall (n : nat) (d : Q),
  QleT' 0 d -> QleT' d (q_pow 3 n) -> QleT' (d * d) (q_pow 9 n).
Proof.
  intros n d Hd0 Hd.
  pose proof (QleT'_to_Qle _ _ Hd0) as Hd0q.
  pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
  assert (H30 : 0 <= q_pow 3 n)
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT';
        unfold Qle; simpl; lia).
  assert (H1 : d * d <= q_pow 3 n * d)
    by (apply (Qmult_le_compat_r d (q_pow 3 n) d); assumption).
  assert (H2 : q_pow 3 n * d <= q_pow 3 n * q_pow 3 n).
  { assert (H2' : d * q_pow 3 n <= q_pow 3 n * q_pow 3 n)
      by (apply (Qmult_le_compat_r d (q_pow 3 n) (q_pow 3 n)); assumption).
    assert (Hc : q_pow 3 n * d == d * q_pow 3 n) by ring.
    rewrite Hc. exact H2'. }
  assert (Hfin : d * d <= q_pow 3 n * q_pow 3 n)
    by (apply (Qle_trans _ (q_pow 3 n * d)); assumption).
  assert (Hsq : q_pow 3 n * q_pow 3 n == q_pow 9 n).
  { rewrite <- (qeqT_imp_qeq _ _ (zb2_q_pow_mul 3 3 n)).
    assert (H33 : 3 * 3 == 9) by ring.
    rewrite H33. reflexivity. }
  rewrite Hsq in Hfin. apply Qle_to_QleT'. exact Hfin.
Qed.

(* Separation main theorem (explicit-premise form, sharpened gear): let d
   satisfy 0 <= d <= 3^(m+1) (d's concrete upper bound is instantiated by the
   downstream Hanson-chain gapB/valbridge supplier at the same type), and let
   the integral value I_{m+1} satisfy I <= (1/4)(1/11)^m (sharpened premise
   II' -- the passage from the pointwise/family bound to the integral upper
   bound is precisely Sec B of this piece, the 1/11 recast face of the
   downstream tail-bound machine); then for m >= 5, d^2*I_{m+1} < 1.
   Nonnegativity of the integral value is taken from the existing strict
   positivity lemma of the Isum family. *)
Theorem dmw2_dc_sep_small : forall (m M : nat) (d : Q),
  (5 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (zb2_Isum (Datatypes.S m) M) ((1#4) * q_pow (1#11) m) ->
  QltT (d * d * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d Hm Hd0 Hd HI.
  pose proof (dmw2_dc_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (zb2_Isum_pos (Datatypes.S m) M) as HposT.
  pose proof (QleT'_to_Qle _ _ (qltT_leT' _ _ HposT)) as HposI.
  pose proof (QleT'_to_Qle _ _ HI) as HIq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT';
        unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * zb2_Isum (Datatypes.S m) M <= q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m)) (zb2_Isum (Datatypes.S m) M)
                                 Hsqq HposI)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#11) m)).
  { assert (H2' : zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)
               <= ((1#4) * q_pow (1#11) m) * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (zb2_Isum (Datatypes.S m) M) ((1#4) * q_pow (1#11) m)
                                   (q_pow 9 (Datatypes.S m)) HIq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
               == zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : ((1#4) * q_pow (1#11) m) * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#11) m)) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * zb2_Isum (Datatypes.S m) M <= (9#4) * q_pow (9#11) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#11) m))).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (QleT'_to_Qle _ _ (dmw2_le_eq _ _ (dmw2_dc_comp_id m))). }
  pose proof (QltT_to_Qlt _ _ (dmw2_dc_comp_verdict m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* Numeric anchor 3: competition base-gear literal value
   (9/4)*(9/11)^5 == 531441/644204 (vm_compute recheck) *)
Lemma dmw2_dc_anchor_base_val : (9#4) * q_pow (9#11) 5 == (531441#644204).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Sec E: extraction and assumption audit (zero-global-assumption *)
(* recheck)                                                       *)
(* ============================================================ *)

Separate Extraction dmw2_dc_comp_verdict dmw2_dc_sep_small.

Print Assumptions dmw2_dc_qp_ge0.
Print Assumptions dmw2_dc_qp_pos.
Print Assumptions dmw2_dc_qp_one.
Print Assumptions dmw2_dc_cancel_one.
Print Assumptions dmw2_dc_ps_ge0.
Print Assumptions dmw2_dc_carrier_ge0.
Print Assumptions dmw2_dc_weight_ge0.
Print Assumptions dmw2_dc_carrier_decay.
Print Assumptions dmw2_dc_anchor_weight.
Print Assumptions dmw2_dc_anchor_sharpen.
Print Assumptions dmw2_dc_comp_id.
Print Assumptions dmw2_dc_comp_base.
Print Assumptions dmw2_dc_comp_base4_ge.
Print Assumptions dmw2_dc_old_base.
Print Assumptions dmw2_dc_old_seven_ge.
Print Assumptions dmw2_dc_comp_step.
Print Assumptions dmw2_dc_comp_drop.
Print Assumptions dmw2_dc_comp_verdict.
Print Assumptions dmw2_dc_weight_sq.
Print Assumptions dmw2_dc_sep_small.
Print Assumptions dmw2_dc_anchor_base_val.
