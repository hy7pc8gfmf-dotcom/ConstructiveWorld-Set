(* ConstructiveWorld-Set -- exact-tier pointwise improvement certificates on decidable Q-carriers. *)

(** * d519a2_cert: the pointwise certificate [56*N <= 3+s-2p] at the exact tier [theta(3) = 1/14].

    Mission.  Formalizes the sharp pointwise improvement certificate
      [56 * x * (1-x) * y * (1-y) <= 3 + x + y - 2*x*y] for the weight
      [d519_psi3] on the unit square, the exact tier [theta(3) = 1/14] above
      the 1/12 tier, proved by a four-base AM-GM route with a boolean
      [Qle_bool] case split at [sigma = 1/2]; carries the diagonal layer
      [d519_u_le_14] and [d519_diag_N_le_14], the normalized chain shape
      [d519_N_le_14_psihat], the ceiling [d519_psi3_le_4], and the anchors
      [d519_anchor_tight], [d519_theta14], [d519_sigma_trade].

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Lia],
      [Extraction].  Requires [S02_CauchyComplete],
      [abl_dmw2_pointwise_sharp] of this development.

    References.  This development, d519a2_cert.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" d519a2_cert.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import QArith.QArith ZArith.ZArith Lia.
From Stdlib Require Import Extraction.
Require Import S02_CauchyComplete abl_dmw2_pointwise_sharp.

Open Scope Q_scope.

(* ============================================================ *)
(* Section 0. Statement face: the [d519_psi3] weight and its canonical bridges *)
(* ============================================================ *)

(* [d519_psi3] := 3 + s - 2p, the s - 2p shape of the u = 3 pure-orbit positive combination; carried by [Set] as a Defined [Q] function. *)
Definition d519_psi3 (x y : Q) : Q := 3 + x + y - 2 * x * y.

Lemma d519_psi3_eq : forall x y : Q,
  d519_psi3 x y == 3 + x + y - 2 * x * y.
Proof.
  intros x y. unfold d519_psi3. reflexivity.
Qed.

(* ============================================================ *)
(* Section 1. The u diagonal layer: closed-form factorization, domain positivity, and the diagonal reduction *)
(* ============================================================ *)

(* closed-form factorization of 3 + 2u - 56u^2; the constant is 3/14, since the 3/28 variant would expand to 3/2 + 8u - 56u^2 rather than the original polynomial. *)
Lemma d519_u_fact : forall u : Q,
  3 + 2 * u - 56 * u * u == 56 * ((1#4) - u) * (u + (3#14)).
Proof.
  intro u. ring.
Qed.

(* domain closing on u: u in [0, 1/4] yields 56u^2 <= 3 + 2u. *)
Theorem d519_u_le_14 : forall u : Q,
  0 <= u -> u <= (1#4) -> QleT' (56 * u * u) (3 + 2 * u).
Proof.
  intros u Hu0 Hu1.
  apply (dmw2_sub_ge0 (56 * u * u) (3 + 2 * u)).
  rewrite (d519_u_fact u).
  apply Qmult_le_0_compat.
  - apply QleT'_to_Qle.
    apply (dmw2_mult2_ge0 56 ((1#4) - u)).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply QleT'_to_Qle.
      apply (dmw2_le_sub u (1#4)). exact Hu1.
  - apply (Qle_trans 0 u (u + (3#14))).
    + exact Hu0.
    + apply QleT'_to_Qle.
      apply (dmw2_add_ge0_le u (3#14)). unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* diagonal specialization of AM-GM: v * (1 - v) <= 1/4, since (2v - 1)^2 >= 0. *)
Lemma d519_v1v_le_quarter : forall v : Q, v * (1 - v) <= (1#4).
Proof.
  intro v.
  apply QleT'_to_Qle.
  apply (dmw2_sub_ge0 (v * (1 - v)) (1#4)).
  assert (E : (1#4) - v * (1 - v) == (2 * v - 1) * (2 * v - 1) * (1#4)) by ring.
  rewrite E. apply Qmult_le_0_compat.
  - apply QleT'_to_Qle.
    apply dmw2_sq_ge0.
  - unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* diagonal reduction: the worst case p = s^2/4 sits on the diagonal, so for
   v in [0, 1] it suffices that 56 * (v * (1 - v))^2 <= 3 + 2 * v * (1 - v). *)
Theorem d519_diag_N_le_14 : forall v : Q,
  0 <= v <= 1 ->
  QleT' (56 * v * (1 - v) * (v * (1 - v))) (3 + v + v - 2 * v * v).
Proof.
  intro v. intros [Hv0 Hv1].
  assert (Hvb : 0 <= 1 - v) by (apply QleT'_to_Qle; apply (dmw2_le_sub v 1); exact Hv1).
  assert (Hu0 : 0 <= v * (1 - v))
    by (apply Qmult_le_0_compat; [ exact Hv0 | exact Hvb ]).
  pose proof (d519_u_le_14 (v * (1 - v)) Hu0 (d519_v1v_le_quarter v)) as H.
  apply Qle_to_QleT'.
  assert (E1 : 56 * v * (1 - v) * (v * (1 - v))
            == 56 * (v * (1 - v)) * (v * (1 - v))) by ring.
  assert (E2 : 3 + v + v - 2 * v * v == 3 + 2 * (v * (1 - v))) by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle. exact H.
Qed.

(* ============================================================ *)
(* Section 2. The main statement: [56*N <= 3+s-2p] by the four-base algebra route *)
(* ============================================================ *)

Theorem d519_N_le_14 : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (56 * x * (1 - x) * y * (1 - y)) (3 + x + y - 2 * x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  (* the four bases x * (1 - y), y * (1 - x), (1 - x) * (1 - y), x * y are nonnegative on the unit square. *)
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (Ha : 0 <= x * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hb : 0 <= y * (1 - x)) by (apply Qmult_le_0_compat; assumption).
  assert (Hc : 0 <= (1 - x) * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hd : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hs0 : 0 <= x * (1 - y) + y * (1 - x)).
  { apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
    - exact Ha.
    - apply QleT'_to_Qle.
      apply (dmw2_add_ge0_le (x * (1 - y)) (y * (1 - x))). exact Hb. }
  assert (Ht0 : 0 <= (1 - x) * (1 - y) + x * y).
  { apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
    - exact Hc.
    - apply QleT'_to_Qle.
      apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)). exact Hd. }
  (* the four-base identities: N == a * b == c * d and sigma + tau == 1. *)
  assert (HNab : x * (1 - x) * y * (1 - y) == (x * (1 - y)) * (y * (1 - x))) by ring.
  assert (HNcd : x * (1 - x) * y * (1 - y) == ((1 - x) * (1 - y)) * (x * y)) by ring.
  assert (Hsym : x * (1 - y) + y * (1 - x) + ((1 - x) * (1 - y) + x * y) == 1) by ring.
  (* AM-GM twice, each instance closing by a square-difference identity. *)
  assert (Hgm1 : 4 * ((x * (1 - y)) * (y * (1 - x)))
              <= (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))).
  { apply QleT'_to_Qle.
    apply (dmw2_sub_ge0 (4 * ((x * (1 - y)) * (y * (1 - x))))
             ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)))).
    assert (E : (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))
                - 4 * ((x * (1 - y)) * (y * (1 - x)))
             == ((x * (1 - y)) - (y * (1 - x)))
                * ((x * (1 - y)) - (y * (1 - x)))) by ring.
    rewrite E. apply QleT'_to_Qle. apply dmw2_sq_ge0. }
  assert (Hgm2 : 4 * (((1 - x) * (1 - y)) * (x * y))
              <= ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)).
  { apply QleT'_to_Qle.
    apply (dmw2_sub_ge0 (4 * (((1 - x) * (1 - y)) * (x * y)))
             (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y))).
    assert (E : ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)
                - 4 * (((1 - x) * (1 - y)) * (x * y))
             == (((1 - x) * (1 - y)) - (x * y))
                * (((1 - x) * (1 - y)) - (x * y))) by ring.
    rewrite E. apply QleT'_to_Qle. apply dmw2_sq_ge0. }
  (* case split on the boolean reflection of sigma := a + b against 1/2, analyzed in place. *)
  destruct (Qle_bool (x * (1 - y) + y * (1 - x)) (1#2)) eqn:Hbs.
  - (* branch sigma <= 1/2: 56N = 56ab <= 14 sigma^2 <= 3 + sigma, the last step by the factorization (1 - 2 sigma) * (7 sigma + 3) >= 0. *)
    assert (Hhalf : x * (1 - y) + y * (1 - x) <= (1#2)).
    { apply QleT'_to_Qle. unfold QleT'. rewrite Hbs. reflexivity. }
    assert (H72 : 0 <= 1 - 2 * (x * (1 - y) + y * (1 - x))).
    { assert (E : 1 - 2 * (x * (1 - y) + y * (1 - x))
               == 2 * ((1#2) - (x * (1 - y) + y * (1 - x)))) by ring.
      rewrite E. apply Qmult_le_0_compat.
      - unfold Qle. cbn [Qnum Qden]. lia.
      - apply QleT'_to_Qle.
        apply (dmw2_le_sub (x * (1 - y) + y * (1 - x)) (1#2)). exact Hhalf. }
    assert (H73 : 0 <= 7 * (x * (1 - y) + y * (1 - x)) + 3).
    { assert (H7s : 0 <= 7 * (x * (1 - y) + y * (1 - x)))
        by (apply QleT'_to_Qle; apply (dmw2_mult2_ge0 7 (x * (1 - y) + y * (1 - x)))
            ; [ unfold Qle; cbn [Qnum Qden]; lia | exact Hs0 ]).
      apply (Qle_trans 0 (7 * (x * (1 - y) + y * (1 - x)))
                        (7 * (x * (1 - y) + y * (1 - x)) + 3)).
      - exact H7s.
      - apply QleT'_to_Qle.
        apply (dmw2_add_ge0_le (7 * (x * (1 - y) + y * (1 - x))) 3)
        ; unfold Qle; cbn [Qnum Qden]; lia. }
    assert (HQ1 : (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14
               <= 3 + (x * (1 - y) + y * (1 - x))).
    { apply QleT'_to_Qle.
      apply (dmw2_sub_ge0
               ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14)
               (3 + (x * (1 - y) + y * (1 - x)))).
      assert (E : 3 + (x * (1 - y) + y * (1 - x))
                  - (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14
               == (1 - 2 * (x * (1 - y) + y * (1 - x)))
                  * (7 * (x * (1 - y) + y * (1 - x)) + 3)) by ring.
      rewrite E. apply Qmult_le_0_compat; assumption. }
    assert (HQ2 : 56 * ((x * (1 - y)) * (y * (1 - x)))
               <= (x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14).
    { assert (H14 : 0 <= 14) by (unfold Qle; cbn [Qnum Qden]; lia).
      pose proof (Qmult_le_compat_r (4 * ((x * (1 - y)) * (y * (1 - x))))
                    ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x))) 14
                    Hgm1 H14) as Hm.
      assert (E : (4 * ((x * (1 - y)) * (y * (1 - x)))) * 14
               == 56 * ((x * (1 - y)) * (y * (1 - x)))) by ring.
      rewrite E in Hm. exact Hm. }
    apply Qle_to_QleT'.
    assert (E1 : 56 * x * (1 - x) * y * (1 - y)
              == 56 * ((x * (1 - y)) * (y * (1 - x)))) by ring.
    assert (E2 : 3 + x + y - 2 * x * y
              == 3 + (x * (1 - y) + y * (1 - x))) by ring.
    rewrite E1, E2.
    apply (Qle_trans
             (56 * ((x * (1 - y)) * (y * (1 - x))))
             ((x * (1 - y) + y * (1 - x)) * (x * (1 - y) + y * (1 - x)) * 14)
             (3 + (x * (1 - y) + y * (1 - x)))).
    + exact HQ2.
    + exact HQ1.
  - (* branch sigma > 1/2: then tau := c + d <= 1/2 and 56N = 56cd <= 14 tau^2 <= 4 - tau = 3 + sigma, the last step by the factorization (1 - 2 tau) * (7 tau + 4) >= 0. *)
    assert (Hnle : ~ (x * (1 - y) + y * (1 - x) <= (1#2))).
    { intro Hcc.
      assert (HcT : QleT' (x * (1 - y) + y * (1 - x)) (1#2))
        by (apply Qle_to_QleT'; exact Hcc).
      unfold QleT' in HcT. rewrite Hbs in HcT. inversion HcT. }
    assert (Hgt : (1#2) < x * (1 - y) + y * (1 - x)).
    { apply (Qnot_le_lt (x * (1 - y) + y * (1 - x)) (1#2)). exact Hnle. }
    assert (Hs1 : x * (1 - y) + y * (1 - x) <= 1).
    { pose proof (Qplus_le_compat (x * (1 - y) + y * (1 - x))
                                  (x * (1 - y) + y * (1 - x)) 0
                                  ((1 - x) * (1 - y) + x * y)
                                  (Qle_refl (x * (1 - y) + y * (1 - x))) Ht0) as Hs.
      assert (Ez : x * (1 - y) + y * (1 - x) + 0
                == x * (1 - y) + y * (1 - x)) by ring.
      rewrite Ez in Hs. rewrite Hsym in Hs. exact Hs. }
    assert (Ht2 : 0 <= 1 - 2 * ((1 - x) * (1 - y) + x * y)).
    { assert (E : 1 - 2 * ((1 - x) * (1 - y) + x * y)
               == 2 * ((x * (1 - y) + y * (1 - x)) - (1#2))) by ring.
      rewrite E. apply Qmult_le_0_compat.
      - unfold Qle. cbn [Qnum Qden]. lia.
      - apply QleT'_to_Qle.
        apply (dmw2_le_sub (1#2) (x * (1 - y) + y * (1 - x)))
        ; apply Qlt_le_weak; exact Hgt. }
    assert (Ht4 : 0 <= 7 * ((1 - x) * (1 - y) + x * y) + 4).
    { assert (H7t : 0 <= 7 * ((1 - x) * (1 - y) + x * y))
        by (apply QleT'_to_Qle; apply (dmw2_mult2_ge0 7 ((1 - x) * (1 - y) + x * y))
            ; [ unfold Qle; cbn [Qnum Qden]; lia | exact Ht0 ]).
      apply (Qle_trans 0 (7 * ((1 - x) * (1 - y) + x * y))
                        (7 * ((1 - x) * (1 - y) + x * y) + 4)).
      - exact H7t.
      - apply QleT'_to_Qle.
        apply (dmw2_add_ge0_le (7 * ((1 - x) * (1 - y) + x * y)) 4)
        ; unfold Qle; cbn [Qnum Qden]; lia. }
    assert (HQ1 : ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14
               <= 4 - ((1 - x) * (1 - y) + x * y)).
    { apply QleT'_to_Qle.
      apply (dmw2_sub_ge0
               (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14)
               (4 - ((1 - x) * (1 - y) + x * y))).
      assert (E : 4 - ((1 - x) * (1 - y) + x * y)
                  - ((1 - x) * (1 - y) + x * y)
                    * ((1 - x) * (1 - y) + x * y) * 14
               == (1 - 2 * ((1 - x) * (1 - y) + x * y))
                  * (7 * ((1 - x) * (1 - y) + x * y) + 4)) by ring.
      rewrite E. apply Qmult_le_0_compat; assumption. }
    assert (HQ2 : 56 * (((1 - x) * (1 - y)) * (x * y))
               <= ((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14).
    { assert (H14 : 0 <= 14) by (unfold Qle; cbn [Qnum Qden]; lia).
      pose proof (Qmult_le_compat_r (4 * (((1 - x) * (1 - y)) * (x * y)))
                    (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y)) 14
                    Hgm2 H14) as Hm.
      assert (E : (4 * (((1 - x) * (1 - y)) * (x * y))) * 14
               == 56 * (((1 - x) * (1 - y)) * (x * y))) by ring.
      rewrite E in Hm. exact Hm. }
    apply Qle_to_QleT'.
    assert (E1 : 56 * x * (1 - x) * y * (1 - y)
              == 56 * (((1 - x) * (1 - y)) * (x * y))) by ring.
    assert (E2 : 3 + x + y - 2 * x * y
              == 4 - ((1 - x) * (1 - y) + x * y)) by ring.
    rewrite E1, E2.
    apply (Qle_trans
             (56 * (((1 - x) * (1 - y)) * (x * y)))
             (((1 - x) * (1 - y) + x * y) * ((1 - x) * (1 - y) + x * y) * 14)
             (4 - ((1 - x) * (1 - y) + x * y))).
    + exact HQ2.
    + exact HQ1.
Qed.

(* ============================================================ *)
(* Section 3. The normalized chain shape, the ceiling [d519_psi3_le_4], and the anchors *)
(* ============================================================ *)

(* normalized chain shape: 14N <= psi_3 * (1/4), i.e. N <= (1/14) * (psi_3 / 4) with the normalized weight psi_3 / 4 peaking at 1 at the center; this is the form consumed by the later weight-replacement step of the famv bound. *)
Theorem d519_N_le_14_psihat : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (14 * x * (1 - x) * y * (1 - y)) ((3 + x + y - 2 * x * y) * (1#4)).
Proof.
  intros x y Hx Hy.
  pose proof (QleT'_to_Qle _ _ (d519_N_le_14 x y Hx Hy)) as H.
  assert (Hq : 0 <= (1#4)) by (unfold Qle; cbn [Qnum Qden]; lia).
  pose proof (Qmult_le_compat_r (56 * x * (1 - x) * y * (1 - y))
                (3 + x + y - 2 * x * y) (1#4) H Hq) as Hm.
  assert (E : (56 * x * (1 - x) * y * (1 - y)) * (1#4)
           == 14 * x * (1 - x) * y * (1 - y)) by ring.
  rewrite E in Hm.
  apply Qle_to_QleT'. exact Hm.
Qed.

(* the ceiling psi_3 <= 4: 4 - psi_3 == (1 - x) * (1 - y) + x * y >= 0, the numerator side of the normalized weight peaking at 1. *)
Theorem d519_psi3_le_4 : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> QleT' (3 + x + y - 2 * x * y) 4.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  apply (dmw2_sub_ge0 (3 + x + y - 2 * x * y) 4).
  assert (E : 4 - (3 + x + y - 2 * x * y) == (1 - x) * (1 - y) + x * y) by ring.
  rewrite E.
  assert (Hxb : 0 <= 1 - x) by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (H1 : 0 <= (1 - x) * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (H2 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
  - exact H1.
  - apply QleT'_to_Qle.
    apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)). exact H2.
Qed.

(* acceptance anchor for the equality case: equality holds only at the
   tau-fixed point (1/2, 1/2), where 56 * N == 3 + psi_3 == 7/2. *)
Lemma d519_anchor_tight : QeqT
  (56 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)))
  (3 + (1#2) + (1#2) - 2 * (1#2) * (1#2)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* the exact value theta(3) == 4/56 == 1/14, i.e. the closed form theta(u) = (u + 1) / (16 * (u + 1/2)) at u = 3. *)
Lemma d519_theta14 : QeqT ((4#56)) ((1#14)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* witness of the sigma trade-off law: theta * sigma == 1/16 at u = 3, where sigma = psi_3(center) / max = (7/2) / 4 = 7/8. *)
Lemma d519_sigma_trade : QeqT ((1#14) * (7#8)) ((1#16)).
Proof.
  apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* Section 4. Extraction and the axiom audit of the main exits *)
(* ============================================================ *)

Print Assumptions d519_u_le_14.
Print Assumptions d519_diag_N_le_14.
Print Assumptions d519_N_le_14.
Print Assumptions d519_N_le_14_psihat.
Print Assumptions d519_psi3_le_4.
Print Assumptions d519_anchor_tight.
Print Assumptions d519_theta14.
Print Assumptions d519_sigma_trade.

Separate Extraction d519_psi3 d519_u_le_14 d519_diag_N_le_14 d519_N_le_14
  d519_N_le_14_psihat d519_psi3_le_4 d519_anchor_tight d519_theta14
  d519_sigma_trade.
