(* ConstructiveWorld-Set -- abl_dmw2_pointwise_sharp: pointwise control face of the Beukers
   1979 zeta(2) integrand family, sharpened-constant re-cast (constructive, Set-carried). *)
(** * abl_dmw2_pointwise_sharp: sharpened pointwise control (Set-carried).
    Mission.  Sharpen the pointwise linear control constant of the Beukers 1979
    zeta(2) integrand family N := x * (1-x) * y * (1-y) from 10 (theta = 1/10) to 11
    (theta = 1/11, about 0.0909), nearing the true optimum ((sqrt(5)-1)/2)^5
    (about 0.09017).  Proved: (1) the main sharpened inequality 11*N <= 1 - x*y,
    via the substitution u = 1-x, v = 1-y with m = u+v, k = u*v, reduced to
    F = m - k * (12-11m+11k) with end term (m/16) * H(m), H(m) =
    16-48m+44m^2-11m^3 = 16-4m-11m*(2-m)^2, positive in both cases
    (m <= 4/5 and m >= 4/5, closed in-file by explicit certificates);
    (2) the square identity pair for 4*N <= (1-x*y)^2 (shape-isomorphic re-cast
    of the abl_z2_pointwise statement); (3) the composite
    4*11^n*N^(n+1) <= (1-x*y)^(n+2) (Set-carried): the integrand family is
    pointwise at most (1/4) * (1/11)^n.  Distance note (as-is): the bound
    serves downstream comparisons; (9/4) * (9/11)^m < 1 from m = 5 on (1/10
    version: m = 8); mu_lib drops from about 21.85 to about 11.95 against a
    true-optimum limit of about 11.52; the Rhin-Viola-type bound itself (the
    group-structure permutation double-integral method) is not yet in the
    library; this file is a pointwise preconditioning step toward it, without
    first-example or stronger-than claims.
    Dependencies.  Stdlib QArith/ZArith/Arith/Lia; S01_BaseRing (Id) and S02_CauchyComplete
    (QeqT/QleT'/QltT and bridges to Qeq/Qle; its Require line precedes the Stdlib line,
    keeping the Stdlib Qle_bool form); linear scaling by explicit lemma chains; nonlinear
    end term by explicit square decomposition; no reals, no classical logic.
    References.  Beukers 1979 (Bull. London Math. Soc. 11); Rhin-Viola
    group-structure method (classic).  Constructivity.  Purely constructive; no
    assumed constants, nothing left open; main statements carried on Set
    (dmw2_qle/QleT'/QeqT).  Build.  [rocq c -native-compiler no -q -Q . ""
    abl_dmw2_pointwise_sharp.v] on Rocq 9.1.0 (-Q root holds S01/S02 .vo). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Open Scope Q_scope.

(* ============================================================ *)
(* S0. Set-level self-carried base: identity type dmw2_id and order witness dmw2_qle. *)
(* ============================================================ *)

Inductive dmw2_id (A : Set) (x : A) : A -> Set :=
  dmw2_idrefl : dmw2_id A x x.

Definition dmw2_qle (x y : Q) : Set := dmw2_id bool (Qle_bool x y) true.

Lemma dmw2_0_le_1 : QleT' 0 1.
Proof. apply Qle_to_QleT'. exact (proj1 (Qle_bool_iff 0 1) eq_refl). Qed.

Lemma dmw2_qle_of_Qle : forall x y : Q, x <= y -> dmw2_qle x y.
Proof.
  intros x y H.
  assert (Hb : Qle_bool x y = true) by exact (proj2 (Qle_bool_iff x y) H).
  unfold dmw2_qle. rewrite Hb. apply dmw2_idrefl.
Qed.

Lemma dmw2_qle_to_Qle : forall x y : Q, dmw2_qle x y -> x <= y.
Proof.
  intros x y H. apply (proj1 (Qle_bool_iff x y)).
  destruct H. reflexivity.
Qed.

Lemma dmw2_qeq_imp_le : forall x y : Q, x == y -> QleT' y x.
Proof.
  intros x y Hxy.
  assert (Hcore : y <= x).
  { unfold Qle. unfold Qeq in Hxy.
    rewrite Hxy. apply Z.le_refl. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_le_eq_swap : forall a b : Q, a == b -> 0 <= a -> QleT' a b.
Proof.
  intros a b Hab Ha.
  apply (dmw2_qeq_imp_le b a).
  apply Qeq_sym. exact Hab.
Qed.

Lemma dmw2_le_eq : forall a b : Q, a == b -> QleT' a b.
Proof.
  intros a b Hab.
  apply (dmw2_qeq_imp_le b a). apply Qeq_sym. exact Hab.
Qed.

Lemma dmw2_ge0_wd : forall a b : Q, a == b -> 0 <= a -> QleT' 0 b.
Proof.
  intros a b Hab Ha.
  apply Qle_to_QleT'.
  apply (Qle_trans 0 a b).
  - exact Ha.
  - apply (QleT'_to_Qle a b). apply (dmw2_le_eq_swap a b); assumption.
Qed.

Lemma dmw2_qle_wd_l : forall x y z : Q, x == y -> dmw2_qle x z -> dmw2_qle y z.
Proof.
  intros x y z Hxy Hxz. apply dmw2_qle_of_Qle.
  apply (Qle_trans y x z)
  ; [ apply (QleT'_to_Qle y x); apply dmw2_qeq_imp_le; exact Hxy
    | apply dmw2_qle_to_Qle; exact Hxz ].
Qed.

Lemma dmw2_qle_wd_r : forall x y z : Q, y == z -> dmw2_qle x y -> dmw2_qle x z.
Proof.
  intros x y z Hyz Hxy. apply dmw2_qle_of_Qle.
  apply (Qle_trans x y z)
  ; [ apply dmw2_qle_to_Qle; exact Hxy
    | apply QleT'_to_Qle; apply (dmw2_qeq_imp_le z y); apply Qeq_sym; exact Hyz ].
Qed.

(* ============================================================ *)
(* A. Atomic linear-scaling library (explicit lemma chains only, no automation). *)
(* ============================================================ *)

Lemma dmw2_add_ge0_le : forall a b : Q, 0 <= b -> QleT' a (a + b).
Proof.
  intros a b H.
  assert (Hcore : a <= a + b).
  { apply (Qle_trans a (a + 0) (a + b)).
    - rewrite Qplus_0_r. apply Qle_refl.
    - apply (Qplus_le_compat a a 0 b); [ apply Qle_refl | exact H ]. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_sub_ge0 : forall a b : Q, 0 <= b - a -> QleT' a b.
Proof.
  intros a b H.
  assert (Hcore : a <= b).
  { apply (Qle_trans a (a + (b - a)) b).
    - apply (QleT'_to_Qle a (a + (b - a))). apply dmw2_add_ge0_le. exact H.
    - assert (Heq : a + (b - a) == b) by ring.
      rewrite Heq. apply Qle_refl. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_le_sub : forall a b : Q, a <= b -> QleT' 0 (b - a).
Proof.
  intros a b H.
  assert (Hcore : 0 <= b - a).
  { assert (H1 : a + (- a) <= b + (- a))
      by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
    assert (Heq1 : a + (- a) == 0) by ring.
    assert (Heq2 : b + (- a) == b - a) by ring.
    rewrite Heq1, Heq2 in H1. exact H1. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_minus_ge0 : forall t c : Q, 0 <= t -> QleT' (c - t) c.
Proof.
  intros t c H.
  assert (Hcore : c - t <= c).
  { apply (QleT'_to_Qle (c - t) c). apply (dmw2_sub_ge0 (c - t) c).
    assert (Heq : c - (c - t) == t) by ring.
    rewrite Heq. exact H. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_le0_opp : forall s : Q, s <= 0 -> QleT' 0 (- s).
Proof.
  intros s H.
  assert (Hcore : 0 <= - s).
  { assert (H1 : s + (- s) <= 0 + (- s))
      by (apply Qplus_le_compat; [ exact H | apply Qle_refl ]).
    assert (Heq1 : s + (- s) == 0) by ring.
    assert (Heq2 : 0 + (- s) == - s) by ring.
    rewrite Heq1, Heq2 in H1. exact H1. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_minus_le : forall p q r : Q, q <= r -> QleT' (p - r) (p - q).
Proof.
  intros p q r H.
  assert (Hcore : p - r <= p - q).
  { apply (QleT'_to_Qle (p - r) (p - q)). apply (dmw2_sub_ge0 (p - r) (p - q)).
    assert (Heq : (p - q) - (p - r) == r - q) by ring.
    rewrite Heq. apply (QleT'_to_Qle 0 (r - q)). apply (dmw2_le_sub q r). exact H. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_sq_ge0 : forall s : Q, QleT' 0 (s * s).
Proof.
  intro s.
  assert (Hcore : 0 <= s * s).
  { destruct (Qlt_le_dec 0 s) as [Hlt | Hle].
    - apply Qmult_le_0_compat
      ; [ apply Qlt_le_weak; exact Hlt | apply Qlt_le_weak; exact Hlt ].
    - assert (Hn : 0 <= - s)
        by (apply (QleT'_to_Qle 0 (- s)); apply dmw2_le0_opp; exact Hle).
      assert (Heq : s * s == (- s) * (- s)) by ring.
      rewrite Heq. apply Qmult_le_0_compat; exact Hn. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_mult2_ge0 : forall a b : Q, 0 <= a -> 0 <= b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb.
  assert (Hcore : 0 <= a * b) by (apply Qmult_le_0_compat; assumption).
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_mult4_ge0 : forall a b c d : Q,
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> QleT' 0 (((a * b) * c) * d).
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (Hcore : 0 <= ((a * b) * c) * d).
  { apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat.
      + apply Qmult_le_0_compat; assumption.
      + exact Hc.
    - exact Hd. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_div_pos : forall a c : Q, 0 <= a * c -> 0 < c -> QleT' 0 a.
Proof.
  intros a c Hac Hc.
  assert (Hcore : 0 <= a).
  { destruct (Qlt_le_dec 0 a) as [Hlt | Hle].
    - apply Qlt_le_weak; exact Hlt.
    - destruct (Qlt_le_dec a 0) as [Hneg | Hzero].
      + exfalso.
        pose proof (Qmult_lt_compat_r a 0 c Hc Hneg) as Hbad.
        assert (Heq : 0 * c == 0) by ring.
        rewrite Heq in Hbad.
        exact (Qlt_not_le (a * c) 0 Hbad Hac).
      + assert (Ha0 : a == 0) by (apply Qle_antisym; assumption).
        rewrite Ha0. apply Qle_refl. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Fixpoint dmw2_pow (t : Q) (k : nat) : Q :=
  match k with
  | O => 1
  | Datatypes.S k' => t * dmw2_pow t k'
  end.

Lemma dmw2_pow_ge0 : forall (t : Q) (k : nat), 0 <= t -> QleT' 0 (dmw2_pow t k).
Proof.
  intros t k Ht.
  assert (Hcore : 0 <= dmw2_pow t k).
  { induction k as [| k' IH].
    - simpl. exact (QleT'_to_Qle 0 1 dmw2_0_le_1).
    - simpl. apply Qmult_le_0_compat; [ exact Ht | exact IH ]. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_xy_le_1 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> QleT' (x * y) 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2.
  assert (Hcore : x * y <= 1).
  { apply (Qle_trans (x * y) (1 * 1) 1).
    - apply (Qmult_le_compat_nonneg x 1 y 1)
      ; [ split; assumption | split; assumption ].
    - assert (Heq : 1 * 1 == 1) by ring.
      rewrite Heq. apply Qle_refl. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_qmake_pos : forall (a : Z) (b : positive),
  (0 <= a)%Z -> QleT' 0 (a # b)%Q.
Proof.
  intros a b Ha.
  assert (Hcore : 0 <= (a # b)%Q) by (unfold Qle; simpl; lia).
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_nat_pos : forall n : nat, QleT' 0 (Z.of_nat n # 1)%Q.
Proof.
  intro n.
  assert (Hcore : 0 <= (Z.of_nat n # 1)%Q).
  { apply (proj1 (Qle_bool_iff 0 (Z.of_nat n # 1))).
    destruct n as [| n']; reflexivity. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

Lemma dmw2_mono_pair : forall a b c d : Q,
  a <= b -> c <= d -> 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
  QleT' (c * a) (d * b).
Proof.
  intros a b c d Hab Hcd Ha Hb Hc Hd.
  assert (Hcore : c * a <= d * b).
  { apply (Qle_trans (c * a) (d * a) (d * b)).
    - apply (Qmult_le_compat_r c d a); [ exact Hcd | exact Ha ].
    - apply (Qmult_le_compat_nonneg d d a b)
      ; [ split; [ exact Hd | apply Qle_refl ] | split; [ exact Ha | exact Hab ] ]. }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

(* ============================================================ *)
(* B. Main sharpened inequality: 11*N <= 1 - x*y. *)
(* ============================================================ *)

(* Main sharpened inequality (substituted form): 0 <= u,v <= 1 implies
   11*u * (1-u) * v * (1-v) <= u+v-u*v.
   Certificate chain (m := u+v, k := u*v; F := m - k * (12-11m+11k)):
   F >= m - k * (12-11m+(11/4)m^2) >= m - (m^2/4) * (12-11m+(11/4)m^2)
     = (m/16) * H(m) >= 0,
   where B* = 12-11m+(11/4)m^2 = 1+(11/4) * (m-2)^2 >= 1 (positive definite,
   discriminant -11), and H(m) = 16-48m+44m^2-11m^3 = 16-4m-11m*(2-m)^2;
   case m <= 4/5: z := 4/5-m gives H = 16/125-(32/25)z+(88/5)z^2+11z^3,
   and dropping 11z^3 >= 0 the quadratic part is
   (8/125) * (275 * (z-2/55)^2+18/11) >= 144/1375 > 0;
   case m >= 4/5: s := m-4/5 in [0,6/5] gives
   H = 16/125+s*(32/25+11*s*(8/5-s)), bracket >= 32/25 > 0 (s <= 6/5 < 8/5),
   hence H >= 16/125 > 0. *)
Lemma dmw2_eleven_le_uv : forall u v : Q,
  0 <= u <= 1 -> 0 <= v <= 1 ->
  QleT' (11 * u * (1 - u) * v * (1 - v)) (u + v - u * v).
Proof.
  intros u v [Hu1 Hu2] [Hv1 Hv2].
  assert (Hcore : 11 * u * (1 - u) * v * (1 - v) <= u + v - u * v).
  {
  assert (Hk0 : 0 <= u * v)
    by (apply QleT'_to_Qle; apply dmw2_mult2_ge0; assumption).
  assert (Hm0 : 0 <= u + v).
  { apply (Qle_trans 0 (0 + 0) (u + v)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 u 0 v); assumption. }
  assert (Hm2 : (u + v) <= 2).
  { apply (Qle_trans (u + v) (1 + 1) 2).
    - apply (Qplus_le_compat u 1 v 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (H4k : 0 <= (u+v)*(u+v) - 4*(u*v)).
  { assert (Heq : (u+v)*(u+v) - 4*(u*v) == (u-v)*(u-v)) by ring.
    rewrite Heq. apply QleT'_to_Qle. apply dmw2_sq_ge0. }
(* Linear consequences of H4k: 11k <= (11/4) * m^2 and k <= m^2/4. *)
  assert (HBB : 11 * (u*v) <= (11#4)*(u+v)*(u+v)).
  { apply (Qle_trans (11 * (u*v))
      (11 * (u*v) + (11#4) * ((u+v)*(u+v) - 4*(u*v)))
      ((11#4)*(u+v)*(u+v))).
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
      apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (11#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 11 4); lia | exact H4k ].
    - assert (Heq : 11 * (u*v) + (11#4) * ((u+v)*(u+v) - 4*(u*v))
                 == (11#4)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 4); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
(* Factor bound: B* = 12-11m+(11/4)m^2 = 1+(11/4) * (m-2)^2 >= 1 > 0. *)
  assert (HBp : 0 <= 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)).
  { assert (Hid0 : 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)
                == (11#4)*((2-(u+v))*(2-(u+v))) + 1) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v)))
      by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
    assert (HX : 0 <= (11#4)*((2-(u+v))*(2-(u+v)))).
    { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (11#4) ((2-(u+v))*(2-(u+v))))
      ; [ apply QleT'_to_Qle; apply (dmw2_qmake_pos 11 4); lia | exact Hs ]. }
    apply (Qle_trans 0 ((11#4)*((2-(u+v))*(2-(u+v))))
                      ((11#4)*((2-(u+v))*(2-(u+v))) + 1)).
    - exact HX.
    - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
      exact (QleT'_to_Qle 0 1 dmw2_0_le_1). }
  assert (HBs : 12 - 11*(u+v) + 11*(u*v)
             <= 12 - 11*(u+v) + (11#4)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (12 - 11*(u+v)) (12 - 11*(u+v))
             (11*(u*v)) ((11#4)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
(* Step 1: k*B <= k*B*. *)
  assert (HkBB : (u*v) * (12 - 11*(u+v) + 11*(u*v))
              <= (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (12 - 11*(u+v) + 11*(u*v))
                  (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (12 - 11*(u+v) + 11*(u*v))
                == (12 - 11*(u+v) + 11*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
                == (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
(* Step 2: k*B* <= (m^2/4) * B*. *)
  assert (HkB2 : (u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
(* Univariate end term nonnegative (cases m <= 4/5 and m >= 4/5). *)
  assert (Hlow : 0 <= ((u+v) * (1#16))
                   * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v))).
  { destruct (Qlt_le_dec (u+v) (4#5)) as [Hm45 | Hm45].
    - (* Case 1 (m <= 4/5): z = 4/5-m, H = 16/125-(32/25)z+(88/5)z^2+11z^3. *)
      assert (Hz0 : 0 <= (4#5) - (u+v))
        by (apply QleT'_to_Qle; apply (dmw2_le_sub (u+v) (4#5));
          exact (Qlt_le_weak _ _ Hm45)).
      assert (HidB : 16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)
                  == (16#125) - (32#25)*((4#5)-(u+v))
                     + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                     + 11*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v))))
        by ring.
      assert (Hcube0 : 0 <= (((4#5)-(u+v))*((4#5)-(u+v)))*((4#5)-(u+v))).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply dmw2_sq_ge0.
        - exact Hz0. }
      assert (Hcube : 0 <= 11*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v)))).
      { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 11)
        ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 11) | exact Hcube0 ]. }
      assert (Hsq : 0 <= (((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55)))
        by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
      assert (Hin : 0 <= (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))).
      { assert (Hasso : (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))
                     == (275)*((((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))))
          by ring.
        rewrite Hasso.
        apply QleT'_to_Qle.
        apply (dmw2_mult2_ge0 (275) ((((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))))
        ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 275) | exact Hsq ]. }
      assert (Hin2 : 0 <= (275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))
                          + (18#11)).
      { apply (Qle_trans 0
                 ((275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55))) _).
        - exact Hin.
        - apply QleT'_to_Qle.
          apply (dmw2_add_ge0_le
                   ((275)*(((4#5)-(u+v))-(2#55))*(((4#5)-(u+v))-(2#55)))
                   (18#11)).
          apply QleT'_to_Qle. apply (dmw2_qmake_pos 18 11); lia. }
      assert (Hquad : 0 <= (16#125) - (32#25)*((4#5)-(u+v))
                           + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))).
      { assert (Hsos : (16#125) - (32#25)*((4#5)-(u+v))
                           + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                    == (8#125)*((275)*(((4#5)-(u+v))-(2#55))
                                          *(((4#5)-(u+v))-(2#55)) + (18#11)))
          by ring.
        rewrite Hsos.
        apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply (dmw2_qmake_pos 8 125); lia.
        - exact Hin2. }
      assert (HH : 0 <= 16 - 48*(u+v) + 44*(u+v)*(u+v)
                        - 11*(u+v)*(u+v)*(u+v)).
      { rewrite HidB.
        apply (Qle_trans _ ((16#125) - (32#25)*((4#5)-(u+v))
                 + (88#5)*(((4#5)-(u+v))*((4#5)-(u+v))))).
        - exact Hquad.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact Hcube. }
      apply Qmult_le_0_compat.
      + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH.
    - (* Case 2 (m >= 4/5): s = m-4/5 in [0,6/5], H = 16/125 + s * (32/25 + 11*s*(8/5-s)) >= 16/125 > 0. *)
      assert (Hs0 : 0 <= (u+v) - (4#5))
        by (apply QleT'_to_Qle; apply (dmw2_le_sub (4#5) (u+v)); exact Hm45).
      assert (Hs2 : (u+v) - (4#5) <= (6#5)).
      { apply QleT'_to_Qle. apply (dmw2_sub_ge0 ((u+v)-(4#5)) (6#5)).
        assert (Heq : (6#5) - ((u+v)-(4#5)) == 2 - (u+v)) by ring.
        rewrite Heq. apply QleT'_to_Qle. apply (dmw2_le_sub (u+v) 2). exact Hm2. }
      assert (Hs8 : (u+v) - (4#5) <= (8#5))
        by (apply (Qle_trans _ (6#5)); [ exact Hs2
          | unfold Qle; simpl; lia ]).
      assert (Hbr : 0 <= (8#5) - ((u+v)-(4#5)))
        by (apply QleT'_to_Qle; apply (dmw2_le_sub ((u+v)-(4#5)) (8#5)); exact Hs8).
      assert (Hbrk : 0 <= (32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))).
      { apply (Qle_trans 0 (32#25) _).
        - apply QleT'_to_Qle. apply (dmw2_qmake_pos 32 25); lia.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le.
          assert (Hasso : 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))
                       == 11*(((u+v)-(4#5))*((8#5)-((u+v)-(4#5))))) by ring.
          rewrite Hasso.
          apply QleT'_to_Qle. apply (dmw2_mult2_ge0 11).
          + apply QleT'_to_Qle. apply (dmw2_nat_pos 11).
          + apply QleT'_to_Qle.
            apply (dmw2_mult2_ge0 ((u+v)-(4#5)) ((8#5)-((u+v)-(4#5))))
            ; [ exact Hs0 | exact Hbr ]. }
      assert (HidA : 16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)
                  == (16#125) + ((u+v)-(4#5))
                       *((32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5)))))
        by ring.
      assert (Hterm : 0 <= ((u+v)-(4#5))
                       *((32#25) + 11*((u+v)-(4#5))*((8#5)-((u+v)-(4#5))))).
      { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((u+v)-(4#5)))
        ; [ exact Hs0 | exact Hbrk ]. }
      assert (HH : 0 <= 16 - 48*(u+v) + 44*(u+v)*(u+v)
                        - 11*(u+v)*(u+v)*(u+v)).
      { rewrite HidA.
        apply (Qle_trans 0 (16#125) _).
        - apply QleT'_to_Qle. apply (dmw2_qmake_pos 16 125); lia.
        - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact Hterm. }
      apply Qmult_le_0_compat.
      + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply QleT'_to_Qle; apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH. }
(* Chained composition: 0 <= (m/16) * H = m-(m^2/4) * B* <= m-k*B* <= m-k*B = F. *)
  assert (Hid2 : (u+v) - (((u+v)*(u+v)) * (1#4))
                       * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))
              == ((u+v) * (1#16))
                   * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)))
    by ring.
  assert (HF : 0 <= u + v - u*v - 11*u*(1-u)*v*(1-v)).
  { assert (HeqF : u + v - u*v - 11*u*(1-u)*v*(1-v)
                == (u+v) - (u*v)*(12 - 11*(u+v) + 11*(u*v))) by ring.
    rewrite HeqF.
    apply (Qle_trans _ (((u+v) * (1#16))
              * (16 - 48*(u+v) + 44*(u+v)*(u+v) - 11*(u+v)*(u+v)*(u+v)))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ ((u+v) - (u*v)*(12 - 11*(u+v) + (11#4)*(u+v)*(u+v)))).
      + apply QleT'_to_Qle.
        apply (dmw2_minus_le (u+v)
          ((u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply QleT'_to_Qle.
        apply (dmw2_minus_le (u+v)
          ((u*v) * (12 - 11*(u+v) + 11*(u*v)))
          ((u*v) * (12 - 11*(u+v) + (11#4)*(u+v)*(u+v))))
        ; exact HkBB. }
(* Conclusion: u+v-u*v = 11*N + F >= 11*N. *)
  apply (Qle_trans (11*u*(1-u)*v*(1-v))
    (11*u*(1-u)*v*(1-v) + (u + v - u*v - 11*u*(1-u)*v*(1-v)))
    (u + v - u*v)).
  - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact HF.
  - assert (HeqG : 11*u*(1-u)*v*(1-v)
                 + (u + v - u*v - 11*u*(1-u)*v*(1-v))
                == u + v - u*v) by ring.
    rewrite HeqG. apply Qle_refl.
  }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

(* Main sharpened inequality (original variables, Set-carried): 0 <= x,y <= 1 implies 11*N <= 1-x*y. *)
Theorem dmw2_eleven_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  dmw2_qle (11 * x * (1 - x) * y * (1 - y)) (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hu1 : 0 <= 1 - x)
    by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hu2 : (1 - x) <= 1)
    by (apply QleT'_to_Qle; apply (dmw2_minus_ge0 x 1); exact Hx1).
  assert (Hv1 : 0 <= 1 - y)
    by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hv2 : (1 - y) <= 1)
    by (apply QleT'_to_Qle; apply (dmw2_minus_ge0 y 1); exact Hy1).
  pose proof (dmw2_eleven_le_uv (1 - x) (1 - y) (conj Hu1 Hu2) (conj Hv1 Hv2)) as H.
  assert (Hl : 11 * x * (1 - x) * y * (1 - y)
            == 11 * (1 - x) * x * (1 - y) * y) by ring.
  assert (Hr : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  assert (Hn : 11 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
            == 11 * x * (1 - x) * y * (1 - y)) by ring.
  apply (dmw2_qle_wd_r (11 * x * (1 - x) * y * (1 - y))
            ((1 - x) + (1 - y) - (1 - x) * (1 - y)) (1 - x * y)).
  - exact Hr.
  - apply (dmw2_qle_wd_l (11 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                        (11 * x * (1 - x) * y * (1 - y))
                        ((1 - x) + (1 - y) - (1 - x) * (1 - y))).
    + exact Hn.
    + apply dmw2_qle_of_Qle. apply QleT'_to_Qle. exact H.
Qed.

(* Numerical anchor 1: at u = v = 1/2, 11*N = 11/16. *)
Lemma dmw2_anchor_main_uv :
  QeqT (11 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2))) (11#16).
Proof.
  assert (Hcore : 11 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)) == (11#16))
    by (vm_compute; reflexivity).
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* ============================================================ *)
(* C. Square identity pair and 4*N <= (1-x*y)^2 (constant-independent; shape-isomorphic re-cast of the abl_z2_pointwise statement). *)
(* ============================================================ *)

Lemma dmw2_amgm_eq_l : forall x y : Q,
  QeqT ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y))
       ((1 - 2*x + x*y)*(1 - 2*x + x*y)).
Proof.
  intros x y.
  assert (Hcore : (1 - x*y)*(1 - x*y) - 4*x*(1-x)*(1-y)
               == (1 - 2*x + x*y)*(1 - 2*x + x*y)) by ring.
  apply qeq_imp_qeqT. exact Hcore.
Qed.

Lemma dmw2_amgm_eq_r : forall x y : Q,
  QeqT ((1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y))
       ((1 - 2*y + x*y)*(1 - 2*y + x*y)).
Proof.
  intros x y.
  assert (Hcore : (1 - x*y)*(1 - x*y) - 4*(1-x)*y*(1-y)
               == (1 - 2*y + x*y)*(1 - 2*y + x*y)) by ring.
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* Composite statement: 0 <= x,y <= 1 implies 4*N <= (1-x*y)^2.
   The two identities give P >= A and P >= B (P = (1-x*y)^2,
   A = 4*x * (1-x) * (1-y), B = 4 * (1-x) * y * (1-y)); multiplying gives
   P^2 >= A*B; moreover A*B-Q^2 = 16*x*y * (1-x)^2 * (1-y)^2 * (1-x*y) >= 0
   (Q = 4*N), so P^2 >= Q^2; from P,Q >= 0 and P+Q > 0 (or the degenerate
   case P+Q <= 0) one gets P >= Q. *)
Lemma dmw2_N4_le_dsq : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (4 * x * (1 - x) * y * (1 - y)) ((1 - x*y)*(1 - x*y)).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hcore : 4 * x * (1 - x) * y * (1 - y) <= (1 - x*y)*(1 - x*y)).
  {
  assert (Hxb : 0 <= 1 - x)
    by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y)
    by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
  assert (HN0 : 0 <= 4 * x * (1 - x) * y * (1 - y)).
  { apply QleT'_to_Qle.
    apply (dmw2_mult2_ge0 ((4 * x * (1 - x)) * y) (1 - y)).
    - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (4 * x * (1 - x)) y).
      + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (4 * x) (1 - x)).
        * apply QleT'_to_Qle. apply (dmw2_mult2_ge0 4 x)
          ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 4) | exact Hx1 ].
        * exact Hxb.
      + exact Hy1.
    - exact Hyb. }
  assert (HP : 0 <= (1 - x*y)*(1 - x*y))
    by (apply QleT'_to_Qle; apply dmw2_sq_ge0).
  pose proof (QleT'_to_Qle _ _ (dmw2_sq_ge0 (1 - 2*x + x*y))) as HAl.
  rewrite <- (qeqT_imp_qeq _ _ (dmw2_amgm_eq_l x y)) in HAl.
  pose proof (QleT'_to_Qle _ _ (dmw2_sq_ge0 (1 - 2*y + x*y))) as HAr.
  rewrite <- (qeqT_imp_qeq _ _ (dmw2_amgm_eq_r x y)) in HAr.
  assert (Hm1 : 4*x*(1-x)*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply QleT'_to_Qle; apply (dmw2_sub_ge0 (4*x*(1-x)*(1-y))); exact HAl).
  assert (Hm2 : 4*(1-x)*y*(1-y) <= (1 - x*y)*(1 - x*y))
    by (apply QleT'_to_Qle; apply (dmw2_sub_ge0 (4*(1-x)*y*(1-y))); exact HAr).
  assert (HPP : (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))
             <= ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))).
  { apply Qmult_le_compat_r; [ exact Hm1 | exact HP ]. }
  assert (HNA : 0 <= 4*x*(1-x)*(1-y)).
  { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (4*x*(1-x)) (1-y)).
    - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (4*x) (1-x)).
      + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 4 x)
        ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 4) | exact Hx1 ].
      + exact Hxb.
    - exact Hyb. }
  assert (HAA : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             <= (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))).
  { apply (Qle_trans _ ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
    - apply QleT'_to_Qle.
      apply (dmw2_le_eq ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y)))).
      assert (Hcmm : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                  == (4*(1-x)*y*(1-y)) * (4*x*(1-x)*(1-y))) by ring.
      exact Hcmm.
    - apply (Qle_trans _ (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))).
      + apply (Qmult_le_compat_r (4*(1-x)*y*(1-y)) ((1 - x*y)*(1 - x*y))
               (4*x*(1-x)*(1-y)))
        ; [ exact Hm2 | exact HNA ].
      + apply QleT'_to_Qle.
        apply (dmw2_le_eq (((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y)))
                         ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
        assert (Hcmm2 : ((1 - x*y)*(1 - x*y)) * (4*x*(1-x)*(1-y))
                     == (4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y))) by ring.
        exact Hcmm2. }
  assert (Hqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
             >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply QleT'_to_Qle.
    apply (dmw2_sub_ge0 ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))).
    assert (Heqq : (4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))
              == (4*x*(1-x)*(1-y)) * (4*y*(1-x)*(1-y)*(1-x*y))) by ring.
    rewrite Heqq.
    apply Qmult_le_0_compat.
    - apply QleT'_to_Qle. apply (dmw2_mult4_ge0 4 x (1-x) (1-y))
      ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 4)
        | exact Hx1 | exact Hxb | exact Hyb ].
    - apply Qmult_le_0_compat.
      + apply QleT'_to_Qle. apply (dmw2_mult4_ge0 4 y (1-x) (1-y))
        ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 4)
          | exact Hy1 | exact Hxb | exact Hyb ].
      + apply QleT'_to_Qle. apply (dmw2_le_sub (x*y) 1).
        apply QleT'_to_Qle. apply (dmw2_xy_le_1 x y); assumption. }
  assert (HPPQ : ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
              >= (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))).
  { apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                     ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))
                     (((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y)))).
    - apply (Qle_trans ((4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * (4*(1-x)*y*(1-y)))
                       ((4*x*(1-x)*(1-y)) * ((1 - x*y)*(1 - x*y)))).
      + exact Hqq.
      + exact HAA.
    - exact HPP. }
  destruct (Qlt_le_dec 0
    ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))) as [Hpos | Hzero].
  - assert (Hdiff : 0 <= ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                       * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))).
    { assert (Heqd : ((1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y))
                   * ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y))
                == ((1 - x*y)*(1 - x*y)) * ((1 - x*y)*(1 - x*y))
                 - (4*x*(1-x)*y*(1-y)) * (4*x*(1-x)*y*(1-y))) by ring.
      rewrite Heqd. exact (QleT'_to_Qle _ _ (dmw2_le_sub _ _ HPPQ)). }
    assert (Hres : 0 <= (1 - x*y)*(1 - x*y) - 4*x*(1-x)*y*(1-y)).
    { apply QleT'_to_Qle.
      apply (dmw2_div_pos _ ((1 - x*y)*(1 - x*y) + 4*x*(1-x)*y*(1-y)))
      ; assumption. }
    exact (QleT'_to_Qle _ _ (dmw2_sub_ge0 _ _ Hres)).
  - assert (HQle : (4*x*(1-x)*y*(1-y)) <= 0).
    { assert (Hcq : (4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)
                 == (1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y))) by ring.
      apply (Qle_trans (4*x*(1-x)*y*(1-y))
               ((4*x*(1-x)*y*(1-y)) + (1 - x*y)*(1 - x*y)) 0).
      - apply QleT'_to_Qle. apply dmw2_add_ge0_le. exact HP.
      - apply (Qle_trans _ ((1 - x*y)*(1 - x*y) + (4*x*(1-x)*y*(1-y)))).
        + apply QleT'_to_Qle. apply (dmw2_le_eq _ _). exact Hcq.
        + exact Hzero. }
    assert (Heq : (4*x*(1-x)*y*(1-y)) == 0) by (apply Qle_antisym; assumption).
    rewrite Heq. exact HP.
  }
  exact (Qle_to_QleT' _ _ Hcore).
Qed.

(* ============================================================ *)
(* D. Composite statement: 4*11^n*N^(n+1) <= (1-x*y)^(n+2) (division-free form, Set-carried). *)
(* ============================================================ *)

(* Inductive composition: the base case is C; the step case multiplies by
   N <= (1-x*y)/11 (the B main sharpened inequality) and then by (1-x*y).
   This is the division-free form of the pointwise family bound
   (1/4) * (1/11)^n (a sharpened re-cast of the 1/10 version). *)
Theorem dmw2_pointwise_decay : forall (n : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  dmw2_qle (4 * dmw2_pow 11 n * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
          (dmw2_pow (1 - x*y) (Datatypes.S (Datatypes.S n))).
Proof.
  induction n as [| n IH]; intros x y [Hx1 Hx2] [Hy1 Hy2].
  - apply dmw2_qle_of_Qle.
    assert (Heq1 : 4 * dmw2_pow 11 0 * dmw2_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (simpl; ring).
    assert (Heq2 : dmw2_pow (1 - x*y) 2 == ((1 - x*y)*(1 - x*y)))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    apply QleT'_to_Qle. apply dmw2_N4_le_dsq
      ; [ split; assumption | split; assumption ].
  - apply dmw2_qle_of_Qle.
    assert (HIH := IH x y (conj Hx1 Hx2) (conj Hy1 Hy2)).
    apply dmw2_qle_to_Qle in HIH.
    pose proof (dmw2_eleven_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hten.
    apply dmw2_qle_to_Qle in Hten.
    assert (Hxy1 : 0 <= x*y)
      by (apply QleT'_to_Qle; apply dmw2_mult2_ge0; assumption).
    assert (HP0 : 0 <= dmw2_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
      by (apply QleT'_to_Qle; apply dmw2_pow_ge0; apply QleT'_to_Qle;
        apply (dmw2_le_sub (x*y) 1); apply QleT'_to_Qle;
        apply (dmw2_xy_le_1 x y); assumption).
    assert (Hxb : 0 <= 1 - x)
      by (apply QleT'_to_Qle; apply (dmw2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y)
      by (apply QleT'_to_Qle; apply (dmw2_le_sub y 1); exact Hy2).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply QleT'_to_Qle; apply (dmw2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (H4N : 0 <= (4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n)).
    { apply QleT'_to_Qle.
      apply (dmw2_mult2_ge0 (4 * dmw2_pow 11 n) (dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))).
      - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 4 (dmw2_pow 11 n))
        ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 4)
          | apply QleT'_to_Qle; apply dmw2_pow_ge0
          ; exact (QleT'_to_Qle _ _ (dmw2_nat_pos 11)) ].
      - apply QleT'_to_Qle. apply dmw2_pow_ge0. exact HN0. }
    assert (HPn : 0 <= 1 - x*y)
      by (apply QleT'_to_Qle; apply (dmw2_le_sub (x*y) 1); apply QleT'_to_Qle;
        apply (dmw2_xy_le_1 x y); assumption).
    assert (HN11 : 0 <= ((11 * x * (1 - x)) * y) * (1 - y)).
    { apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((11 * x * (1 - x)) * y) (1 - y)).
      - apply QleT'_to_Qle. apply (dmw2_mult2_ge0 ((11 * x) * (1 - x)) y).
        + apply QleT'_to_Qle. apply (dmw2_mult2_ge0 (11 * x) (1 - x)).
          * apply QleT'_to_Qle. apply (dmw2_mult2_ge0 11 x)
            ; [ apply QleT'_to_Qle; apply (dmw2_nat_pos 11) | exact Hx1 ].
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    apply (Qle_trans (4 * dmw2_pow 11 (Datatypes.S n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S (Datatypes.S n)))
                     (11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n)))
                     ((1 - x*y) * dmw2_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))).
    + apply QleT'_to_Qle.
      apply (dmw2_le_eq (4 * dmw2_pow 11 (Datatypes.S n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S (Datatypes.S n)))
                       (11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n)))).
      assert (Hrw : 4 * dmw2_pow 11 (Datatypes.S n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S (Datatypes.S n))
                 == 11 * x * (1 - x) * y * (1 - y) * ((4 * dmw2_pow 11 n) * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n)))
        by (simpl; ring).
      exact Hrw.
    + apply QleT'_to_Qle.
      apply (dmw2_mono_pair (4 * dmw2_pow 11 n * dmw2_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
                           (dmw2_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
                           _ (1 - x*y))
      ; [ exact HIH | exact Hten | exact H4N | exact HP0 | exact HN11 | exact HPn ].
Qed.

(* Numerical anchor 2: at n = 1, x = y = 1/2, the composite left side is 4*11*N^2 = 44/256. *)
Lemma dmw2_anchor_decay_n1 :
  QeqT (4 * dmw2_pow 11 1
        * dmw2_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2) (44#256).
Proof.
  assert (Hcore : 4 * dmw2_pow 11 1
                       * dmw2_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2
                  == (44#256)) by (vm_compute; reflexivity).
  apply qeq_imp_qeqT. exact Hcore.
Qed.

(* ============================================================ *)
(* E. Tail section: closedness self-check of the main statements. *)
(* ============================================================ *)

Print Assumptions dmw2_eleven_le_uv.
Print Assumptions dmw2_eleven_le.
Print Assumptions dmw2_N4_le_dsq.
Print Assumptions dmw2_pointwise_decay.
Print Assumptions dmw2_anchor_main_uv.
Print Assumptions dmw2_anchor_decay_n1.
