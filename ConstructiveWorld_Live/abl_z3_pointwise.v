(* ConstructiveWorld-Set — zeta(2) double-integral estimate modules. *)

(** * abl_z3_pointwise: three-variable pointwise control for the Beukers
    zeta(3) integrand family.

    Mission.  Pointwise exponential control for the integrand family of
      the Beukers 1979 zeta(3) irrationality triple integral: writing
      N := x(1-x)y(1-y)z(1-z) and T := 1-xyz on the closed cube
      0 <= x,y,z <= 1, proves the square control 4N <= T^2
      ([zb3_N_le_Tsq]), the linear control 40N <= T, and the
      division-free composite 4 * 40^m * N^(m+1) <= T^(m+2)
      ([zb3_pointwise_decay]); [zb3_4zz_le_1] and [zb3_sq_id] carry
      the chains.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith],
      [Arith.Arith], [Lia]; requires [abl_z2_pointwise] of this
      development ([zb2_qle], the linear atoms, the main inequality).

    References.  The baseline module abl_z3_pointwise.v in
      ConstructiveWorld-Main (statement names carried over verbatim);
      the pointwise step of Beukers 1979 (Bull. London Math. Soc. 11)
      for the zeta(3) family.

    Constructivity.  All statements are carried by [Set] via
      [zb2_qle]; nonlinear inequalities go by explicit square
      decompositions; extraction has [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_z3_pointwise.v]
      compiles cleanly (exit 0); the artifact begins [436f7121 00015ff4]. *)


From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Require Import abl_z2_pointwise.
Require Import S02_CauchyComplete (QleT', QeqT, Qle_to_QleT', QleT'_to_Qle, qeq_imp_qeqT, qeqT_imp_qeq).

Open Scope Q_scope.

(* ================= Section A. Single variable: 4 * z(1-z) <= 1 ================= *)

(* Square decomposition: 1 - 4z(1-z) = (2z-1)^2 >= 0. *)
Lemma zb3_4zz_le_1 : forall z : Q, zb2_qle (4 * z * (1 - z)) 1.
Proof.
  intro z.
  assert (Hs : 0 <= (2 * z - 1) * (2 * z - 1))
    by (apply zb2_qle_to_Qle; apply zb2_sq_ge0).
  assert (Heq2 : 4 * z * (1 - z) == 1 - (2 * z - 1) * (2 * z - 1)) by ring.
  apply (zb2_qle_wd_l (1 - (2 * z - 1) * (2 * z - 1)) (4 * z * (1 - z)) 1).
  - symmetry. exact Heq2.
  - apply (zb2_minus_ge0 ((2 * z - 1) * (2 * z - 1)) 1 Hs).
Qed.

(* ================= Section B. Two variables: (1-x)(1-y) <= 1-xy ================= *)

Lemma zb3_11xy_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' ((1 - x) * (1 - y)) (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  apply Qle_to_QleT'.
  assert (Hxb : 0 <= 1 - x) by (apply zb2_qle_to_Qle; apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply zb2_qle_to_Qle; apply (zb2_le_sub y 1); exact Hy2).
  assert (HA : 0 <= x * (1 - y)) by (apply zb2_qle_to_Qle; apply zb2_mult2_ge0; assumption).
  assert (HB : 0 <= y * (1 - x)) by (apply zb2_qle_to_Qle; apply zb2_mult2_ge0; assumption).
  assert (Hr : 1 - x * y - ((1 - x) * (1 - y)) == x * (1 - y) + y * (1 - x)) by ring.
  apply zb2_qle_to_Qle.
  apply (zb2_sub_ge0 ((1 - x) * (1 - y)) (1 - x * y)).
  rewrite Hr.
  apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
  - exact HA.
  - apply zb2_qle_to_Qle. apply zb2_add_ge0_le. exact HB.
Qed.

(* ================= Section C. Square control: 4N <= T^2 ================= *)

(* Exact square identity: T^2 - 4xy(1-xy)(1-z) = (1-2xy+xyz)^2. *)
Lemma zb3_sq_id : forall x y z : Q,
  QeqT ((1 - x*y*z)*(1 - x*y*z) - 4*x*y*(1 - x*y)*(1 - z))
    ((1 - 2*x*y + x*y*z)*(1 - 2*x*y + x*y*z)).
Proof. intros x y z. apply qeq_imp_qeqT. ring. Qed.

Theorem zb3_N_le_Tsq : forall x y z : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  QleT' (4 * x * (1 - x) * y * (1 - y) * z * (1 - z))
    ((1 - x*y*z) * (1 - x*y*z)).
Proof.
  intros x y z [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
  apply Qle_to_QleT'.
  assert (Hxb : 0 <= 1 - x) by (apply zb2_qle_to_Qle; apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply zb2_qle_to_Qle; apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply zb2_qle_to_Qle; apply (zb2_le_sub z 1); exact Hz2).
  assert (Hfac2 : 0 <= x * y * (1 - x * y)).
  { assert (Hxy1 : x * y <= 1) by (apply zb2_qle_to_Qle; apply (zb2_xy_le_1 x y); assumption).
    apply (Qmult_le_0_compat (x * y) (1 - x * y)).
    - apply (Qmult_le_0_compat x y); assumption.
    - apply zb2_qle_to_Qle; apply (zb2_le_sub (x * y) 1); exact Hxy1. }
  assert (Hfac3 : 0 <= (1 - z) * (4 * x * y * (1 - x * y))).
  { apply (Qmult_le_0_compat (1 - z) (4 * x * y * (1 - x * y)))
    ; [ exact Hzb
      | apply zb2_qle_to_Qle; apply (zb2_mult4_ge0 4 x y (1 - x * y))
      ; [ apply zb2_qle_to_Qle; apply (zb2_nat_pos 4) | exact Hx1 | exact Hy1
        | apply zb2_qle_to_Qle; apply (zb2_le_sub (x * y) 1)
          ; apply zb2_qle_to_Qle; apply (zb2_xy_le_1 x y); assumption ] ]. }
(* Step one: (1-x)(1-y) <= 1-xy, right-multiplied by the nonnegative
      factor K = 4xyz(1-z). *)
  assert (Hstep1 : ((1 - x) * (1 - y)) * (4 * x * y * z * (1 - z))
                <= (1 - x * y) * (4 * x * y * z * (1 - z))).
  { pose proof (QleT'_to_Qle _ _ (zb3_11xy_le x y (conj Hx1 Hx2) (conj Hy1 Hy2))) as H11.
    apply (Qmult_le_compat_r ((1 - x) * (1 - y)) (1 - x * y)
                             (4 * x * y * z * (1 - z)) H11).
    apply (Qmult_le_0_compat (((4 * x) * y) * z) (1 - z)).
    - apply (Qmult_le_0_compat ((4 * x) * y) z).
      + apply (Qmult_le_0_compat (4 * x) y).
        * apply zb2_qle_to_Qle; apply (zb2_mult2_ge0 4 x); [ apply zb2_qle_to_Qle; apply (zb2_nat_pos 4) | exact Hx1 ].
        * exact Hy1.
      + exact Hz1.
    - exact Hzb. }
  assert (E1 : ((1 - x) * (1 - y)) * (4 * x * y * z * (1 - z))
            == 4 * x * (1 - x) * y * (1 - y) * z * (1 - z)) by ring.
  assert (HA : 4 * x * (1 - x) * y * (1 - y) * z * (1 - z)
            <= (1 - x * y) * (4 * x * y * z * (1 - z)))
    by (rewrite <- E1; exact Hstep1).
(* Step two: scaling by z <= 1 (after reshaping identities). *)
  assert (E2 : (1 - x * y) * (4 * x * y * z * (1 - z))
            == z * (1 - z) * (4 * x * y * (1 - x * y))) by ring.
  assert (HB : (1 - x * y) * (4 * x * y * z * (1 - z))
            <= (1 - z) * (4 * x * y * (1 - x * y))).
  { rewrite E2.
    assert (Hrw : z * (1 - z) * (4 * x * y * (1 - x * y))
               == z * ((1 - z) * (4 * x * y * (1 - x * y)))) by ring.
    rewrite Hrw.
    assert (Hrw2 : z * ((1 - z) * (4 * x * y * (1 - x * y)))
                <= 1 * ((1 - z) * (4 * x * y * (1 - x * y))))
      by (apply (Qmult_le_compat_r z 1 ((1 - z) * (4 * x * y * (1 - x * y))))
         ; [ exact Hz2 | exact Hfac3 ]).
    rewrite Qmult_1_l in Hrw2. exact Hrw2. }
(* Step three: the square identity 4xy(1-xy)(1-z) <= T^2. *)
  assert (E3 : (1 - z) * (4 * x * y * (1 - x * y))
            == 4 * x * y * (1 - x * y) * (1 - z)) by ring.
  assert (Hstep3 : 4 * x * y * (1 - x * y) * (1 - z)
                <= (1 - x*y*z) * (1 - x*y*z)).
  { apply (zb2_qle_to_Qle _ _).
    apply (zb2_sub_ge0 _ _).
    pose proof (zb2_sq_ge0 (1 - 2*x*y + x*y*z)) as Hsq.
    rewrite (qeqT_imp_qeq _ _ (zb3_sq_id x y z)).
    exact (zb2_qle_to_Qle _ _ Hsq). }
  assert (HC : (1 - z) * (4 * x * y * (1 - x * y))
            <= (1 - x*y*z) * (1 - x*y*z))
    by (rewrite E3; exact Hstep3).
  apply (Qle_trans _ ((1 - x * y) * (4 * x * y * z * (1 - z)))).
  - exact HA.
  - apply (Qle_trans _ ((1 - z) * (4 * x * y * (1 - x * y)))).
    + exact HB.
    + exact HC.
Qed.

(* ================= Section D. Linear control: 40N <= T ================= *)

(* The linear control 40N <= T. Chain: 40N = 10A * 4C with
   A = x(1-x)y(1-y) and C = z(1-z); 4C <= 1 scaling, the zeta(2)-face
   main inequality 10A <= 1-xy, and xy >= xyz transmit level by level. *)
Theorem zb3_N_le_T40 : forall x y z : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  QleT' (40 * x * (1 - x) * y * (1 - y) * z * (1 - z)) (1 - x*y*z).
Proof.
  intros x y z [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
  apply Qle_to_QleT'.
  assert (Hxb : 0 <= 1 - x) by (apply zb2_qle_to_Qle; apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply zb2_qle_to_Qle; apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply zb2_qle_to_Qle; apply (zb2_le_sub z 1); exact Hz2).
  assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
  assert (HC0 : 0 <= 4 * z * (1 - z))
    by (apply (Qmult_le_0_compat (4 * z) (1 - z))
       ; [ apply zb2_qle_to_Qle; apply (zb2_mult2_ge0 4 z); [ apply zb2_qle_to_Qle; apply (zb2_nat_pos 4) | exact Hz1 ]
         | exact Hzb ]).
(* The zeta(2)-face main inequality lifted to the Qle face. *)
  pose proof (zb2_ten_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as HtenS.
  pose proof (zb2_qle_to_Qle _ _ HtenS) as Hten.
(* Chain one: 10A * 4C <= (1-xy) * 4C. *)
  assert (Hs1 : (10 * x * (1 - x) * y * (1 - y)) * (4 * z * (1 - z))
             <= (1 - x * y) * (4 * z * (1 - z)))
    by (apply (Qmult_le_compat_r _ _ _ Hten HC0)).
  assert (E1 : (10 * x * (1 - x) * y * (1 - y)) * (4 * z * (1 - z))
            == 40 * x * (1 - x) * y * (1 - y) * z * (1 - z)) by ring.
  assert (HA : 40 * x * (1 - x) * y * (1 - y) * z * (1 - z)
            <= (1 - x * y) * (4 * z * (1 - z)))
    by (rewrite <- E1; exact Hs1).
(* Chain two: (1-xy) * 4C <= (1-xy) * 1 = 1-xy, by 4C <= 1. *)
  pose proof (zb2_qle_to_Qle _ _ (zb3_4zz_le_1 z)) as H4c.
  assert (Hxy1 : x * y <= 1) by (apply zb2_qle_to_Qle; apply (zb2_xy_le_1 x y); assumption).
  assert (Hle1 : 0 <= 1 - x * y)
    by (apply zb2_qle_to_Qle; apply (zb2_le_sub (x * y) 1); exact Hxy1).
  pose proof (Qmult_le_compat_r (4 * z * (1 - z)) 1 (1 - x * y) H4c Hle1) as Ht.
  rewrite Qmult_1_l in Ht.
  assert (E2 : (4 * z * (1 - z)) * (1 - x * y)
            == (1 - x * y) * (4 * z * (1 - z))) by ring.
  rewrite E2 in Ht.
  assert (HB : (1 - x * y) * (4 * z * (1 - z)) <= 1 - x * y) by exact Ht.
(* Chain three: 1-xy <= 1-xyz, since xy >= xyz. *)
  assert (Hzr : x * y * z <= x * y).
  { assert (Hq := Qmult_le_compat_r z 1 (x * y) Hz2 Hxy0).
    rewrite Qmult_1_l in Hq.
    assert (Ez : x * y * z == z * (x * y)) by ring.
    rewrite Ez. exact Hq. }
  assert (HC : 1 - x * y <= 1 - x * y * z).
  { apply zb2_qle_to_Qle. apply (zb2_minus_le 1 (x * y * z) (x * y) Hzr). }
  apply (Qle_trans _ ((1 - x * y) * (4 * z * (1 - z)))).
  - exact HA.
  - apply (Qle_trans _ (1 - x * y)).
    + exact HB.
    + exact HC.
Qed.

(* ================= Section E. The composite decay bound ================= *)

(* Composite decay: the base case is Section C; the step multiplies by
   40N <= T (Section D) and inducts. *)
Theorem zb3_pointwise_decay : forall (m : nat) (x y z : Q),
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  zb2_qle (4 * zb2_pow 40 m * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
          (zb2_pow (1 - x*y*z) (S (S m))).
Proof.
  intros m x y z Hx Hy Hz.
  revert Hx Hy Hz.
  induction m as [| m IH]; intros [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
    - (* Base case: 4N <= T^2. *)
    apply zb2_qle_of_Qle.
    assert (Heq1 : 4 * zb2_pow 40 0 * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) 1
                == 4 * x * (1-x) * y * (1-y) * z * (1-z)) by (simpl; ring).
    assert (Heq2 : zb2_pow (1 - x*y*z) 2 == (1 - x*y*z)*(1 - x*y*z))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    apply QleT'_to_Qle.
    apply zb3_N_le_Tsq
    ; [ split; assumption | split; assumption | split; assumption ].
    - (* Step: multiply by 40N <= T, then induct. *)
    apply zb2_qle_of_Qle.
    assert (HIH := IH (conj Hx1 Hx2) (conj Hy1 Hy2) (conj Hz1 Hz2)).
    apply zb2_qle_to_Qle in HIH.
    pose proof (QleT'_to_Qle _ _
             (zb3_N_le_T40 x y z (conj Hx1 Hx2) (conj Hy1 Hy2) (conj Hz1 Hz2)))
      as Hstep.
    assert (Hxb : 0 <= 1 - x) by (apply zb2_qle_to_Qle; apply (zb2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply zb2_qle_to_Qle; apply (zb2_le_sub y 1); exact Hy2).
    assert (Hzb : 0 <= 1 - z) by (apply zb2_qle_to_Qle; apply (zb2_le_sub z 1); exact Hz2).
    assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
    assert (Hxy1 : x * y <= 1) by (apply zb2_qle_to_Qle; apply (zb2_xy_le_1 x y); assumption).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y)*z*(1-z)).
    { assert (Hxy : 0 <= x * (1 - x)) by (apply zb2_qle_to_Qle; apply zb2_mult2_ge0; [exact Hx1 | exact Hxb]).
      assert (Hyy : 0 <= y * (1 - y)) by (apply zb2_qle_to_Qle; apply zb2_mult2_ge0; [exact Hy1 | exact Hyb]).
      assert (Hzz : 0 <= z * (1 - z)) by (apply zb2_qle_to_Qle; apply zb2_mult2_ge0; [exact Hz1 | exact Hzb]).
      assert (Hpre : 0 <= (x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z)))).
      { apply (Qmult_le_0_compat (x * (1 - x)) ((y * (1 - y)) * (z * (1 - z))))
        ; [ exact Hxy
          | apply (Qmult_le_0_compat (y * (1 - y)) (z * (1 - z)))
          ; [ exact Hyy | exact Hzz ] ]. }
      apply zb2_qle_to_Qle.
      apply (zb2_ge0_wd
               ((x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z))))
               (x*(1-x)*y*(1-y)*z*(1-z)))
      ; [ ring | exact Hpre ]. }
    assert (HP0 : 0 <= zb2_pow (1 - x*y*z) (S (S m)))
      by (apply zb2_qle_to_Qle; apply zb2_pow_ge0
         ; apply zb2_qle_to_Qle; apply (zb2_le_sub (x*y*z) 1)
         ; apply zb2_qle_to_Qle
         ; apply (zb2_xy_le_1 (x*y) z Hxy0 Hxy1 Hz1 Hz2)).
    assert (HK0 : 0 <= zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
      by (apply zb2_qle_to_Qle; apply zb2_pow_ge0; exact HN0).
    assert (H4K : 0 <= (4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)).
    { apply (Qmult_le_0_compat (4 * zb2_pow 40 m)
                               (zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
      ; [ apply zb2_qle_to_Qle; apply (zb2_mult2_ge0 4 (zb2_pow 40 m))
        ; [ apply zb2_qle_to_Qle; apply (zb2_nat_pos 4)
          | apply zb2_qle_to_Qle; apply zb2_pow_ge0; apply zb2_qle_to_Qle
          ; apply (zb2_nat_pos 40) ]
        | apply zb2_qle_to_Qle; apply zb2_pow_ge0; exact HN0 ]. }
    assert (HN40 : 0 <= 40 * x*(1-x)*y*(1-y)*z*(1-z)).
    { apply zb2_qle_to_Qle.
      apply (zb2_ge0_wd
               (40 * (x*(1-x)*y*(1-y)*z*(1-z)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)))
      ; [ ring
        | apply zb2_qle_to_Qle; apply (zb2_mult2_ge0 40 (x*(1-x)*y*(1-y)*z*(1-z)))
        ; [ apply zb2_qle_to_Qle; apply (zb2_nat_pos 40) | exact HN0 ] ]. }
    apply (Qle_trans
             (4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m)))
             (40 * x*(1-x)*y*(1-y)*z*(1-z)
              * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
             ((1 - x*y*z) * zb2_pow (1 - x*y*z) (S (S m)))).
    + apply zb2_qle_to_Qle.
      apply (zb2_le_eq
               (4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)
                * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))).
      assert (Hrw : 4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m))
                 == 40 * x*(1-x)*y*(1-y)*z*(1-z)
                    * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
        by (simpl; ring).
      exact Hrw.
    + apply zb2_qle_to_Qle.
      apply (zb2_mono_pair
               ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
               (zb2_pow (1 - x*y*z) (S (S m)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)) (1 - x*y*z))
      ; [ exact HIH | exact Hstep | exact H4K | exact HP0 | exact HN40
        | apply zb2_qle_to_Qle; apply (zb2_le_sub (x*y*z) 1)
        ; apply zb2_qle_to_Qle
        ; apply (zb2_xy_le_1 (x*y) z Hxy0 Hxy1 Hz1 Hz2) ].
Qed.

(* Numerical benchmark: at m = M = 1 and the diagonal point x = y = z = 1/2,
   40N = 40/64 = 5/8 <= 1 - 1/8 = 7/8 (by Qcompare). *)
Lemma zb3_lin_anchor : zb2_qle (40 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)))
                               (1 - (1#2)*(1#2)*(1#2)).
Proof. apply zb2_idrefl. Qed.

(* ================= Assumption closure of the main statements ================= *)

Print Assumptions zb3_4zz_le_1.
Print Assumptions zb3_11xy_le.
Print Assumptions zb3_sq_id.
Print Assumptions zb3_N_le_Tsq.
Print Assumptions zb3_N_le_T40.
Print Assumptions zb3_pointwise_decay.
Print Assumptions zb3_lin_anchor.
