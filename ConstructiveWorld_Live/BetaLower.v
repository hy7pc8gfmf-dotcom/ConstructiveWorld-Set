(* ConstructiveWorld-Main -> Set - BetaLower: c*sigma^n lower-bound family on
   the Beta closed-form carrier (statements carried on Set). *)
(** * BetaLower: c*sigma^n lower bounds carried by the Beta closed form.

    Mission.  Carrier [lne_B n] := (n!)^2/(2n+1)! (Beta closed form,
      [lne_B_closed]); the c*sigma^n lower-bound family: [bl_beta_lower],
      (1/2)*(3/16)^n <= lne_B n ([QleT']); family-optimal [bl_beta_lower_opt],
      (98/135)*(3/14)^n <= lne_B n, equality at both n = 2 and n = 3 (any
      c*sigma^n family has sigma <= min_{n>=2} step ratio = 3/14, optimal
      for all n >= 2); shifted variant [bl_variant_shift], (1/4)*(3/32)^n
      <= 2^{-(n+1)}*lne_B n = 2^{-(n+2)}*(3/16)^n.  Background:
      I_n := int_0^1 t^n(1-t)^n/(1-t/2)^{n+1} dt has ln2 - x'_n =
      I_n/(2^{n+1}*qtilde_n) and I_n >= lne_B n; I_n itself (rational
      integrand) is not in the library, so the file delivers lne_B-carried
      lower-bound shapes for I_n.  Anchors: lne_B 0..3 = 1, 1/6, 1/30,
      1/140 (nine [vm_compute] instances, three value witnesses).
    Dependencies.  [S02_CauchyComplete] ([QleT']/[QltT] bridges), [S03_QExp]
      ([q_pow]/[q_fact]), [SumInvFactEscape] ([sif_qfact_Z]), [PolyIntegral],
      [Ln2Escape] ([lne_B]); Stdlib [QArith], [Arith], [ZArith], [Arith.Factorial], [Lia].
    References.  PadeErrorIntegral [pei_beta] family and Ln2Escape [lne_beta_value]
      (Beta closed-form lineage); [lne_div_eq] (division comparator, isomorphic shape).
    Constructivity.  Statements on the Set face ([QleT'], [QeqT]; Q-layer
      [Prop] is internal scaffolding only); zero admitted statements, zero
      classical logic; pure nat factorial-inequality inductions
      ([bl_nat_core16]/[bl_nat_core14]: 3(2n+3) <= 8(n+1) / <= 7(n+1), linear
      [lia] certificates); comparators [bl_div_le]/[bl_div_ge]; extraction
      check [Obj.magic] = 0.
    Build.  [rocq c -native-compiler no -q -Q . "" BetaLower.v] exits 0
      against the S01/S02/S03 + PolyIntegral + SumInvFactEscape + Ln2Escape
      artifacts (COQLIB/ROCQLIB as full literal environment prefixes). *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Arith.Factorial.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S01_BaseRing (Id, id_refl, NatLe, NatLe_lift, NatLe_drop, Not).
Require Import SumInvFactEscape.
Require Import PolyIntegral.
Require Import Ln2Escape.

(* ============================================================ *)
(* S1. Q-layer support pieces (internal; the Prop face is scaffolding only)      *)
(* ============================================================ *)

(* k^n >= 1 (a power with positive base has a nonzero lower bound; for the Qlt cast branch) *)
Lemma bl_mul_ge1 : forall k n : nat, (1 <= k)%nat -> NatLe 1 (k ^ n).
Proof.
  intros k n Hk. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

(* Qmake multiplication bridge: (a#1)*(b#1) == (a*b#1) (definitional) *)
Lemma bl_qmake_mul : forall a b : Z, QeqT ((a # 1) * (b # 1)) ((a * b # 1)%Q).
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qmult. cbn [Pos.mul]. reflexivity.
Qed.

(* Multiplication/division associativity bridge: x*(y/z) == (x*y)/z (Qdiv is defined as multiplication by Qinv, associativity after unfolding) *)
Lemma bl_mult_div_assoc : forall x y z : Q, QeqT (x * (y / z)) ((x * y) / z).
Proof. intros x y z. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* Equal-exponent power product bridge: q_pow x n * q_pow y n == q_pow (x*y) n (used by bl_variant_shift) *)
Lemma bl_qpow_mul : forall (x y : Q) (n : nat), QeqT (q_pow x n * q_pow y n) (q_pow (x * y) n).
Proof.
  intros x y n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ x n)), (qeqT_imp_qeq _ _ (q_pow_succ y n)),
           (qeqT_imp_qeq _ _ (q_pow_succ (x * y) n)).
    transitivity ((x * y) * (q_pow x n * q_pow y n)).
    + ring.
    + rewrite IH. ring.
Qed.

(* Qinv distributes over the product (both factors nonzero; used by bl_pow_div and the bridges) *)
Lemma bl_qinv_mult : forall x y : Q,
  ~ (x == 0%Q) -> ~ (y == 0%Q) -> QeqT (Qinv (x * y)) (Qinv x * Qinv y).
Proof.
  intros x y Hx Hy. apply qeq_imp_qeqT.
  apply (fun H1 H2 => qeqT_imp_qeq _ _
           (lne_mult_canc (Qinv (x * y)) (Qinv x * Qinv y) (x * y) H1 H2)).
  - transitivity (1%Q).
    + rewrite (Qmult_comm (Qinv (x * y)) (x * y)).
      apply Qmult_inv_r.
      intro E. apply Hx.
      apply (fun H1 H2 => qeqT_imp_qeq _ _ (lne_mult_canc x 0%Q y H1 H2)).
      * rewrite Qmult_0_l. exact E.
      * exact Hy.
    + assert (E1 : (Qinv x * Qinv y) * (x * y) == (x * Qinv x) * (y * Qinv y)) by ring.
      rewrite E1.
      rewrite (Qmult_inv_r x Hx). rewrite (Qmult_inv_r y Hy). ring.
  - intro E. apply False_rect.
    exact (match lne_mult_nz x y Hx Hy (qeq_imp_qeqT _ _ E) with end).
Qed.

(* Positive-base powers are nonzero: ~ (q_pow y n == 0) *)
Lemma bl_qpow_nz : forall (y : Q) (n : nat),
  ~ (y == 0%Q) -> Not (QeqT (q_pow y n) 0%Q).
Proof.
  intros y n Hy.
  assert (Hprop : forall m : nat, ~ (q_pow y m == 0%Q)).
  { intro m. induction m as [| m IH].
    - intro E. vm_compute in E. lia.
    - intro E. apply False_rect.
      exact (match lne_mult_nz y (q_pow y m) Hy IH (qeq_imp_qeqT _ _ E) with end). }
  intro E. exact (False_rect _ (Hprop n (qeqT_imp_qeq _ _ E))).
Qed.

(* Powers distribute over division: q_pow (x/y) n == q_pow x n / q_pow y n *)
Lemma bl_pow_div : forall (x y : Q) (n : nat),
  ~ (y == 0%Q) -> QeqT (q_pow (x / y) n) (q_pow x n / q_pow y n).
Proof.
  intros x y n Hy. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - assert (Hzn : ~ (q_pow y n == 0%Q)).
    { intro E. exact (match bl_qpow_nz y n Hy (qeq_imp_qeqT _ _ E) with end). }
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (x / y) n)), (qeqT_imp_qeq _ _ (q_pow_succ x n)),
            (qeqT_imp_qeq _ _ (q_pow_succ y n)).
    rewrite IH.
    unfold Qdiv.
    rewrite (qeqT_imp_qeq _ _ (bl_qinv_mult y (q_pow y n) Hy Hzn)).
    ring.
Qed.

(* Integer cast power bridge: q_pow (k#1) n == (k^n # 1) *)
Lemma bl_pZ : forall k n : nat, QeqT (q_pow (Z.of_nat k # 1) n) ((Z.of_nat (k ^ n) # 1)%Q).
Proof.
  intros k n. apply qeq_imp_qeqT. induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (Z.of_nat k # 1) n)). rewrite IH. rewrite Nat.pow_succ_r'.
    unfold Qmult. cbn [Pos.mul]. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* Left multiplication preserves order: x <= y, 0 <= z imply z*x <= z*y (wrapper of Qmult_le_compat_r) *)
Lemma bl_mlc : forall x y z : Q, Qle x y -> Qle 0 z -> QleT' (z * x) (z * y).
Proof.
  intros x y z H Hz. apply Qle_to_QleT'.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  exact (Qmult_le_compat_r x y z H Hz).
Qed.

(* Division lower-bound comparator (dual of lne_div_le_inv): 0 < y, z*y <= x imply z <= x/y *)
Lemma bl_div_ge : forall x y z : Q, Qlt 0 y -> Qle (z * y) x -> QleT' z (x / y).
Proof.
  intros x y z Hy Hzy. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ E). }
  assert (Ey : (y * Qinv y)%Q == 1%Q) by (apply Qmult_inv_r; exact Hy0).
  assert (H1 : Qle ((z * y) * Qinv y) (x * Qinv y)).
  { apply (Qmult_le_compat_r (z * y) x).
    - exact Hzy.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy. }
  rewrite <- (Qmult_assoc z y (Qinv y)) in H1.
  rewrite Ey in H1. rewrite Qmult_1_r in H1.
  exact H1.
Qed.

(* Right canceller: 0 < s, a*s <= b*s imply a <= b (internally via bl_div_ge) *)
Lemma bl_cancel_r : forall a b s : Q, Qlt 0 s -> Qle (a * s) (b * s) -> QleT' a b.
Proof.
  intros a b s Hs H.
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (H1 : Qle a ((b * s) / s))
    by (apply QleT'_to_Qle; apply (bl_div_ge (b * s) s a Hs H)).
  assert (E : (b * s) / s == b).
  { unfold Qdiv.
    assert (E0 : (b * s) * Qinv s == b * (s * Qinv s)) by ring.
    rewrite E0, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
  rewrite E in H1. exact (Qle_to_QleT' _ _ H1).
Qed.

(* Division comparator (inequality version of lne_div_eq): 0 < y, 0 < s, x*s <= y*r imply x/y <= r/s *)
Lemma bl_div_le : forall x y r s : Q,
  Qlt 0 y -> Qlt 0 s -> Qle (x * s) (y * r) -> QleT' (x / y) (r / s).
Proof.
  intros x y r s Hy Hs Hc. apply Qle_to_QleT'.
  assert (Hy0 : ~ (y == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q y Hy). exact (Qeq_sym _ _ Ee). }
  assert (Hs0 : ~ (s == 0%Q)).
  { intro Ee. apply (Qlt_not_eq 0%Q s Hs). exact (Qeq_sym _ _ Ee). }
  assert (E : x / y == (x * s) / (y * s)).
  { apply (fun H1 H2 H3 => qeqT_imp_qeq _ _
             (lne_div_eq x y (x * s) (y * s) H1 H2 H3)).
    - exact Hy.
    - apply Qmult_lt_0_compat; assumption.
    - ring. }
  rewrite E. unfold Qdiv.
  rewrite (qeqT_imp_qeq _ _ (bl_qinv_mult y s Hy0 Hs0)).
  assert (E2 : (x * s) * (Qinv y * Qinv s) == (x * Qinv y) * (s * Qinv s)) by ring.
  rewrite E2.
  apply (Qle_trans _ (x * Qinv y)).
  - apply QleT'_to_Qle. apply qeq_imp_qle.
    assert (HT : (s * Qinv s)%Q == 1) by (apply Qmult_inv_r; exact Hs0).
    apply qeq_imp_qeqT. rewrite HT, Qmult_1_r. reflexivity.
  - apply QleT'_to_Qle. apply (bl_cancel_r (x * Qinv y) (r * Qinv s) s Hs).
    assert (E3 : (x * Qinv y) * s == (x * s) * Qinv y) by ring.
    rewrite E3.
    assert (E5 : (r * Qinv s) * s == r).
    { assert (E6 : (r * Qinv s) * s == r * (s * Qinv s)) by ring.
      rewrite E6, (Qmult_inv_r s Hs0), Qmult_1_r. reflexivity. }
    rewrite E5.
    apply (Qle_trans _ ((y * r) * Qinv y)).
    + apply (Qmult_le_compat_r (x * s) (y * r) (Qinv y)).
      * exact Hc.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hy.
    + assert (E4 : (y * r) * Qinv y == r).
      { assert (E7 : (y * r) * Qinv y == r * (y * Qinv y)) by ring.
        rewrite E7, (Qmult_inv_r y Hy0), Qmult_1_r. reflexivity. }
      rewrite E4. apply Qle_refl.
Qed.

(* ============================================================ *)
(* S2. Pure nat factorial-inequality cores (same shape as lne_nat_core; linear lia certificates) *)
(* ============================================================ *)

(* Main core: 3^n*8*(2n+1)! <= 16^n*16*(n!)^2
   (iff (1/2)(3/16)^n <= (n!)^2/(2n+1)!; the step factor 3(2n+3)(2n+2) <= 16(n+1)^2
     is achieved by the linear certificate 3(2n+3) <= 8(n+1) (n >= 1) times (2n+2)) *)
Lemma bl_nat_core16 : forall n : nat,
  NatLe (3 ^ n * 8 * fact (2 * n + 1)) (16 ^ n * 16 * fact n * fact n).
Proof.
  intros n. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (16 ^ Datatypes.S (Datatypes.S m))%nat with (16 * 16 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 8 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 8 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (8 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * replace ((3 * 3 ^ Datatypes.S m) * 8
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * ((2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 8 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((16 * 16 ^ Datatypes.S m) * 16
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((16 ^ Datatypes.S m * 16 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (16 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB.

Qed.

(* Optimal-tier core: 3^n*98*(2n+1)! <= 14^n*135*(n!)^2
   (iff (98/135)(3/14)^n <= (n!)^2/(2n+1)!; the step factor 3(2n+3)(2n+2) <= 14(n+1)^2
     is achieved by the linear certificate 3(2n+3) <= 7(n+1) (n >= 2) times (2n+2); equality 105840 at n = 2) *)
Lemma bl_nat_core14 : forall n : nat,
  NatLe (3 ^ n * 98 * fact (2 * n + 1)) (14 ^ n * 135 * fact n * fact n).
Proof.
  intros n. apply NatLe_lift. induction n as [| n IH].
  - cbn. lia.
  - destruct n as [| m].
    + cbn. lia.
    + destruct (Nat.eq_dec m 0) as [Hm0 | Hmpos].
      { subst m. cbn. lia. }
      replace (2 * Datatypes.S (Datatypes.S m) + 1)%nat
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))%nat by lia.
      cbn [fact].
      change (3 ^ Datatypes.S (Datatypes.S m))%nat with (3 * 3 ^ Datatypes.S m)%nat.
      change (14 ^ Datatypes.S (Datatypes.S m))%nat with (14 * 14 ^ Datatypes.S m)%nat.
      replace (Datatypes.S (Datatypes.S (2 * Datatypes.S m + 1)))
        with (2 * Datatypes.S (Datatypes.S m) + 1)%nat by lia.
      replace (Datatypes.S (2 * Datatypes.S m + 1))
        with (2 * Datatypes.S (Datatypes.S m))%nat by lia.
      assert (H1 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                    <= 7 * Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (H2 : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                    <= 7 * Datatypes.S (Datatypes.S m) * (2 * Datatypes.S (Datatypes.S m)))%nat)
        by (apply Nat.mul_le_mono_r; exact H1).
      assert (HAB : (3 * (2 * Datatypes.S (Datatypes.S m) + 1) * (2 * Datatypes.S (Datatypes.S m))
                     <= 14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m))%nat).
      { apply (Nat.le_trans _ (7 * Datatypes.S (Datatypes.S m)
                                 * (2 * Datatypes.S (Datatypes.S m)))%nat).
        - exact H2.
        - lia. }
      transitivity ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                      * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                           * (2 * Datatypes.S (Datatypes.S m))))%nat.
      * replace ((3 * 3 ^ Datatypes.S m) * 98
                   * ((2 * Datatypes.S (Datatypes.S m) + 1)
                        * ((2 * Datatypes.S (Datatypes.S m)) * fact (2 * Datatypes.S m + 1))))%nat
          with ((3 ^ Datatypes.S m * 98 * fact (2 * Datatypes.S m + 1))
                  * (3 * (2 * Datatypes.S (Datatypes.S m) + 1)
                       * (2 * Datatypes.S (Datatypes.S m))))%nat by ring.
        apply Nat.mul_le_mono_r. exact IH.
      * replace (Datatypes.S m * fact m)%nat with (fact (Datatypes.S m))%nat by reflexivity.
        replace ((14 * 14 ^ Datatypes.S m) * 135
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m))
                   * (Datatypes.S (Datatypes.S m) * fact (Datatypes.S m)))%nat
          with ((14 ^ Datatypes.S m * 135 * fact (Datatypes.S m) * fact (Datatypes.S m))
                  * (14 * Datatypes.S (Datatypes.S m) * Datatypes.S (Datatypes.S m)))%nat by ring.
        apply Nat.mul_le_mono_l. exact HAB.

Qed.

(* ============================================================ *)
(* S3. Q bridges: constant-power goals into single-division Z cast form          *)
(* ============================================================ *)

(* (1/2)*(3/16)^n == (3^n*8 # 1)/(16^n*16 # 1)
   ((1/2)(3/16)^n = 3^n/(2*16^n) = (8*3^n)/(16*16^n)) *)
Lemma bl_half_pow : forall n : nat,
  QeqT ((1 # 2) * q_pow (3 # 16) n)
       ((Z.of_nat (3 ^ n * 8) # 1) / (Z.of_nat (16 ^ n * 16) # 1)%Q).
Proof.
  (* Strategy: split 3/16 into 3/1 divided by 16/1, distribute the power by bl_pow_div, convert the
     casts by bl_pZ, merge the factors by bl_mult_div_assoc and bl_qmake_mul, close by lne_div_eq. *)
  intro n. apply qeq_imp_qeqT.
  replace (3 # 16)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 16 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 16 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 16) ltac:(lia)). lia. }
  rewrite (qeqT_imp_qeq _ _ (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 16 # 1) n Hnz)),
          (qeqT_imp_qeq _ _ (bl_pZ 3 n)), (qeqT_imp_qeq _ _ (bl_pZ 16 n)).
  assert (E1 : (Z.of_nat (3 ^ n * 8))%Z = (8 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (16 ^ n * 16))%Z = (16 * Z.of_nat (16 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (qeqT_imp_qeq _ _
             (bl_mult_div_assoc (1 # 2)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (16 ^ n) # 1))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 8%Z (Z.of_nat (3 ^ n)))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 16%Z (Z.of_nat (16 ^ n)))).
  apply (fun H1 H2 H3 => qeqT_imp_qeq _ _ (lne_div_eq _ _ _ _ H1 H2 H3)).
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (16 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* (98/135)*(3/14)^n == (3^n*98 # 1)/(14^n*135 # 1) *)
Lemma bl_opt_pow : forall n : nat,
  QeqT ((98 # 135) * q_pow (3 # 14) n)
       ((Z.of_nat (3 ^ n * 98) # 1) / (Z.of_nat (14 ^ n * 135) # 1)%Q).
Proof.
  (* Strategy as in bl_half_pow: after bl_pow_div distributes the power, merge into a single fraction,
     then close through bl_mult_div_assoc, bl_qmake_mul and lne_div_eq. *)
  intro n. apply qeq_imp_qeqT.
  replace (3 # 14)%Q with ((Z.of_nat 3 # 1) / (Z.of_nat 14 # 1))%Q by reflexivity.
  assert (Hnz : ~ ((Z.of_nat 14 # 1) == 0%Q)).
  { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
    pose proof (proj1 (Nat2Z.inj_lt 0 14) ltac:(lia)). lia. }
  rewrite (qeqT_imp_qeq _ _ (bl_pow_div (Z.of_nat 3 # 1) (Z.of_nat 14 # 1) n Hnz)),
          (qeqT_imp_qeq _ _ (bl_pZ 3 n)), (qeqT_imp_qeq _ _ (bl_pZ 14 n)).
  assert (E1 : (Z.of_nat (3 ^ n * 98))%Z = (98 * Z.of_nat (3 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  assert (E2 : (Z.of_nat (14 ^ n * 135))%Z = (135 * Z.of_nat (14 ^ n))%Z)
    by (rewrite Nat2Z.inj_mul; lia).
  rewrite E1, E2.
  rewrite (qeqT_imp_qeq _ _
             (bl_mult_div_assoc (98 # 135)%Q (Z.of_nat (3 ^ n) # 1) (Z.of_nat (14 ^ n) # 1))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 98%Z (Z.of_nat (3 ^ n)))).
  rewrite <- (qeqT_imp_qeq _ _ (bl_qmake_mul 135%Z (Z.of_nat (14 ^ n)))).
  apply (fun H1 H2 H3 => qeqT_imp_qeq _ _ (lne_div_eq _ _ _ _ H1 H2 H3)).
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))).
    pose proof (proj1 (Nat2Z.inj_lt 0 (14 ^ n)) ltac:(lia)). lia.
  - ring.
Qed.

(* ============================================================ *)
(* S4. Main pieces (Set face)                                                    *)
(* ============================================================ *)

(* Main piece (specification tier): (1/2)*(3/16)^n <= lne_B n *)
Theorem bl_beta_lower : forall n : nat, QleT' ((1 # 2) * q_pow (3 # 16) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bl_half_pow n)). rewrite (fun n => qeqT_imp_qeq _ _ (lne_B_closed n)).
  apply QleT'_to_Qle. apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 16 n ltac:(lia))). lia.
  - apply QltT_to_Qlt. apply q_fact_pos.
  - rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z n)),
            (qeqT_imp_qeq _ _ (sif_qfact_Z (Datatypes.S (n + n)))).
    pose proof (NatLe_drop _ _ (bl_nat_core16 n)) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* Optimal tier (family-optimal pair, equality at both n = 2 and n = 3): (98/135)*(3/14)^n <= lne_B n *)
Theorem bl_beta_lower_opt : forall n : nat, QleT' ((98 # 135) * q_pow (3 # 14) n) (lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bl_opt_pow n)). rewrite (fun n => qeqT_imp_qeq _ _ (lne_B_closed n)).
  apply QleT'_to_Qle. apply bl_div_le.
  - unfold Qlt. cbn [Qnum Qden].
    pose proof (NatLe_drop _ _ (bl_mul_ge1 14 n ltac:(lia))). lia.
  - apply QltT_to_Qlt. apply q_fact_pos.
  - rewrite (qeqT_imp_qeq _ _ (sif_qfact_Z n)),
            (qeqT_imp_qeq _ _ (sif_qfact_Z (Datatypes.S (n + n)))).
    pose proof (NatLe_drop _ _ (bl_nat_core14 n)) as Hnat.
    replace (2 * n + 1)%nat with (Datatypes.S (n + n))%nat in Hnat by lia.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
Qed.

(* Shifted variant ((1+t) face): (1/4)*(3/32)^n <= 2^{-(n+1)}*lne_B n.
   Note: the right side 2^{-(n+1)}*lne_B n is the provably foldable carrier of the (1+t)^{n+1}
   variant integral I'_n (proving I'_n >= 2^{-(n+1)}*lne_B n needs a pointwise machine on the
   full sequence; the exact shift is beyond this file); (1/4)(3/32)^n = 2^{-(n+2)}(3/16)^n matches the Lambda_n lower-bound requirement exactly. *)
Theorem bl_variant_shift : forall n : nat,
  QleT' ((1 # 4) * q_pow (3 # 32) n) (q_pow (1 # 2) (Datatypes.S n) * lne_B n).
Proof.
  intro n. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (1 # 2) (Datatypes.S n) * ((1 # 2) * q_pow (3 # 16) n))).
  - (* Left branch: the equality bridge (1/4)(3/32)^n == (1/2)^{n+1}*(1/2)(3/16)^n (the LHS has no
       A*(...) factor shape, so unifying against the bl_mlc conclusion z*x <= z*y must fail; take the qeq_imp_qle equality track) *)
    apply QleT'_to_Qle. apply qeq_imp_qle. apply qeq_imp_qeqT.
    replace (3 # 32) with ((1 # 2) * (3 # 16))%Q by reflexivity.
    rewrite <- (qeqT_imp_qeq _ _ (bl_qpow_mul (1 # 2) (3 # 16) n)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 # 2) n)).
    ring.
  - (* Right branch: A*(1/2)(3/16)^n <= A*lne_B n -- bl_mlc (order preservation under left multiplication by 0 <= A) in its direct orientation *)
    apply QleT'_to_Qle. apply (bl_mlc _ _ (q_pow (1 # 2) (Datatypes.S n))).
    + apply QleT'_to_Qle. apply bl_beta_lower.
    + apply QleT'_to_Qle. apply (q_pow_nonneg (1 # 2) (Datatypes.S n)).
      apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* S5. Numerical anchor checks (n = 0..3 vm_compute instances + carrier value witnesses) *)
(* ============================================================ *)

Lemma bl_spec_anchor0 : QleT' ((1 # 2) * q_pow (3 # 16) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor1 : QleT' ((1 # 2) * q_pow (3 # 16) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor2 : QleT' ((1 # 2) * q_pow (3 # 16) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_spec_anchor3 : QleT' ((1 # 2) * q_pow (3 # 16) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor0 : QleT' ((98 # 135) * q_pow (3 # 14) 0) (lne_B 0).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor1 : QleT' ((98 # 135) * q_pow (3 # 14) 1) (lne_B 1).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor2 : QleT' ((98 # 135) * q_pow (3 # 14) 2) (lne_B 2).
Proof. vm_compute. reflexivity. Qed.

Lemma bl_opt_anchor3 : QleT' ((98 # 135) * q_pow (3 # 14) 3) (lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* Variant fold n = 3 anchor: 2^{-4}*(1/140) = 1/2240 >= 27/131072 *)
Lemma bl_var_anchor3 : QleT' ((1 # 4) * q_pow (3 # 32) 3) (q_pow (1 # 2) 3 * lne_B 3).
Proof. vm_compute. reflexivity. Qed.

(* Carrier value witnesses (Beta closed-form numerical face): 1, 1/6, 1/30, 1/140 *)
Lemma bl_value1 : QeqT (lne_B 1) (1 # 6).
Proof. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (lne_B_closed 1)). reflexivity. Qed.

Lemma bl_value2 : QeqT (lne_B 2) (1 # 30).
Proof. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (lne_B_closed 2)). reflexivity. Qed.

Lemma bl_value3 : QeqT (lne_B 3) (1 # 140).
Proof. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ (lne_B_closed 3)). reflexivity. Qed.

(* ============================================================ *)
(* S6. Extraction check + Print Assumptions self-audit                           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bl_beta_lower bl_beta_lower_opt bl_variant_shift
  bl_spec_anchor3 bl_var_anchor3 lne_B q_pow.

Print Assumptions bl_beta_lower.
Print Assumptions bl_beta_lower_opt.
Print Assumptions bl_variant_shift.
