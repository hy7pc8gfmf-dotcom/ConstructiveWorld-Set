(* ========================================================================= *)
(* Module   : abl_ln2_tail_bound                                            *)
(* Mission. Geometric tail-bound core of the ln2 irrationality chain: the   *)
(*           pole-series tail object u(n,k) = C(n+k,n)/((k+1)*2^(k+1)) with *)
(*           uniform ratio u(n,k+1)/u(n,k) <= 3/4 under 2n <= k+4, closed   *)
(*           through the power step, the geometric partial sum              *)
(*           4*(1-(3/4)^d), the partial-sum gap (Cauchy modulus), the       *)
(*           absolute peak 2^(n-1), and the combined bound                  *)
(*           gap <= 2^(n+1)*(3/4)^(S M-2n); plus the beta-series side: the  *)
(*           exact cross-ratio identity for bv_term and two machine anchors *)
(*           refuting any uniform geometric ratio rho < 1 on bv_term        *)
(*           (R(0,30) = 1891/2016 > 15/16 > 3/4).                           *)
(* Dependencies. Stdlib QArith.QArith, ZArith.ZArith, Arith.Arith, Lia,     *)
(*           Setoid; S01_BaseRing, S02_CauchyComplete, S03_QExp,            *)
(*           BeukersLists, BeukersVariant, PsQReindex of this development.  *)
(* Constructivity. Every named statement face is Set-carried: order faces   *)
(*           via QltT/QleT' (boolean identity carriers), equality faces via *)
(*           QeqT (Qcompare carrier), nat order faces via NatLe, strict nat *)
(*           inequality via NatLe (S a) b; zero Prop statements remain, no  *)
(*           sigT embedding, zero axioms, zero admits. Constructive Prop    *)
(*           reasoning is confined to proof bodies. No pure-Prop bridge     *)
(*           survives in the statement face, so no Qed is used and every    *)
(*           proof ends in Defined; vm_compute is confined to the three     *)
(*           concrete numeric pins.                                         *)
(* Build. coqc -native-compiler no -q -Q <Set Live root> "" via the r237    *)
(*           compile driver on the sandbox copy; the world copy is compiled *)
(*           again at the same root for downstream seats.                   *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists BeukersVariant PsQReindex.
Require Import S07_RealSetoidExpLog.

Open Scope nat_scope.

(* ============================================================ *)
(* Section 0. Generic small bridges: QeqT/QleT' transfers, cancellation, two-power positivity, geometric constants *)
(* ============================================================ *)

(* Symmetry of the Set-level Q equality carrier. *)
Lemma lnt_QeqT_sym : forall x y : Q, QeqT x y -> QeqT y x.
Proof.
  intros x y H. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. exact H.
Defined.

(* Left transfer: equal premises move a QleT' conclusion sideways. *)
Lemma lnt_leT'_eq_l : forall x y z : Q, QeqT x y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans y x z).
  - assert (Ey : y == x) by (apply Qeq_sym; apply qeqT_imp_qeq; exact H).
    exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ey))).
  - apply QleT'_to_Qle. exact Hq.
Defined.

(* Right transfer: equal conclusions move a QleT' premise sideways. *)
Lemma lnt_leT'_eq_r : forall x y z : Q, QeqT y z -> QleT' x y -> QleT' x z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact Hq.
  - exact (QleT'_to_Qle _ _
             (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ (qeqT_imp_qeq _ _ H)))).
Defined.

(* Right-multiplicative cancellation by a positive factor: 0 < z and x*z <= y*z give x <= y. *)
Lemma lnt_qle_mul_cancel_r : forall (x y z : Q),
  QltT 0 z -> QleT' (x * z) (y * z) -> QleT' x y.
Proof.
  intros x y z Hz Hle. apply Qle_to_QleT'.
  assert (HzP : Qlt 0 z) by (apply QltT_to_Qlt; exact Hz).
  assert (Hzn : ~ (z == 0%Q)).
  { intro HC. exact (Qlt_not_eq 0%Q z HzP (Qeq_sym z 0%Q HC)). }
  assert (Hzinv : (z * Qinv z)%Q == 1%Q) by (apply Qmult_inv_r; exact Hzn).
  assert (E1 : x == x * z * Qinv z).
  { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
    rewrite Qmult_1_r. reflexivity. }
  assert (E2 : Qle (y * z * Qinv z) y).
  { assert (H1 : (y * z * Qinv z)%Q == y%Q).
    { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
      rewrite Qmult_1_r. reflexivity. }
    exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ H1))). }
  apply (Qle_trans x (x * z * Qinv z)%Q y).
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1))).
  - apply (Qle_trans (x * z * Qinv z)%Q (y * z * Qinv z)%Q y).
    + apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hle).
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HzP.
    + exact E2.
Defined.

(* Left-multiplicative monotonicity by a nonnegative factor (this development's supplement). *)
Lemma lnt_Qmult_le_compat_l : forall (x y z : Q),
  QleT' 0 z -> QleT' x y -> QleT' (z * x) (z * y).
Proof.
  intros x y z Hz Hxy. apply Qle_to_QleT'.
  assert (E1 : (z * x)%Q == (x * z)%Q) by ring.
  apply (Qle_trans (z * x) (x * z) (z * y)).
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1))).
  - apply (Qle_trans (x * z) (y * z) (z * y)).
    + apply Qmult_le_compat_r;
        [exact (QleT'_to_Qle _ _ Hxy) | exact (QleT'_to_Qle _ _ Hz)].
    + assert (E2 : (y * z)%Q == (z * y)%Q) by ring.
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E2))).
Defined.

(* Inverse of a positive rational is a unit: Qinv z * z == 1. *)
Lemma lnt_qinv_mul_cancel : forall z : Q, QltT 0 z -> QeqT (Qinv z * z) 1%Q.
Proof.
  intros z Hz. apply qeq_imp_qeqT. rewrite Qmult_comm. apply Qmult_inv_r.
  intro HC. exact (Qlt_not_eq 0%Q z (QltT_to_Qlt _ _ Hz) (Qeq_sym z 0%Q HC)).
Defined.

(* Two-powers are strictly positive. *)
Lemma lnt_pow2_pos : forall j : nat, QltT 0 (q_pow (2 # 1)%Q j).
Proof.
  induction j as [| j IH].
  - apply rx_Qlt_Z1. lia.
  - apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q j)).
    apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply rx_Qlt_Z1. lia.
    + apply QltT_to_Qlt. exact IH.
Defined.

Lemma lnt_q4_le0 : QleT' 0 (4 # 1)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Defined.

Lemma lnt_rho_le0 : QleT' 0 (3 # 4)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Defined.

Lemma lnt_pow_pos_le : forall d : nat, QleT' 0 (q_pow (3 # 4)%Q d).
Proof.
  induction d as [| d IH].
  - cbn [q_pow]. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - apply (lnt_leT'_eq_r 0%Q (((3 # 4)%Q * q_pow (3 # 4)%Q d)%Q)
             (q_pow (3 # 4)%Q (Datatypes.S d))).
    + apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ (3 # 4)%Q d)). ring.
    + apply (lnt_leT'_eq_l (0 * q_pow (3 # 4)%Q d)%Q 0%Q
               (((3 # 4)%Q * q_pow (3 # 4)%Q d)%Q)).
      * apply qeq_imp_qeqT. ring.
      * apply qleT'_mult_compat_r; [exact IH | apply lnt_rho_le0].
Defined.

(* 1 - x <= 1 from 0 <= x. *)
Lemma lnt_sub_le1 : forall x : Q, QleT' 0 x -> QleT' (1 - x)%Q 1%Q.
Proof.
  intros x Hx. apply Qle_to_QleT'.
  apply (Qle_trans ((1 + (- x))%Q) ((1 + 0)%Q) 1%Q).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply (Qle_trans (- x) ((- x) + x) 0%Q).
      * apply (Qle_trans (- x) ((- x) + 0) ((- x) + x)).
        -- assert (E0 : ((- x) + 0)%Q == (- x)%Q) by ring.
          exact (QleT'_to_Qle _ _
                   (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ E0)))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. exact Hx.
      * assert (Er2 : ((- x) + x)%Q == 0%Q) by ring.
        exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Er2))).
  - assert (H1 : 1%Q == (1 + 0)%Q) by ring.
    exact (QleT'_to_Qle _ _
             (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ H1)))).
Defined.

(* Z-image bridge for two-powers: q_pow (2#1) j == (2^j)#1. *)
Lemma lnt_qpow_Zofnat : forall j : nat,
  QeqT (q_pow (2 # 1)%Q j) ((Z.of_nat (2 ^ j) # 1)%Q).
Proof.
  induction j as [| j IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q j)).
    rewrite (qeqT_imp_qeq _ _ IH).
    change (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    apply qeqT_imp_qeq. apply bk_Qmul_nat.
Defined.

(* ============================================================ *)
(* Section A. nat-level core: the pole-ratio window key, the beta deficit all-positive expansion, the bkC two-power bound *)
(* ============================================================ *)

(* Window key: 2n <= k+4 gives 2(n+k+1) <= 3(k+2), i.e. the pole ratio is at most 3/4. *)
Lemma lnt_key_pole : forall n k : nat,
  NatLe (2 * n) (k + 4) ->
  NatLe (2 * (n + Datatypes.S k)) (3 * (Datatypes.S (Datatypes.S k))).
Proof.
  intros n k H. apply NatLe_lift.
  pose proof (NatLe_drop _ _ H) as HP. lia.
Defined.

(* Beta deficit (n <= m window): the numerator product is strictly below the
   denominator product; strict nat inequality is carried as NatLe (S a) b,
   the all-positive polynomial expansion makes the gap explicit. *)
Theorem lnt_deficit_pos : forall n m : nat,
  NatLe n m ->
  NatLe (Datatypes.S ((n + m + 1) * (n + 2 * m + 1) * (n + 2 * m + 2)))
        ((m + 1) * (3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)).
Proof.
  intros n m Hnm. pose proof (NatLe_drop _ _ Hnm) as Hle.
  pose (d := m - n).
  assert (Hdm : m = n + d) by (unfold d; lia).
  rewrite Hdm.
  apply NatLe_lift.
  assert (Hexp : (n + d + 1) * (3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4)
               = (n + (n + d) + 1) * (n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2)
                 + (7 * (n * n * n) + 12 * (n * n) * d + 4 * n * (d * d)
                    + 8 * (d * d) + 36 * n * d + 33 * (n * n) + 18 * d + 34 * n + 10))
    by ring.
  rewrite Hexp. lia.
Defined.

(* Two-powers are at least one (nat face, NatLe carrier). *)
Lemma lnt_pow2_ge1 : forall N : nat, NatLe 1 (2 ^ N).
Proof.
  intro N. apply NatLe_lift. induction N as [| N IH].
  - reflexivity.
  - cbn [Nat.pow]. lia.
Defined.

(* bkC two-power bound: k <= N gives C(N,k) <= 2^N (Pascal induction, row-sum bound). *)
Lemma lnt_bkC_le_pow2 : forall N k : nat, NatLe k N -> NatLe (bkC N k) (2 ^ N).
Proof.
  induction N as [| N IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as HkP. assert (Hk0 : k = 0) by lia. subst k.
    apply NatLe_lift. cbn [bkC Nat.pow]. lia.
  - pose proof (NatLe_drop _ _ Hk) as HkP. destruct k as [| k'].
    + apply NatLe_lift. cbn [bkC Nat.pow].
      assert (Hg : (1 <= 2 ^ N)%nat) by (apply NatLe_drop; apply lnt_pow2_ge1).
      lia.
    + apply NatLe_lift. cbn [bkC Nat.pow].
      assert (Hk'P : (k' <= N)%nat) by lia.
      assert (H1 : (bkC N k' <= 2 ^ N)%nat)
        by (apply NatLe_drop; apply IH; apply NatLe_lift; exact Hk'P).
      destruct (le_lt_dec (Datatypes.S k') N) as [Hs | Hl].
      * assert (H2 : (bkC N (Datatypes.S k') <= 2 ^ N)%nat)
          by (apply NatLe_drop; apply IH; apply NatLe_lift; lia).
        lia.
      * assert (H0 : bkC N (Datatypes.S k') = 0).
        { apply RealSetoid.Id_eq. apply bkC_out. apply NatLe_lift. lia. }
        assert (Hg : (1 <= 2 ^ N)%nat) by (apply NatLe_drop; apply lnt_pow2_ge1).
        lia.
Defined.

(* This development's shifted instance of rx_bkC_ratio: C(S(n+m),n)*(S m) == C(n+m,n)*(n + S m). *)
Lemma lnt_bkC_step : forall n m : nat,
  Id (bkC (Datatypes.S (n + m)) n * Datatypes.S m)
     (bkC (n + m) n * (n + Datatypes.S m)).
Proof.
  intros n m. apply RealSetoid.eq_Id.
  assert (Hsm : Datatypes.S (n + m) = n + Datatypes.S m) by lia.
  rewrite Hsm.
  assert (H1 := rx_bkC_ratio (n + m) n (NatLe_lift _ _ (Nat.le_add_r n m))).
  replace (Datatypes.S (n + m) - n) with (Datatypes.S m) in H1 by lia.
  rewrite Hsm in H1.
  exact (RealSetoid.Id_eq _ _ H1).
Defined.

(* ============================================================ *)
(* Section B. The pole-series tail object: the all-positive term family of the (2-t)-normalized expansion and its geometric ratio tier *)
(*   u(n,k) = C(n+k,n) / ((k+1) * 2^(k+1))                                   *)
(* ============================================================ *)

Definition lnt_pterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

Theorem lnt_pterm_pos : forall n k : nat, QltT 0 (lnt_pterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnt_pterm, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (HbP : (1 <= bkC (n + k) n)%nat)
      by (apply NatLe_drop; apply bkC_pos; apply NatLe_lift; lia).
    assert (Hz : (0 <= Z.of_nat (bkC (n + k) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply rx_Qlt_Z1. lia.
    + apply QltT_to_Qlt. apply lnt_pow2_pos.
Defined.

(* Core step 1, the ratio tier: 2n <= k+4 gives u(n,k+1) <= (3/4) * u(n,k).
   Algebra: u(n,k+1)/u(n,k) = (n+k+1)/(2(k+2)); the window key gives
   2(n+k+1) <= 3(k+2). *)
Theorem lnt_pterm_ratio : forall n k : nat,
  NatLe (2 * n) (k + 4) ->
  QleT' (lnt_pterm n (Datatypes.S k)) ((3 # 4)%Q * lnt_pterm n k).
Proof.
  intros n k H. pose proof (NatLe_drop _ _ H) as HP. apply Qle_to_QleT'.
  assert (HsS : lnt_pterm n (Datatypes.S k)
    == ((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
  { unfold lnt_pterm, Qdiv.
    replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q (Datatypes.S k))). reflexivity. }
  assert (HsT : lnt_pterm n k
    == ((Z.of_nat (bkC (n + k) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
  { unfold lnt_pterm, Qdiv. reflexivity. }
  set (Qp := q_pow (2 # 1)%Q (Datatypes.S k)).
  assert (HQp : Qlt 0 Qp) by (apply QltT_to_Qlt; apply lnt_pow2_pos).
  (* nat core: 2*C1num*(S k) <= 3*C0num*(S (S k)), via the window key and the bkC step *)
  assert (Hnat : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
               <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)).
  { pose proof (NatLe_drop _ _ (lnt_key_pole n k H)) as HkeyP.
    assert (HstepE : bkC (Datatypes.S (n + k)) n * Datatypes.S k
                   = bkC (n + k) n * (n + Datatypes.S k))
      by (exact (RealSetoid.Id_eq _ _ (lnt_bkC_step n k))).
    assert (Hm := Nat.mul_le_mono_l (2 * (n + Datatypes.S k))
                  (3 * Datatypes.S (Datatypes.S k)) (bkC (n + k) n) HkeyP).
    assert (HeqL : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
                 = bkC (n + k) n * (2 * (n + Datatypes.S k))).
    { replace (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
        with (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
      rewrite HstepE. ring. }
    assert (HeqR : 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)
                 = bkC (n + k) n * (3 * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HeqL, HeqR. exact Hm. }
  (* Q core: 2 * C1num * a0 <= 3 * C0num * a1, via the Z-image bridge *)
  assert (HQcore : Qle (((2 # 1)%Q * (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)
                           * (Z.of_nat (Datatypes.S k) # 1)))%Q
                       (((3 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)
                           * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))%Q).
  { apply (Qle_trans (((2 # 1)%Q * (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)
                         * (Z.of_nat (Datatypes.S k) # 1)))%Q
             ((Z.of_nat (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) # 1)%Q)
             (((3 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)
                 * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))%Q).
    - assert (EA : (((2 # 1)%Q * (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)
                       * (Z.of_nat (Datatypes.S k) # 1)))%Q
                   == ((Z.of_nat (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) # 1)%Q)).
      { transitivity (((Z.of_nat 2 # 1) * (Z.of_nat (bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1))%Q).
        - assert (Einner : ((Z.of_nat (bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q)
                           == (((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) * (Z.of_nat (Datatypes.S k) # 1)))%Q)
            by (symmetry; apply qeqT_imp_qeq; apply bk_Qmul_nat).
          rewrite Einner. change (Z.of_nat 2 # 1)%Q with (2 # 1)%Q. ring.
        - apply qeqT_imp_qeq. apply bk_Qmul_nat. }
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ EA))).
    - apply (Qle_trans ((Z.of_nat (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) # 1)%Q)
               ((Z.of_nat (3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k))) # 1)%Q)
               (((3 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)
                   * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))%Q).
      + apply (QleT'_to_Qle _ _). apply bk_Qle_nat. apply NatLe_lift.
        replace (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k))
          with (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k) by ring.
        replace (3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k)))
          with (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)) by ring.
        exact Hnat.
      + assert (EB : ((Z.of_nat (3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k))) # 1)%Q)
                     == (((3 # 1)%Q * (Z.of_nat (bkC (n + k) n) # 1)
                            * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))%Q).
        { transitivity (((Z.of_nat 3 # 1) * (Z.of_nat (bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1))%Q).
          - symmetry. apply qeqT_imp_qeq. apply bk_Qmul_nat.
          - assert (Einner2 : ((Z.of_nat (bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q)
                              == (((Z.of_nat (bkC (n + k) n) # 1) * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))%Q)
              by (symmetry; apply qeqT_imp_qeq; apply bk_Qmul_nat).
            rewrite Einner2. change (Z.of_nat 3 # 1)%Q with (3 # 1)%Q. ring. }
        exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ EB))). }
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + k) n) # 1)%Q).
  set (a1 := (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q).
  set (a0 := (Z.of_nat (Datatypes.S k) # 1)%Q).
  assert (Ha1 : Qlt 0 a1) by (apply QltT_to_Qlt; apply rx_Qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply QltT_to_Qlt; apply rx_Qlt_Z1; lia).
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat;
         [exact Ha1 | apply Qmult_lt_0_compat;
           [apply QltT_to_Qlt; apply rx_Qlt_Z1; lia | exact HQp]]).
  assert (Ha0Q : Qlt 0 (a0 * Qp)%Q) by (apply Qmult_lt_0_compat; assumption).
  (* exploded-shape Qle cancellation chain: x := C1*Qinv(a1*(2*Qp)) <= (3/4)*(C0*Qinv(a0*Qp)) *)
  assert (Hmain : Qle ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
                      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)).
  { assert (Hxz : ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == (C1 * (a0 * Qp))%Q).
    { assert (Hcert : Qinv (a1 * ((2 # 1)%Q * Qp))
                        * (a1 * ((2 # 1)%Q * Qp)) == 1%Q)
        by (apply qeqT_imp_qeq; apply lnt_qinv_mul_cancel;
              apply Qlt_to_QltT; exact Ha1HQ).
      rewrite <- Qmult_assoc.
      transitivity (C1 * ((Qinv (a1 * ((2 # 1)%Q * Qp))
                            * (a1 * ((2 # 1)%Q * Qp))) * (a0 * Qp)))%Q.
      - ring.
      - rewrite Hcert. ring. }
    assert (Hyz : (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == ((3 # 4)%Q * C0 * a1 * ((2 # 1)%Q * Qp))%Q).
    { assert (Hcert0 : Qinv (a0 * Qp) * (a0 * Qp) == 1%Q)
        by (apply qeqT_imp_qeq; apply lnt_qinv_mul_cancel;
              apply Qlt_to_QltT; exact Ha0Q).
      rewrite <- Qmult_assoc, <- Qmult_assoc.
      transitivity ((3 # 4)%Q * C0
                      * ((Qinv (a0 * Qp) * (a0 * Qp))
                           * (a1 * ((2 # 1)%Q * Qp))))%Q.
      - ring.
      - rewrite Hcert0. ring. }
    apply (QleT'_to_Qle _ _).
    apply (lnt_qle_mul_cancel_r
      ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)
      (((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp))%Q)).
    - apply Qlt_to_QltT. apply Qmult_lt_0_compat; [exact Ha1HQ | exact Ha0Q].
    - apply Qle_to_QleT'.
      apply (Qle_trans ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                (C1 * (a0 * Qp))%Q
                (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q).
      + exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hxz))).
      + apply (QleT'_to_Qle _ _).
        apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qlt_to_QltT. apply Qmult_lt_0_compat;
            [apply QltT_to_Qlt; apply rx_Qlt_Z1; lia | exact HQp].
        * apply Qle_to_QleT'.
          apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- assert (E1 : ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                         == (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q) by ring.
            exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1))).
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                         * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ assert (E2 : (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                             == ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                                   * ((2 # 1)%Q * Qp))%Q).
                { rewrite Hyz. ring. }
                exact (QleT'_to_Qle _ _
                         (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E2))). }
  (* three-stage transfer: the exploded shape meets the lnt_pterm shape *)
  apply (Qle_trans (lnt_pterm n (Datatypes.S k))
           ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
           (((3 # 4)%Q * lnt_pterm n k)%Q)).
  - exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ HsS))).
  - apply (Qle_trans _ (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q) _).
    + exact Hmain.
    + assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnt_pterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ey))).
Defined.

(* Core step 2, the power tier: u(n,k+j) <= u(n,k) * (3/4)^j. *)
Theorem lnt_pterm_pow : forall (n k j : nat),
  NatLe (2 * n) (k + 4) ->
  QleT' (lnt_pterm n (k + j)) ((lnt_pterm n k * q_pow (3 # 4)%Q j)%Q).
Proof.
  intros n k j H. pose proof (NatLe_drop _ _ H) as HP.
  induction j as [| j IH].
  - assert (Ek0 : lnt_pterm n (k + 0) == lnt_pterm n k)
      by (unfold lnt_pterm; rewrite Nat.add_0_r; apply Qeq_refl).
    apply (lnt_leT'_eq_r (lnt_pterm n (k + 0)) (lnt_pterm n k)
             ((lnt_pterm n k * q_pow (3 # 4)%Q 0)%Q)).
    + apply qeq_imp_qeqT. cbn [q_pow]. ring.
    + exact (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Ek0)).
  - apply (lnt_leT'_eq_r (lnt_pterm n (k + Datatypes.S j))
             ((lnt_pterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q)
             ((lnt_pterm n k * q_pow (3 # 4)%Q (Datatypes.S j))%Q)).
    + apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ (3 # 4)%Q j)). ring.
    + apply qleT'_trans with (((3 # 4)%Q * lnt_pterm n (k + j))%Q).
      * apply (qleT'_trans (lnt_pterm n (k + Datatypes.S j))
                 (lnt_pterm n (Datatypes.S (k + j)))
                 (((3 # 4)%Q * lnt_pterm n (k + j))%Q)).
        -- assert (Ekj : lnt_pterm n (k + Datatypes.S j)
                       == lnt_pterm n (Datatypes.S (k + j))).
           { unfold lnt_pterm. replace (k + Datatypes.S j)
               with (Datatypes.S (k + j)) by lia. apply Qeq_refl. }
           exact (qeq_leT' _ _ (qeq_imp_qeqT _ _ Ekj)).
        -- apply lnt_pterm_ratio. apply NatLe_lift. lia.
      * apply (lnt_leT'_eq_r (((3 # 4)%Q * lnt_pterm n (k + j))%Q)
                 (((3 # 4)%Q * (lnt_pterm n k * q_pow (3 # 4)%Q j))%Q)
                 ((lnt_pterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q)).
        -- apply qeq_imp_qeqT. ring.
        -- apply (qleT'_mult_compat_l (lnt_pterm n (k + j))
                    (lnt_pterm n k * q_pow (3 # 4)%Q j) (3 # 4)%Q
                    lnt_rho_le0 IH).
Defined.

(* Core step 3, the exact geometric partial-sum identity: sum (3/4)^i == 4*(1-(3/4)^d). *)
Theorem lnt_geo_partial : forall d : nat,
  QeqT (sum_upto d (fun i : nat => q_pow (3 # 4)%Q i))
       (((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)).
Proof.
  induction d as [| d IH].
  - apply qeq_imp_qeqT. cbn [sum_upto q_pow]. ring.
  - apply qeq_imp_qeqT. cbn [sum_upto].
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (3 # 4)%Q d)).
    rewrite (qeqT_imp_qeq _ _ IH). ring.
Defined.

(* Finite-sum tool: pointwise transfer. *)
Lemma lnt_sum_le : forall (d : nat) (f g : nat -> Q),
  (forall i : nat, NatLe (Datatypes.S i) d -> QleT' (f i) (g i)) ->
  QleT' (sum_upto d f) (sum_upto d g).
Proof.
  intros d. induction d as [| d IH]; intros f g Hpt.
  - cbn [sum_upto]. apply qleT'_refl.
  - cbn [sum_upto]. apply qleT'_plus_compat.
    + apply IH. intros i Hi.
      apply Hpt. apply NatLe_lift. pose proof (NatLe_drop _ _ Hi) as HiP. lia.
    + apply Hpt. apply NatLe_lift. lia.
Defined.

(* Finite-sum tool: common-factor extraction. *)
Lemma lnt_sum_scale : forall (d : nat) (c : Q) (h : nat -> Q),
  QeqT (sum_upto d (fun i : nat => (c * h i)%Q)) ((c * sum_upto d h)%Q).
Proof.
  induction d as [| d IH]; intros c h.
  - cbn [sum_upto]. apply qeq_imp_qeqT. ring.
  - cbn [sum_upto]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (IH c h)). ring.
Defined.

(* Finite-sum tool: range split. *)
Lemma lnt_sum_range : forall (d M : nat) (f : nat -> Q),
  QeqT (sum_upto (Datatypes.S (M + d)) f)
       (sum_upto (Datatypes.S M) f
          + sum_upto d (fun i : nat => f (M + Datatypes.S i))).
Proof.
  induction d as [| d IH]; intros M f.
  - apply qeq_imp_qeqT. replace (M + 0)%nat with M by lia. cbn [sum_upto].
    rewrite Qplus_0_r. apply Qeq_refl.
  - apply qeq_imp_qeqT. cbn [sum_upto].
    replace (M + Datatypes.S d)%nat with (Datatypes.S (M + d)) by lia.
    rewrite (qeqT_imp_qeq _ _ (IH M f)).
    rewrite <- Qplus_assoc. apply Qeq_refl.
Defined.

(* Core step 4, the tail control (Cauchy modulus core): sum u(n,M+1+i) <= 4*u(n,M+1). *)
Theorem lnt_pterm_tail : forall (n M d : nat),
  NatLe (2 * n) (M + 4) ->
  QleT' (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
        (((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
Proof.
  intros n M d H. pose proof (NatLe_drop _ _ H) as HP.
  apply qleT'_trans with
    (((lnt_pterm n (Datatypes.S M))
       * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q).
  - apply (lnt_leT'_eq_r
      (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
      ((sum_upto d (fun i : nat =>
                         (lnt_pterm n (Datatypes.S M) * q_pow (3 # 4)%Q i))%Q))
      (((lnt_pterm n (Datatypes.S M))
         * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q)).
    + apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (lnt_sum_scale d (lnt_pterm n (Datatypes.S M))
                                  (fun i : nat => q_pow (3 # 4)%Q i))).
      rewrite (qeqT_imp_qeq _ _ (lnt_geo_partial d)). apply Qeq_refl.
    + apply lnt_sum_le. intros i Hi.
      apply (qleT'_trans (lnt_pterm n (M + Datatypes.S i))
              (lnt_pterm n (Datatypes.S M + i))
              ((lnt_pterm n (Datatypes.S M) * q_pow (3 # 4)%Q i))).
      * assert (Ems : lnt_pterm n (M + Datatypes.S i)
                    == lnt_pterm n (Datatypes.S M + i)).
        { unfold lnt_pterm.
          replace (M + Datatypes.S i) with (Datatypes.S M + i) by lia.
          apply Qeq_refl. }
        exact (qeq_leT' _ _ (qeq_imp_qeqT _ _ Ems)).
      * apply lnt_pterm_pow. apply NatLe_lift. lia.
  - apply qleT'_trans with
      (((lnt_pterm n (Datatypes.S M)) * ((4 # 1)%Q * 1)%Q)%Q).
    + apply (qleT'_mult_compat_l ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)
               ((4 # 1)%Q * 1)%Q (lnt_pterm n (Datatypes.S M))).
      * apply qltT_leT'. apply lnt_pterm_pos.
      * apply qleT'_mult_compat_l.
        { apply lnt_q4_le0. }
        { apply lnt_sub_le1. apply lnt_pow_pos_le. }
    + assert (Eone : ((lnt_pterm n (Datatypes.S M)) * ((4 # 1)%Q * 1)%Q)%Q
                   == (((4 # 1)%Q * lnt_pterm n (Datatypes.S M)))%Q) by ring.
      exact (qeq_leT' _ _ (qeq_imp_qeqT _ _ Eone)).
Defined.

(* Core step 5, the partial-sum gap (convergence-bridge Cauchy modulus): the additive form of S_{M+d} - S_M <= 4*u(n,M+1). *)
Theorem lnt_pterm_gap : forall (n M d : nat),
  NatLe (2 * n) (M + 4) ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        ((sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    ((sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))%Q)
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
    ((sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)).
  - apply (lnt_QeqT_sym _ _ (lnt_sum_range d M (fun k : nat => lnt_pterm n k))).
  - apply Qle_to_QleT'.
    apply (Qplus_le_compat
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
      ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnt_pterm_tail. exact H.
Defined.

(* Core step 6, the absolute peak tier: 1 <= n gives u(n,k) <= 2^(n-1) (bkC <= 2^(n+k) transfer). *)
Theorem lnt_pterm_peak : forall n k : nat,
  NatLe 1 n -> QleT' (lnt_pterm n k) (q_pow (2 # 1)%Q (n - 1)).
Proof.
  intros n k Hn. pose proof (NatLe_drop _ _ Hn) as HnP.
  assert (Ha0 : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1)%Q))
    by (apply QltT_to_Qlt; apply rx_Qlt_Z1; lia).
  assert (HQp : Qlt 0 (q_pow (2 # 1)%Q (Datatypes.S k)))
    by (apply QltT_to_Qlt; apply lnt_pow2_pos).
  assert (Haz : Qlt 0 (((Z.of_nat (Datatypes.S k) # 1)
                         * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  apply (lnt_qle_mul_cancel_r
    (((Z.of_nat (bkC (n + k) n) # 1) *
        Qinv ((Z.of_nat (Datatypes.S k) # 1) *
            q_pow (2 # 1)%Q (Datatypes.S k)))%Q)
    (q_pow (2 # 1)%Q (n - 1))
    ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q).
  - apply Qlt_to_QltT. exact Haz.
  - assert (Hcert : Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k))
                       * ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k)) == 1%Q)
      by (apply qeqT_imp_qeq; apply lnt_qinv_mul_cancel;
            apply Qlt_to_QltT; exact Haz).
    apply Qle_to_QleT'.
    apply (Qle_trans
      ((((Z.of_nat (bkC (n + k) n) # 1)
          * Qinv ((Z.of_nat (Datatypes.S k) # 1)
              * q_pow (2 # 1)%Q (Datatypes.S k)))
         * ((Z.of_nat (Datatypes.S k) # 1)
             * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)
      ((Z.of_nat (bkC (n + k) n) # 1)%Q)
      ((q_pow (2 # 1)%Q (n - 1)
          * ((Z.of_nat (Datatypes.S k) # 1)
              * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
    + assert (EA : (((Z.of_nat (bkC (n + k) n) # 1) *
                       Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                           q_pow (2 # 1)%Q (Datatypes.S k)))
                      * ((Z.of_nat (Datatypes.S k) # 1) *
                        q_pow (2 # 1)%Q (Datatypes.S k)))%Q
                == (Z.of_nat (bkC (n + k) n) # 1)%Q).
      { transitivity (((Z.of_nat (bkC (n + k) n) # 1) *
          (Qinv ((Z.of_nat (Datatypes.S k) # 1) *
              q_pow (2 # 1)%Q (Datatypes.S k)) *
            ((Z.of_nat (Datatypes.S k) # 1) *
              q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
        - ring.
        - rewrite Hcert. ring. }
      exact (QleT'_to_Qle _ _ (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ EA))).
    + assert (Hbr : ((Z.of_nat (2 ^ (n + k)) # 1)%Q)
                    == ((q_pow (2 # 1)%Q (n - 1) *
                          q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
      { replace (n + k) with ((n - 1) + Datatypes.S k) by lia.
        rewrite <- (qeqT_imp_qeq _ _ (lnt_qpow_Zofnat ((n - 1) + Datatypes.S k))).
        rewrite (qeqT_imp_qeq _ _ (q_pow_add (2 # 1)%Q (n - 1) (Datatypes.S k))).
        reflexivity. }
      apply (Qle_trans
        ((Z.of_nat (bkC (n + k) n) # 1)%Q)
        ((Z.of_nat (2 ^ (n + k)) # 1)%Q)
        ((q_pow (2 # 1)%Q (n - 1)
            * ((Z.of_nat (Datatypes.S k) # 1)
                * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
      * apply (QleT'_to_Qle _ _). apply bk_Qle_nat.
        apply lnt_bkC_le_pow2. apply NatLe_lift. lia.
      * apply (Qle_trans _ ((q_pow (2 # 1)%Q (n - 1) *
                               q_pow (2 # 1)%Q (Datatypes.S k))%Q) _).
        -- exact (QleT'_to_Qle _ _
                    (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ Hbr))).
        -- apply (Qle_trans
              ((q_pow (2 # 1)%Q (n - 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q)
              ((q_pow (2 # 1)%Q (n - 1)
                  * (1 * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)
              ((q_pow (2 # 1)%Q (n - 1)
                  * ((Z.of_nat (Datatypes.S k) # 1)
                      * q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
          ++ apply (QleT'_to_Qle _ _). apply lnt_Qmult_le_compat_l.
             ** apply qltT_leT'. apply lnt_pow2_pos.
             ** assert (E1Q : (q_pow (2 # 1)%Q (Datatypes.S k))
                            == (1 * q_pow (2 # 1)%Q (Datatypes.S k))%Q) by ring.
                exact (qeq_imp_qle _ _ (qeq_imp_qeqT _ _ E1Q)).
          ++ apply (QleT'_to_Qle _ _). apply lnt_Qmult_le_compat_l.
             ** apply qltT_leT'. apply lnt_pow2_pos.
             ** apply Qle_to_QleT'.
                assert (H1a0 : QleT' ((Z.of_nat 1 # 1)%Q)
                                 ((Z.of_nat (Datatypes.S k) # 1)%Q))
                  by (apply bk_Qle_nat; apply NatLe_lift; lia).
                apply Qmult_le_compat_r;
                  [exact (QleT'_to_Qle _ _ H1a0) | apply Qlt_le_weak; exact HQp].
Defined.

(* Combined geometric form: the tail gap is at most 2^(n+1) * (3/4)^(S M - 2n), the C(n)*rho^M shape with rho = 3/4. *)
Theorem lnt_gap_geo : forall (n M d : nat),
  NatLe 1 n -> NatLe (2 * n) (M + 1) ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        ((sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + ((q_pow (2 # 1)%Q (Datatypes.S n)
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q))%Q).
Proof.
  intros n M d Hn HM.
  pose proof (NatLe_drop _ _ Hn) as HnP. pose proof (NatLe_drop _ _ HM) as HMP.
  apply qleT'_trans with
    ((sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + (((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q))%Q).
  - apply lnt_pterm_gap. apply NatLe_lift. lia.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hpow := lnt_pterm_pow n (2 * n) (Datatypes.S M - 2 * n)
                        ltac:(apply NatLe_lift; lia)).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnt_pterm n (2 * n)) (q_pow (2 # 1)%Q (n - 1)))
        by (apply lnt_pterm_peak; exact Hn).
      assert (Hchain : QleT' (lnt_pterm n (Datatypes.S M))
                         ((q_pow (2 # 1)%Q (n - 1)
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))).
      { apply qleT'_trans with
          (((lnt_pterm n (2 * n)) * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnt_pterm n (2 * n))
                   (q_pow (2 # 1)%Q (n - 1))
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' (((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)
                      (((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
                          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)).
      { apply (qleT'_mult_compat_l (lnt_pterm n (Datatypes.S M))
                 ((q_pow (2 # 1)%Q (n - 1)
                    * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))) (4 # 1)%Q
                 lnt_q4_le0 Hchain). }
      assert (E42 : (((4 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q)
                    == (q_pow (2 # 1)%Q (Datatypes.S n))).
      { replace (Datatypes.S n) with (2 + (n - 1)) by lia.
        rewrite (qeqT_imp_qeq _ _ (q_pow_add (2 # 1)%Q 2 (n - 1))).
        cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        (((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)
        (((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
        (((q_pow (2 # 1)%Q (Datatypes.S n)) *
            q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)).
      * apply qeq_imp_qeqT. rewrite <- E42. ring.
      * exact Hxy.
Defined.

(* ============================================================ *)
(* Section C. The beta-series (bv_term) side: the exact cross-ratio identity and the machine anchors refuting a uniform geometric ratio *)
(* ============================================================ *)

(* Exact cross-ratio identity (the quantitative upgrade of the rx_term_decayQ monotonicity tier):
   T(n,m+1)*(m+1)(3n+2m+3)(3n+2m+4) == T(n,m)*(n+m+1)(n+2m+1)(n+2m+2). *)
Theorem lnt_bv_cross : forall n m : nat,
  QeqT ((bv_term n (Datatypes.S m)
          * (Z.of_nat (Datatypes.S m * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)%Q)%Q)
       ((bv_term n m
          * (Z.of_nat ((n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)%Q)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT.
  assert (HshapeS : bv_term n (Datatypes.S m)
    == ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1) *
          ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1) *
             ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))))
        * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))%Q).
  { unfold bv_term, Qdiv.
    replace (n + Datatypes.S m) with (Datatypes.S (n + m)) by lia.
    replace (n + 2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (n + 2 * m))) by lia.
    replace (3 * n + 2 * Datatypes.S m + 2)
      with (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2))) by lia.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (n + 2 * m)))).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (n + 2 * m))).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (3 * n + 2 * m + 2)))).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (3 * n + 2 * m + 2))).
    rewrite !Qinv_mult_distr.
    replace (Datatypes.S (Datatypes.S (n + 2 * m))) with (n + 2 * m + 2) by lia.
    replace (Datatypes.S (n + 2 * m)) with (n + 2 * m + 1) by lia.
    replace (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2)))
      with (3 * n + 2 * m + 4) by lia.
    replace (Datatypes.S (3 * n + 2 * m + 2)) with (3 * n + 2 * m + 3) by lia.
    ring. }
  assert (HshapeT : bv_term n m
    == ((Z.of_nat (bkC (n + m) n) # 1) *
         (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q).
  { unfold bv_term, Qdiv. reflexivity. }
  rewrite HshapeS, HshapeT.
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + m) n) # 1)%Q).
  set (CF := (q_fact (n + 2 * m) * q_fact (2 * n + 1)
                 / q_fact (3 * n + 2 * m + 2))%Q).
  set (Jp := ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q).
  set (cd := (Z.of_nat ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) # 1)%Q).
  assert (Hc3 : Qlt 0 ((Z.of_nat (3 * n + 2 * m + 3) # 1)%Q))
    by (apply QltT_to_Qlt; apply rx_Qlt_Z1; lia).
  assert (Hc4 : Qlt 0 ((Z.of_nat (3 * n + 2 * m + 4) # 1)%Q))
    by (apply QltT_to_Qlt; apply rx_Qlt_Z1; lia).
  assert (Hcd : Qlt 0 (((Z.of_nat (3 * n + 2 * m + 3) # 1)
                         * (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  assert (HcdJp : cd * Jp == 1%Q).
  { unfold cd, Jp.
    rewrite <- (qeqT_imp_qeq _ _
                  (bk_Qmul_nat (3 * n + 2 * m + 3) (3 * n + 2 * m + 4))).
    unfold Qdiv. rewrite !Qmult_1_l. rewrite <- Qinv_mult_distr.
    apply Qmult_inv_r. intro HC.
    exact (Qlt_not_eq 0%Q
            (((Z.of_nat (3 * n + 2 * m + 3) # 1)
                * (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q
            Hcd (Qeq_sym _ _ HC)). }
  assert (Ez1 : ((Z.of_nat (Datatypes.S m * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)%Q)
              == (((Z.of_nat (Datatypes.S m) # 1) * cd)%Q))
    by (symmetry; apply qeqT_imp_qeq; apply bk_Qmul_nat).
  assert (Ez2 : ((Z.of_nat ((n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)%Q)
              == (((Z.of_nat (n + m + 1) # 1)
                    * (Z.of_nat ((n + 2 * m + 1) * (n + 2 * m + 2)) # 1)))%Q)
    by (symmetry; apply qeqT_imp_qeq; apply bk_Qmul_nat).
  assert (Eab : ((Z.of_nat ((n + 2 * m + 1) * (n + 2 * m + 2)) # 1)%Q)
              == (((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1)))%Q)
    by (symmetry; apply qeqT_imp_qeq; apply bk_Qmul_nat).
  rewrite Ez1, Ez2, Eab.
  assert (HJpcd : Jp * cd == 1%Q) by (rewrite Qmult_comm; exact HcdJp).
  transitivity ((((C1 * (Z.of_nat (Datatypes.S m) # 1))%Q
                  * ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1))%Q
                  * (Jp * cd)%Q * CF)%Q)).
  - ring.
  - rewrite HJpcd.
    assert (Hsm : n + Datatypes.S m = n + m + 1) by lia.
    assert (Hkey : (C1 * (Z.of_nat (Datatypes.S m) # 1))%Q
                 == (C0 * (Z.of_nat (n + m + 1) # 1))%Q).
    { assert (HstepE : bkC (Datatypes.S (n + m)) n * Datatypes.S m
                     = bkC (n + m) n * (n + m + 1)).
      { pose proof (RealSetoid.Id_eq _ _ (lnt_bkC_step n m)) as HstepI.
        rewrite Hsm in HstepI. exact HstepI. }
      transitivity ((Z.of_nat (bkC (Datatypes.S (n + m)) n * Datatypes.S m) # 1)%Q).
      - apply qeqT_imp_qeq.
        apply (bk_Qmul_nat (bkC (Datatypes.S (n + m)) n) (Datatypes.S m)).
      - transitivity ((Z.of_nat (bkC (n + m) n * (n + m + 1)) # 1)%Q).
        + rewrite HstepE. reflexivity.
        + symmetry. apply qeqT_imp_qeq.
          apply (bk_Qmul_nat (bkC (n + m) n) (n + m + 1)). }
    rewrite Hkey. ring.
Defined.

(* Machine refutation anchor 1: at n=0, m=30 the beta-series ratio R = 1891/2016 > 3/4,
   so any uniform post-peak geometric ratio rho = 3/4 on bv_term is refuted. *)
Theorem lnt_beta_rho_refuted34 : QltT ((3 # 4)%Q * bv_term 0 30)%Q (bv_term 0 31).
Proof. vm_compute. reflexivity. Defined.

(* Machine refutation anchor 2: at the same point R > 15/16, so no uniform ratio rho < 1
   exists on the beta series (the rho^M draft must retarget to the pole-series tail object). *)
Theorem lnt_beta_rho_refuted1516 : QltT ((15 # 16)%Q * bv_term 0 30)%Q (bv_term 0 31).
Proof. vm_compute. reflexivity. Defined.

(* Pole-series positive anchor: inside the n=2 window the ratio tier is at most 3/4 (machine recheck). *)
Theorem lnt_pterm_anchor2 : QleT' (lnt_pterm 2 3) (((3 # 4)%Q * lnt_pterm 2 2)%Q).
Proof. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Section D. Closedness audit and independent extraction *)
(* ============================================================ *)

Print Assumptions lnt_QeqT_sym.
Print Assumptions lnt_leT'_eq_l.
Print Assumptions lnt_leT'_eq_r.
Print Assumptions lnt_qle_mul_cancel_r.
Print Assumptions lnt_Qmult_le_compat_l.
Print Assumptions lnt_qinv_mul_cancel.
Print Assumptions lnt_pow2_pos.
Print Assumptions lnt_q4_le0.
Print Assumptions lnt_rho_le0.
Print Assumptions lnt_pow_pos_le.
Print Assumptions lnt_sub_le1.
Print Assumptions lnt_qpow_Zofnat.
Print Assumptions lnt_key_pole.
Print Assumptions lnt_deficit_pos.
Print Assumptions lnt_pow2_ge1.
Print Assumptions lnt_bkC_le_pow2.
Print Assumptions lnt_bkC_step.
Print Assumptions lnt_pterm.
Print Assumptions lnt_pterm_pos.
Print Assumptions lnt_pterm_ratio.
Print Assumptions lnt_pterm_pow.
Print Assumptions lnt_geo_partial.
Print Assumptions lnt_sum_le.
Print Assumptions lnt_sum_scale.
Print Assumptions lnt_sum_range.
Print Assumptions lnt_pterm_tail.
Print Assumptions lnt_pterm_gap.
Print Assumptions lnt_pterm_peak.
Print Assumptions lnt_gap_geo.
Print Assumptions lnt_bv_cross.
Print Assumptions lnt_beta_rho_refuted34.
Print Assumptions lnt_beta_rho_refuted1516.
Print Assumptions lnt_pterm_anchor2.

From Stdlib Require Import Extraction.
Separate Extraction lnt_pterm_gap lnt_gap_geo lnt_pterm_peak lnt_bv_cross
  lnt_deficit_pos lnt_beta_rho_refuted34 lnt_beta_rho_refuted1516
  lnt_pterm_anchor2.
