(* ========================================================================= *)
(* Module   : abl_ln2_theta_total                                           *)
(* Mission.  Terminal assembly of the ln2 irrationality chain: the theta^n  *)
(*            final bound. Layer 1: DH tail-gap 2^(n+2)*(3/4)^(m-2n) x DU   *)
(*            growth budget A_n := 2^n*q~_n <= 12^n (q~_n = central         *)
(*            Delannoy number); slope race closes at slope 18 with C18 :=   *)
(*            (128/3)*(3/4)^18 = 3^17/2^29 < 1/4 so A_n*tail < 1 for all    *)
(*            n >= 1 (lnt4_An_gap_compose/lnt4_compete_exp/lnt4_theta_lt),  *)
(*            pure-budget gate at slope 11 with C11 = 3^10/2^16 < 1         *)
(*            (lnt4_budget_lt). Layer 2: full-container band A_n*S_{M+d} <= *)
(*            SM*24^n + d*(128/3)^n*rho^SM (lnt4_total_budget), DH gap twin *)
(*            (lnt4_total_gap_budget), slope form (lnt4_total_slope).       *)
(*            Layer 3: sigT witness B := 4*C18 = 3^17/2^27 < 1              *)
(*            (lnt4_remainder_sig), final And face (lnt4_theta_final);      *)
(*            numeric pins close the layer.                                 *)
(* Dependencies. Stdlib QArith/Arith/ZArith/Lia/Extraction; landed modules  *)
(*            S01_BaseRing, S02_CauchyComplete, S03_QExp, BeukersLists      *)
(*            (bkC/bk_psd/bk_Qn_qtilde), PsQReindex; the upstream Main-chain *)
(*            supply is rebuilt inside this file, no unlanded Required.     *)
(* Constructivity. Conclusion faces all Set-carried: QeqT/QleT'/QltT        *)
(*            (decidable boolean carriers), S01 Set product And, sigT; the  *)
(*            single sigT mirrors the stdlib existential shape with closed  *)
(*            rational witness B := 3^17/2^27 (declared). Definitions       *)
(*            transparent; Qed confined to pure Prop proof bridges (Qeq/    *)
(*            Qle/Qlt/nat scaffolding incl. decidable premise slots         *)
(*            1<=n, 2n<=m, 18n<=m); Set-face proofs end in Defined;         *)
(*            vm_compute only on concrete numeric pins.                     *)
(* Build.     rocq c -native-compiler no -q -Q <Set Live root> ""           *)
(*            abl_ln2_theta_total.v  (driver: r237_compile.py).             *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists PsQReindex.

Open Scope nat_scope.

(* ============================================================ *)
(* Section A: Prop-face bridges toward the landed Set modules.      *)
(*   Qeq-form wrappers of the QeqT/q_pow lemmas of S03/BeukersLists,   *)
(*   Prop-order wrappers of bk_Qle_nat/bk_Qmul_nat, and the Qeq-to-Qle  *)
(*   kernel. These carry the Qeq/Qle faces used only as reasoning       *)
(*   scaffolding inside proof bodies (declared in the header).          *)
(* ============================================================ *)

Lemma qeqQ_le : forall x y : Q, x == y -> Qle x y.
Proof.
  intros x y H.
  unfold Qle, Qeq in *.
  rewrite H.
  apply Z.le_refl.
Qed.

Lemma w_qeq_leT' : forall a b : Q, a == b -> QleT' a b.
Proof. intros a b H. apply qeq_leT'. apply qeq_imp_qeqT. exact H. Defined.

Lemma w_qpow_succ : forall (x : Q) (n : nat), q_pow x (Datatypes.S n) == (x * q_pow x n)%Q.
Proof. intros x n. apply (qeqT_imp_qeq _ _). apply q_pow_succ. Qed.

Lemma w_qpow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b) == (q_pow x a * q_pow x b)%Q.
Proof. intros x a b. apply (qeqT_imp_qeq _ _). apply q_pow_add. Qed.

Lemma w_qpow_one : forall k : nat, q_pow (1 # 1)%Q k == (1 # 1)%Q.
Proof.
  intro k. induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. reflexivity.
Qed.

Lemma w_qpow_mul_eq : forall (x y : Q) (k : nat),
  q_pow (x * y)%Q k == (q_pow x k * q_pow y k)%Q.
Proof. intros x y k. apply (qeqT_imp_qeq _ _). apply bk_q_pow_mul. Qed.

Lemma w_Qmul_nat : forall a b : nat,
  ((Z.of_nat a # 1)%Q * (Z.of_nat b # 1)%Q) == ((Z.of_nat (a * b) # 1)%Q).
Proof. intros a b. apply (qeqT_imp_qeq _ _). apply bk_Qmul_nat. Qed.

Lemma w_Qle_nat : forall a b : nat, a <= b -> Qle (Z.of_nat a # 1)%Q (Z.of_nat b # 1)%Q.
Proof.
  intros a b H. apply QleT'_to_Qle. apply bk_Qle_nat. apply NatLe_lift. exact H.
Qed.

Lemma w_QleT'_nat : forall a b : nat, a <= b -> QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H. apply bk_Qle_nat. apply NatLe_lift. exact H.
Defined.

Lemma w_Qlt_Z1 : forall z : Z, (0 < z)%Z -> Qlt 0 (z # 1)%Q.
Proof. intros z H. apply QltT_to_Qlt. apply rx_Qlt_Z1. exact H. Qed.

Lemma w_bkC_pos : forall n k : nat, k <= n -> 1 <= bkC n k.
Proof.
  intros n k H. apply NatLe_drop. apply bkC_pos. apply NatLe_lift. exact H.
Qed.

Lemma w_pow2_ge1 : forall N : nat, 1 <= 2 ^ N.
Proof.
  induction N as [| N IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
Qed.

Lemma lng_qpow_congr : forall (a b : Q) (k : nat), a == b -> q_pow a k == q_pow b k.
Proof.
  intros a b k H. induction k as [| k IH].
  - apply Qeq_refl.
  - cbn [q_pow]. rewrite IH, H. apply Qeq_refl.
Qed.

Lemma lnt_bkC_step : forall n m : nat,
  bkC (Datatypes.S (n + m)) n * Datatypes.S m = bkC (n + m) n * (n + Datatypes.S m).
Proof.
  intros n m.
  assert (Hsm : Datatypes.S (n + m) = n + Datatypes.S m) by lia.
  rewrite Hsm.
  assert (H1 := rx_bkC_ratio (n + m) n (NatLe_lift n (n + m) (Nat.le_add_r n m))).
  replace (Datatypes.S (n + m) - n) with (Datatypes.S m) in H1 by lia.
  rewrite Hsm in H1.
  apply (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ H1).
Qed.

(* ============================================================ *)
(* Section B: Q order core (Prop scaffolding of the Main baseline).   *)
(* ============================================================ *)

Lemma lnt_leT'_eq_l : forall x y z : Q, x == y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans y x z).
  - apply qeqQ_le. apply Qeq_sym. exact H.
  - apply QleT'_to_Qle. exact Hq.
Defined.

Lemma lnt_leT'_eq_r : forall x y z : Q, y == z -> QleT' x y -> QleT' x z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact Hq.
  - apply qeqQ_le. exact H.
Defined.

Lemma lnt_qneq_of_eq0 : forall x : Q, Qlt 0 x -> ~ (x == 0%Q).
Proof.
  intros x H HC. apply (Qlt_not_eq 0%Q x H). rewrite HC. reflexivity.
Qed.

Lemma lnt_qle_mul_cancel_r : forall (x y z : Q),
  Qlt 0 z -> Qle (x * z) (y * z) -> Qle x y.
Proof.
  intros x y z Hz Hle.
  assert (Hzn : ~ (z == 0%Q)) by (apply lnt_qneq_of_eq0; exact Hz).
  assert (Hzinv : (z * Qinv z)%Q == 1%Q) by (apply Qmult_inv_r; exact Hzn).
  assert (E1 : x == x * z * Qinv z).
  { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
    rewrite Qmult_1_r. reflexivity. }
  assert (E2 : Qle (y * z * Qinv z) y).
  { assert (H1 : (y * z * Qinv z)%Q == y%Q).
    { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
      rewrite Qmult_1_r. reflexivity. }
    apply qeqQ_le. exact H1. }
  apply (Qle_trans x (x * z * Qinv z)%Q y).
  - apply qeqQ_le. exact E1.
  - apply (Qle_trans (x * z * Qinv z)%Q (y * z * Qinv z)%Q y).
    + apply Qmult_le_compat_r.
      * exact Hle.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hz.
    + exact E2.
Qed.

Lemma lnt_Qmult_le_compat_l : forall (x y z : Q),
  Qle 0 z -> Qle x y -> Qle (z * x) (z * y).
Proof.
  intros x y z Hz Hxy.
  apply (Qle_trans (z * x) (x * z) (z * y)).
  - apply qeqQ_le. ring.
  - apply (Qle_trans (x * z) (y * z) (z * y)).
    + apply Qmult_le_compat_r; assumption.
    + apply qeqQ_le. ring.
Qed.

Lemma lnt_qinv_mul_cancel : forall z : Q, ~ (z == 0%Q) -> Qinv z * z == 1.
Proof.
  intros z Hz. rewrite Qmult_comm. apply Qmult_inv_r. exact Hz.
Qed.

Lemma lnt_pow2_pos : forall j : nat, Qlt 0 (q_pow (2 # 1)%Q j).
Proof.
  induction j as [| j IH].
  - apply w_Qlt_Z1. lia.
  - rewrite w_qpow_succ. apply Qmult_lt_0_compat.
    + apply w_Qlt_Z1. lia.
    + exact IH.
Qed.

Lemma lnt_q4_le0 : QleT' 0 (4 # 1)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Defined.

Lemma lnt_rho_le0 : QleT' 0 (3 # 4)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Defined.

Lemma lnt_pow_pos_le : forall d : nat, QleT' 0 (q_pow (3 # 4)%Q d).
Proof.
  induction d as [| d IH].
  - cbn [q_pow]. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - apply lnt_leT'_eq_r with (y := ((3 # 4)%Q * q_pow (3 # 4)%Q d)%Q).
    + rewrite w_qpow_succ. ring.
    + apply lnt_leT'_eq_l with (x := (0 * q_pow (3 # 4)%Q d)%Q).
      * ring.
      * apply qleT'_mult_compat_r; [exact IH | apply lnt_rho_le0].
Defined.

Lemma lnt_sub_le1 : forall x : Q, QleT' 0 x -> QleT' (1 - x)%Q 1%Q.
Proof.
  intros x Hx. apply Qle_to_QleT'.
  apply (Qle_trans ((1 + (- x))%Q) ((1 + 0)%Q) 1%Q).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply (Qle_trans (- x) ((- x) + x) 0%Q).
      * apply (Qle_trans (- x) ((- x) + 0) ((- x) + x)).
        -- apply qeqQ_le. apply Qeq_sym. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. exact Hx.
      * assert (Er2 : ((- x) + x)%Q == 0%Q) by ring.
        apply qeqQ_le. exact Er2.
  - assert (H1 : 1%Q == (1 + 0)%Q) by ring.
    apply qeqQ_le. apply Qeq_sym. exact H1.
Qed.

Lemma lnt_qpow_Zofnat : forall j : nat,
  q_pow (2 # 1)%Q j == ((Z.of_nat (2 ^ j) # 1)%Q).
Proof.
  induction j as [| j IH].
  - reflexivity.
  - rewrite w_qpow_succ, IH.
    change (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat.
    replace (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q) by reflexivity.
    apply w_Qmul_nat.
Qed.

Lemma lnt_key_pole : forall n k : nat,
  2 * n <= k + 4 -> 2 * (n + Datatypes.S k) <= 3 * (Datatypes.S (Datatypes.S k)).
Proof. intros n k H. lia. Qed.

Lemma lng2_bkC_le_pow2 : forall n k : nat, bkC n k <= 2 ^ n.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. apply Nat.le_refl.
    + cbn [bkC Nat.pow]. apply Nat.le_0_l.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. assert (H := w_pow2_ge1 n). lia.
    + cbn [bkC]. rewrite Nat.pow_succ_r'.
      assert (H1 := IH k'). assert (H2 := IH (Datatypes.S k')). lia.
Qed.

(* ============================================================ *)
(* Section C: finite-sum container lemmas over sum_upto (S03).        *)
(* ============================================================ *)

Lemma lnt_sum_le : forall (d : nat) (f g : nat -> Q),
  (forall i : nat, i < d -> QleT' (f i) (g i)) ->
  QleT' (sum_upto d f) (sum_upto d g).
Proof.
  intros d. induction d as [| d IH]; intros f g Hpt.
  - cbn [sum_upto]. apply qleT'_refl.
  - cbn [sum_upto]. apply qleT'_plus_compat.
    + apply IH. intros i Hi. apply Hpt. lia.
    + apply Hpt. lia.
Defined.

Lemma lnt_sum_scale : forall (d : nat) (c : Q) (h : nat -> Q),
  sum_upto d (fun i : nat => (c * h i)%Q) == (c * sum_upto d h)%Q.
Proof.
  induction d as [| d IH]; intros c h.
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

Lemma lnt_sum_range : forall (d M : nat) (f : nat -> Q),
  sum_upto (Datatypes.S (M + d)) f
  == sum_upto (Datatypes.S M) f + sum_upto d (fun i : nat => f (M + Datatypes.S i)).
Proof.
  induction d as [| d IH]; intros M f.
  - replace (M + 0) with M by lia. cbn [sum_upto].
    rewrite Qplus_0_r. apply Qeq_refl.
  - cbn [sum_upto].
    replace (M + Datatypes.S d) with (Datatypes.S (M + d)) by lia.
    rewrite IH.
    rewrite <- Qplus_assoc. apply Qeq_refl.
Qed.

Lemma lnt_geo_partial : forall d : nat,
  sum_upto d (fun i : nat => q_pow (3 # 4)%Q i)
  == ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d))%Q.
Proof.
  induction d as [| d IH].
  - cbn [sum_upto q_pow]. ring.
  - cbn [sum_upto]. rewrite w_qpow_succ, IH. ring.
Qed.

(* ============================================================ *)
(* Section D: the pole-series term family u(n,k) = C(n+k,n)/((k+1)*2^(k+1)). *)
(* ============================================================ *)

Definition lnt_pterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

Theorem lnt_pterm_pos : forall n k : nat, QltT 0 (lnt_pterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnt_pterm, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : 1 <= bkC (n + k) n) by (apply w_bkC_pos; lia).
    assert (Hz : (0 <= Z.of_nat (bkC (n + k) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply w_Qlt_Z1. lia.
    + apply lnt_pow2_pos.
Qed.

Theorem lnt_pterm_ratio : forall n k : nat,
  2 * n <= k + 4 -> QleT' (lnt_pterm n (Datatypes.S k)) ((3 # 4)%Q * lnt_pterm n k).
Proof.
  intros n k H. apply Qle_to_QleT'.
  assert (HsS : lnt_pterm n (Datatypes.S k)
    == ((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
  { unfold lnt_pterm, Qdiv.
    replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    rewrite (w_qpow_succ (2 # 1)%Q (Datatypes.S k)). reflexivity. }
  assert (HsT : lnt_pterm n k
    == ((Z.of_nat (bkC (n + k) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
  { unfold lnt_pterm, Qdiv. reflexivity. }
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + k) n) # 1)%Q).
  set (a1 := (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q).
  set (a0 := (Z.of_nat (Datatypes.S k) # 1)%Q).
  set (Qp := q_pow (2 # 1)%Q (Datatypes.S k)).
  assert (Ha1 : Qlt 0 a1) by (apply w_Qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply w_Qlt_Z1; lia).
  assert (HQp : Qlt 0 Qp) by apply lnt_pow2_pos.
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat; [exact Ha1 | apply Qmult_lt_0_compat;
         [apply w_Qlt_Z1; lia | exact HQp]]).
  assert (Ha0Q : Qlt 0 (a0 * Qp)%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hnat : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
               <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)).
  { assert (Hkey := lnt_key_pole n k H).
    assert (Hstep := lnt_bkC_step n k).
    assert (Hm := Nat.mul_le_mono_l (2 * (n + Datatypes.S k))
                  (3 * Datatypes.S (Datatypes.S k)) (bkC (n + k) n) Hkey).
    assert (HeqL : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
                 = bkC (n + k) n * (2 * (n + Datatypes.S k))).
    { replace (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
        with (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
      rewrite Hstep. ring. }
    assert (HeqR : 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)
                 = bkC (n + k) n * (3 * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HeqL, HeqR. exact Hm. }
  assert (HQcore : Qle ((2 # 1)%Q * C1 * a0) ((3 # 1)%Q * C0 * a1)).
  { assert (H1 : Qle ((Z.of_nat (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q)
                     ((Z.of_nat (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q))
      by (apply w_Qle_nat; exact Hnat).
    assert (HassocL : (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
                    = 2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
    assert (HassocR : (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k))
                    = 3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HassocL, HassocR in H1.
    assert (E1 : (Z.of_nat (bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q
                 == (C1 * a0)%Q) by (symmetry; apply w_Qmul_nat).
    assert (E2 : (Z.of_nat (bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q
                 == (C0 * a1)%Q) by (symmetry; apply w_Qmul_nat).
    rewrite <- (w_Qmul_nat 2 (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) in H1.
    rewrite <- (w_Qmul_nat 3 (bkC (n + k) n * Datatypes.S (Datatypes.S k))) in H1.
    rewrite E1, E2 in H1.
    change (Z.of_nat 2 # 1)%Q with (2 # 1)%Q in H1.
    change (Z.of_nat 3 # 1)%Q with (3 # 1)%Q in H1.
    assert (E3 : ((2 # 1)%Q * (C1 * a0))%Q == ((2 # 1)%Q * C1 * a0)%Q) by ring.
    assert (E4 : ((3 # 1)%Q * (C0 * a1))%Q == ((3 # 1)%Q * C0 * a1)%Q) by ring.
    rewrite E3, E4 in H1. exact H1. }
  assert (Hmain : Qle ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
                      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)).
  { assert (Hxz : ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == (C1 * (a0 * Qp))%Q).
    { assert (Hcert : Qinv (a1 * ((2 # 1)%Q * Qp))
                        * (a1 * ((2 # 1)%Q * Qp)) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha1HQ).
      rewrite <- Qmult_assoc.
      transitivity (C1 * ((Qinv (a1 * ((2 # 1)%Q * Qp))
                            * (a1 * ((2 # 1)%Q * Qp))) * (a0 * Qp)))%Q.
      - ring.
      - rewrite Hcert. ring. }
    assert (Hyz : (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == ((3 # 4)%Q * C0 * a1 * ((2 # 1)%Q * Qp))%Q).
    { assert (Hcert0 : Qinv (a0 * Qp) * (a0 * Qp) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha0Q).
      rewrite <- Qmult_assoc, <- Qmult_assoc.
      transitivity ((3 # 4)%Q * C0
                      * ((Qinv (a0 * Qp) * (a0 * Qp))
                           * (a1 * ((2 # 1)%Q * Qp))))%Q.
      - ring.
      - rewrite Hcert0. ring. }
    apply (lnt_qle_mul_cancel_r
      ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)
      (((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp))%Q)).
    - apply Qmult_lt_0_compat; [exact Ha1HQ | exact Ha0Q].
    - apply (Qle_trans ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                (C1 * (a0 * Qp))%Q
                (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q).
      + apply qeqQ_le. exact Hxz.
      + apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qmult_lt_0_compat;
            [apply w_Qlt_Z1; lia | exact HQp].
        * apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- apply qeqQ_le. ring.
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                        * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ apply qeqQ_le. rewrite Hyz. ring. }
  apply (Qle_trans (lnt_pterm n (Datatypes.S k))
           (C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q
           ((3 # 4)%Q * lnt_pterm n k)%Q).
  - apply qeqQ_le. exact HsS.
  - apply (Qle_trans _ ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q _).
    + exact Hmain.
    + apply qeqQ_le.
      assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnt_pterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact Ey.
Qed.

Theorem lnt_pterm_pow : forall (n k j : nat),
  2 * n <= k + 4 -> QleT' (lnt_pterm n (k + j))
    ((lnt_pterm n k * q_pow (3 # 4)%Q j)%Q).
Proof.
  intros n k j H. induction j as [| j IH].
  - apply lnt_leT'_eq_r with (y := (lnt_pterm n k * 1)%Q).
    + cbn [q_pow]. rewrite Qmult_1_r. apply Qeq_refl.
    + apply w_qeq_leT'. replace (k + 0) with k by lia.
      rewrite Qmult_1_r. apply Qeq_refl.
  - apply lnt_leT'_eq_r with
      (y := (lnt_pterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
    + rewrite w_qpow_succ. ring.
    + apply qleT'_trans with ((3 # 4)%Q * lnt_pterm n (k + j))%Q.
      * replace (k + Datatypes.S j) with (Datatypes.S (k + j)) by lia.
        apply lnt_pterm_ratio. lia.
      * apply lnt_leT'_eq_r with
          (y := ((3 # 4)%Q * (lnt_pterm n k * q_pow (3 # 4)%Q j))%Q).
        -- ring.
        -- apply (qleT'_mult_compat_l (lnt_pterm n (k + j))
                    (lnt_pterm n k * q_pow (3 # 4)%Q j) (3 # 4)%Q
                    lnt_rho_le0 IH).
Defined.

Theorem lnt_pterm_peak : forall n k : nat,
  1 <= n -> QleT' (lnt_pterm n k) (q_pow (2 # 1)%Q (n - 1)).
Proof.
  intros n k Hn. apply Qle_to_QleT'.
  assert (Ha0 : Qlt 0 (Z.of_nat (Datatypes.S k) # 1)%Q) by (apply w_Qlt_Z1; lia).
  assert (HQp : Qlt 0 (q_pow (2 # 1)%Q (Datatypes.S k))) by apply lnt_pow2_pos.
  assert (Haz : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1)
                         * q_pow (2 # 1)%Q (Datatypes.S k))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  apply (lnt_qle_mul_cancel_r
    ((Z.of_nat (bkC (n + k) n) # 1) *
       Qinv ((Z.of_nat (Datatypes.S k) # 1) *
           q_pow (2 # 1)%Q (Datatypes.S k)))%Q
    (q_pow (2 # 1)%Q (n - 1))
    ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q).
  - exact Haz.
  - assert (Hcert : Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k))
                       * ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k)) == 1%Q)
      by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Haz).
    apply (Qle_trans (((Z.of_nat (bkC (n + k) n) # 1) *
                          Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                              q_pow (2 # 1)%Q (Datatypes.S k)))
                         * ((Z.of_nat (Datatypes.S k) # 1) *
                              q_pow (2 # 1)%Q (Datatypes.S k)))%Q
                (Z.of_nat (bkC (n + k) n) # 1)%Q
                ((q_pow (2 # 1)%Q (n - 1) *
                    ((Z.of_nat (Datatypes.S k) # 1) *
                        q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
    + apply qeqQ_le.
      transitivity ((Z.of_nat (bkC (n + k) n) # 1) *
        (Qinv ((Z.of_nat (Datatypes.S k) # 1) *
            q_pow (2 # 1)%Q (Datatypes.S k)) *
          ((Z.of_nat (Datatypes.S k) # 1) *
            q_pow (2 # 1)%Q (Datatypes.S k))))%Q.
      * ring.
      * rewrite Hcert. ring.
    + assert (Hbr : (Z.of_nat (2 ^ (n + k)) # 1)%Q
                    == (q_pow (2 # 1)%Q (n - 1) *
                          q_pow (2 # 1)%Q (Datatypes.S k))%Q).
      { replace (n + k) with ((n - 1) + Datatypes.S k) by lia.
        rewrite <- lnt_qpow_Zofnat, w_qpow_add. reflexivity. }
      apply (Qle_trans (Z.of_nat (bkC (n + k) n) # 1)%Q
              (Z.of_nat (2 ^ (n + k)) # 1)%Q
              ((q_pow (2 # 1)%Q (n - 1) *
                  ((Z.of_nat (Datatypes.S k) # 1) *
                      q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
      * apply w_Qle_nat. apply lng2_bkC_le_pow2.
      * apply (Qle_trans _ (q_pow (2 # 1)%Q (n - 1) *
                               q_pow (2 # 1)%Q (Datatypes.S k))%Q _).
        -- apply qeqQ_le. exact Hbr.
        -- apply (Qle_trans
              (q_pow (2 # 1)%Q (n - 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 (1 * q_pow (2 # 1)%Q (Datatypes.S k)))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 ((Z.of_nat (Datatypes.S k) # 1) *
                    q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** apply qeqQ_le. ring.
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** assert (H1a0 : Qle 1 (Z.of_nat (Datatypes.S k) # 1)%Q)
                   by (apply (w_Qle_nat 1 (Datatypes.S k)); lia).
                 apply Qmult_le_compat_r;
                   [exact H1a0 | apply Qlt_le_weak; exact HQp].
Qed.

(* ============================================================ *)
(* Section E: the sharp-weight term family w(n,k) = u(n,k)+u~(n,k),    *)
(*   the (1+t) weight lift of the pole series.                         *)
(* ============================================================ *)

Definition lnw_uterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
        q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

Definition lnw_wterm (n k : nat) : Q :=
  (lnt_pterm n k + lnw_uterm n k)%Q.

Lemma lnw_zpos_of_bkC : forall n k : nat, (0 < Z.of_nat (bkC (n + k) n))%Z.
Proof.
  intros n k.
  assert (Hb : 1 <= bkC (n + k) n) by (apply w_bkC_pos; lia).
  exact (proj1 (Nat2Z.inj_lt 0%nat (bkC (n + k) n)) Hb).
Qed.

Theorem lnw_uterm_pos : forall n k : nat, QltT 0 (lnw_uterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnw_uterm, Qdiv.
  apply Qmult_lt_0_compat.
  - apply w_Qlt_Z1. apply lnw_zpos_of_bkC.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply w_Qlt_Z1. lia.
    + apply lnt_pow2_pos.
Qed.

Lemma lnw_qZ_le0 : forall z : Z, (0 <= z)%Z -> QleT' 0 (z # 1)%Q.
Proof.
  intros z Hz. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Defined.

Lemma lnw_q2_le0 : QleT' 0 (2 # 1)%Q.
Proof. apply lnw_qZ_le0. lia. Defined.

Lemma lnw_qinv_den_le : forall (a d1 d2 p : Q),
  Qlt 0 a -> Qle d1 d2 -> Qlt 0 d1 -> Qlt 0 p ->
  Qle (a * Qinv (d2 * p)) (a * Qinv (d1 * p)).
Proof.
  intros a d1 d2 p Ha Hd Hd1 Hp.
  assert (Hd2 : Qlt 0 d2) by (apply (Qlt_le_trans 0%Q d1 d2); assumption).
  assert (Hc1 : Qinv (d2 * p) * (d2 * p) == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0;
        apply Qmult_lt_0_compat; assumption).
  assert (Hc2 : Qinv (d1 * p) * (d1 * p) == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0;
        apply Qmult_lt_0_compat; assumption).
  assert (EL : ((a * Qinv (d2 * p)) * ((d1 * p) * (d2 * p)))%Q
             == (a * (d1 * p))%Q).
  { transitivity (a * ((Qinv (d2 * p) * (d2 * p)) * (d1 * p)))%Q.
    - ring.
    - rewrite Hc1. ring. }
  assert (ER : ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q
             == (a * (d2 * p))%Q).
  { transitivity (a * ((Qinv (d1 * p) * (d1 * p)) * (d2 * p)))%Q.
    - ring.
    - rewrite Hc2. ring. }
  apply (lnt_qle_mul_cancel_r
    (a * Qinv (d2 * p)) (a * Qinv (d1 * p)) (((d1 * p) * (d2 * p))%Q)).
  - apply Qmult_lt_0_compat; apply Qmult_lt_0_compat; assumption.
  - apply (Qle_trans ((a * Qinv (d2 * p)) * ((d1 * p) * (d2 * p)))%Q
             (a * (d1 * p))%Q
             ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q).
    + apply qeqQ_le. exact EL.
    + apply (Qle_trans (a * (d1 * p))%Q (a * (d2 * p))%Q
               ((a * Qinv (d1 * p)) * ((d1 * p) * (d2 * p)))%Q).
      * apply lnt_Qmult_le_compat_l.
        -- apply Qlt_le_weak. exact Ha.
        -- apply Qmult_le_compat_r; [exact Hd | apply Qlt_le_weak; exact Hp].
      * apply qeqQ_le. symmetry. exact ER.
Qed.

Theorem lnw_uterm_le : forall n k : nat, QleT' (lnw_uterm n k) (lnt_pterm n k).
Proof.
  intros n k. apply Qle_to_QleT'.
  unfold lnw_uterm, lnt_pterm, Qdiv.
  apply lnw_qinv_den_le.
  - apply w_Qlt_Z1. apply lnw_zpos_of_bkC.
  - apply w_Qle_nat. lia.
  - apply w_Qlt_Z1. lia.
  - apply lnt_pow2_pos.
Qed.

Theorem lnw_wterm_pos : forall n k : nat, QltT 0 (lnw_wterm n k).
Proof.
  intros n k. apply qltT_leT'_ltT with (y := lnw_uterm n k).
  - apply lnw_uterm_pos.
  - apply Qle_to_QleT'. unfold lnw_wterm.
    apply (Qle_trans (lnw_uterm n k) ((lnw_uterm n k + lnt_pterm n k)%Q)
             ((lnt_pterm n k + lnw_uterm n k)%Q)).
    + apply (Qle_trans (lnw_uterm n k) ((lnw_uterm n k + 0)%Q)
               ((lnw_uterm n k + lnt_pterm n k)%Q)).
      * apply qeqQ_le. ring.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply QleT'_to_Qle. apply qltT_leT'. apply lnt_pterm_pos.
    + apply qeqQ_le. ring.
Qed.

Theorem lnw_wterm_ge : forall n k : nat, QleT' (lnt_pterm n k) (lnw_wterm n k).
Proof.
  intros n k. apply Qle_to_QleT'. unfold lnw_wterm.
  apply (Qle_trans (lnt_pterm n k) ((lnt_pterm n k + 0)%Q)
           ((lnt_pterm n k + lnw_uterm n k)%Q)).
  - apply qeqQ_le. ring.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply qltT_leT'. apply lnw_uterm_pos.
Qed.

Theorem lnw_wterm_le2 : forall n k : nat,
  QleT' (lnw_wterm n k) ((2 # 1)%Q * lnt_pterm n k)%Q.
Proof.
  intros n k. apply qleT'_trans with ((lnt_pterm n k + lnt_pterm n k)%Q).
  - apply qleT'_plus_compat; [apply qleT'_refl | apply lnw_uterm_le].
  - apply w_qeq_leT'. unfold lnw_wterm. ring.
Defined.

Theorem lnw_wterm_peak : forall n k : nat,
  1 <= n -> QleT' (lnw_wterm n k) (q_pow (2 # 1)%Q n).
Proof.
  intros n k Hn.
  assert (E2n : q_pow (2 # 1)%Q n == ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q).
  { assert (Hm : exists m : nat, n = Datatypes.S m) by (exists (n - 1); lia).
    destruct Hm as [m Hm]. subst n.
    rewrite w_qpow_succ.
    replace (Datatypes.S m - 1) with m by lia.
    apply Qeq_refl. }
  apply qleT'_trans with ((2 # 1)%Q * lnt_pterm n k)%Q.
  - apply lnw_wterm_le2.
  - apply lnt_leT'_eq_r with (y := ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q).
    + apply Qeq_sym. exact E2n.
    + apply qleT'_trans with ((2 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q.
      * apply qleT'_mult_compat_l;
          [apply lnw_q2_le0 | apply lnt_pterm_peak; exact Hn].
      * apply qleT'_refl.
Defined.

(* ============================================================ *)
(* Section F: quadratic decay kernel and the theta := 4/5 budget.      *)
(* ============================================================ *)

Lemma lnt2_sq_nonneg : forall s : Q, QleT' 0 (s * s)%Q.
Proof.
  intros s. apply Qle_to_QleT'.
  destruct (Qlt_le_dec s 0) as [Hlt | Hle].
  - assert (Hn : Qlt 0 (Qopp s)) by (apply (Qopp_lt_compat s 0); exact Hlt).
    apply (Qle_trans 0%Q ((Qopp s) * (Qopp s))%Q (s * s)%Q).
    + apply Qmult_le_0_compat; apply Qlt_le_weak; exact Hn.
    + apply qeqQ_le. ring.
  - apply Qmult_le_0_compat; exact Hle.
Qed.

Lemma lnt2_nat_cancel_r : forall a b p : nat,
  0 < p -> a * p <= b * p -> a <= b.
Proof.
  intros a b p Hp H. apply (proj2 (Nat.mul_le_mono_pos_r a b p Hp)). exact H.
Qed.

Lemma lnt2_key_of_ge : forall n k : nat,
  2 * n <= k -> 2 * n * (k + 2) <= (k + 1) * (k + 5).
Proof.
  intros n k H.
  assert (H1 : 2 * n * k <= k * k) by (apply Nat.mul_le_mono_r; lia).
  assert (H2 : 2 * n * 2 <= k * 2) by (apply Nat.mul_le_mono_r; lia).
  assert (H3 : 0 <= k * k) by (apply (Nat.mul_le_mono 0 k 0 k); lia).
  lia.
Qed.

Lemma lnt2_key_lin : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) -> 2 * n <= k + 4.
Proof.
  intros n k H.
  destruct (le_lt_dec (2 * n) (k + 4)) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hlow : (k + 5) * (k + 2) <= 2 * n * (k + 2))
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Lemma lnt2_key_mono : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (Datatypes.S k + 2) <= (Datatypes.S k + 1) * (Datatypes.S k + 5).
Proof.
  intros n k H.
  pose proof (lnt2_key_lin n k H) as Hlin.
  assert (H1 : 2 * n * k <= (k + 4) * k)
    by (apply (Nat.mul_le_mono_r (2 * n) (k + 4) k); exact Hlin).
  assert (H2 : 2 * n * 3 <= (k + 4) * 3)
    by (apply (Nat.mul_le_mono_r (2 * n) (k + 4) 3); exact Hlin).
  lia.
Qed.

Lemma lnt2_key_shift : forall (n k d : nat),
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (k + d + 2) <= (k + d + 1) * (k + d + 5).
Proof.
  intros n k d H. induction d as [| d IHd].
  - rewrite !Nat.add_0_r. exact H.
  - replace (k + Datatypes.S d) with (Datatypes.S (k + d)) by lia.
    exact (lnt2_key_mono n (k + d) IHd).
Qed.

Lemma lnt2_key_at : forall (n k m : nat),
  k <= m ->
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  2 * n * (m + 2) <= (m + 1) * (m + 5).
Proof.
  intros n k m Hkm H.
  assert (Hd := lnt2_key_shift n k (m - k) H).
  replace (k + (m - k) + 2) with (m + 2) in Hd by lia.
  replace (k + (m - k) + 1) with (m + 1) in Hd by lia.
  replace (k + (m - k) + 5) with (m + 5) in Hd by lia.
  exact Hd.
Qed.

Lemma lnt2_pow_nonneg : forall (n : nat) (a : Q), Qle 0 a -> Qle 0 (q_pow a n).
Proof.
  intros n a Ha. induction n as [| n IHn].
  - cbn [q_pow]. unfold Qle. cbn [Qnum Qden]. lia.
  - rewrite w_qpow_succ. apply Qmult_le_0_compat; [exact Ha | exact IHn].
Qed.

Lemma lnt2_pow_mono : forall (n : nat) (a b : Q),
  Qle 0 a -> Qle a b -> Qle (q_pow a n) (q_pow b n).
Proof.
  intros n a b Ha0 Hab.
  assert (Hb0 : Qle 0 b) by (apply (Qle_trans 0%Q a b); assumption).
  induction n as [| n IHn].
  - cbn [q_pow]. apply Qle_refl.
  - rewrite w_qpow_succ, w_qpow_succ.
    apply (Qle_trans (a * q_pow a n)%Q (b * q_pow a n)%Q (b * q_pow b n)%Q).
    + apply Qmult_le_compat_r; [exact Hab | apply lnt2_pow_nonneg; exact Ha0].
    + apply lnt_Qmult_le_compat_l; [exact Hb0 | exact IHn].
Qed.

Lemma lnt2_pow_mul : forall (n : nat) (a b : Q),
  q_pow a n * q_pow b n == q_pow (a * b)%Q n.
Proof.
  intros n a b. induction n as [| n IHn].
  - cbn [q_pow]. ring.
  - rewrite w_qpow_succ, w_qpow_succ, w_qpow_succ. rewrite <- IHn. ring.
Qed.

Theorem lnt2_hquad : forall t : Q,
  QleT' ((40 # 1)%Q * (t * (1 - t)))%Q
        ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q.
Proof.
  intros t.
  assert (Hsq : Qle 0 ((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47)))%Q)).
  { apply Qmult_le_0_compat.
    - unfold Qle. cbn [Qnum Qden]. lia.
    - apply QleT'_to_Qle. apply lnt2_sq_nonneg. }
  assert (Hsum : Qle 0 (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47)))
                           + (160 # 47))%Q)).
  { apply (Qle_trans 0%Q ((0 + 0)%Q)
             (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                + (160 # 47))%Q).
    - apply qeqQ_le. ring.
    - apply Qplus_le_compat.
      + exact Hsq.
      + unfold Qle. cbn [Qnum Qden]. lia. }
  apply Qle_to_QleT'.
  apply (Qle_trans ((40 # 1)%Q * (t * (1 - t)))%Q
           (((40 # 1)%Q * (t * (1 - t)))
              + (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                 + (160 # 47)))%Q
           ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q).
  - apply (Qle_trans ((40 # 1)%Q * (t * (1 - t)))%Q
             (((40 # 1)%Q * (t * (1 - t))) + 0)%Q
             (((40 # 1)%Q * (t * (1 - t)))
                + (((47 # 1)%Q * ((t - (13 # 47)) * (t - (13 # 47))))
                   + (160 # 47)))%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply Qplus_le_compat; [apply Qle_refl | exact Hsum].
  - apply qeqQ_le. ring.
Qed.

Theorem lnt2_hquad_pow : forall (n : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  QleT' (q_pow ((40 # 1)%Q * (t * (1 - t)))%Q n)
        (q_pow ((7 # 1)%Q * ((1 + t) * (1 + t)))%Q n).
Proof.
  intros n t Ht0 Ht1.
  assert (Hs : Qle 0 (1 - t)%Q).
  { pose proof (proj2 (Qplus_le_r t 1 (Qopp t)) Ht1) as Hm.
    apply (Qle_trans 0%Q (Qopp t + t)%Q (1 - t)%Q).
    - apply qeqQ_le. ring.
    - apply (Qle_trans (Qopp t + t)%Q (Qopp t + 1)%Q (1 - t)%Q).
      + exact Hm.
      + apply qeqQ_le. ring. }
  apply Qle_to_QleT'. apply lnt2_pow_mono.
  - apply Qmult_le_0_compat.
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qmult_le_0_compat; [exact Ht0 | exact Hs].
  - apply QleT'_to_Qle. apply lnt2_hquad.
Qed.

Theorem lnt2_theta_budget : forall n : nat,
  QleT' (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow (4 # 5)%Q n)%Q.
Proof.
  intros n.
  apply (qleT'_trans (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q
           (q_pow ((4 # 1)%Q * (7 # 40)%Q)%Q n) (q_pow (4 # 5)%Q n)).
  - apply lnt_leT'_eq_l with (x := q_pow ((4 # 1)%Q * (7 # 40)%Q)%Q n).
    + apply Qeq_sym. apply lnt2_pow_mul.
    + apply qleT'_refl.
  - apply Qle_to_QleT'. apply lnt2_pow_mono.
    + unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    + unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Defined.

Theorem lnt2_uterm_ratio34 : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_uterm n (Datatypes.S k)) ((3 # 4)%Q * lnw_uterm n k)%Q.
Proof.
  intros n k H. apply Qle_to_QleT'.
  assert (HsS : lnw_uterm n (Datatypes.S k)
    == ((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S k))) # 1) *
                ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
  { unfold lnw_uterm, Qdiv.
    replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    rewrite (w_qpow_succ (2 # 1)%Q (Datatypes.S k)). reflexivity. }
  assert (HsT : lnw_uterm n k
    == ((Z.of_nat (bkC (n + k) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
  { unfold lnw_uterm, Qdiv. reflexivity. }
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + k) n) # 1)%Q).
  set (a1 := (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q).
  set (a0 := (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q).
  set (Qp := q_pow (2 # 1)%Q (Datatypes.S k)).
  assert (Ha1 : Qlt 0 a1) by (apply w_Qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply w_Qlt_Z1; lia).
  assert (HQp : Qlt 0 Qp) by apply lnt_pow2_pos.
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat; [exact Ha1 | apply Qmult_lt_0_compat;
         [apply w_Qlt_Z1; lia | exact HQp]]).
  assert (Ha0Q : Qlt 0 (a0 * Qp)%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hnat : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
               <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))).
  { pose proof (lnt_bkC_step n k) as Hstep.
    assert (Hkey : 2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k)
                 <= 3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k).
    { assert (E1 : 2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k)
                 = 2 * n * Datatypes.S (Datatypes.S k)
                   + 2 * Datatypes.S k * Datatypes.S (Datatypes.S k)) by ring.
      rewrite E1. lia. }
    assert (Hm : bkC (n + k) n * (2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k))
               <= bkC (n + k) n
                    * (3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k))
      by (apply Nat.mul_le_mono_l; exact Hkey).
    assert (HeqL : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                     * Datatypes.S k
                 = bkC (n + k) n
                     * (2 * (n + Datatypes.S k) * Datatypes.S (Datatypes.S k))).
    { replace (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                 * Datatypes.S k)
        with (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)
                * Datatypes.S (Datatypes.S k)) by ring.
      rewrite Hstep. ring. }
    assert (HeqR : 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))
                     * Datatypes.S k
                 = bkC (n + k) n
                     * (3 * Datatypes.S (Datatypes.S (Datatypes.S k)) * Datatypes.S k))
      by ring.
    assert (Hscaled : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)
                        * Datatypes.S k
                    <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))
                         * Datatypes.S k).
    { rewrite HeqL, HeqR. exact Hm. }
    apply (lnt2_nat_cancel_r _ _ (Datatypes.S k) ltac:(lia) Hscaled). }
  assert (HQcore : Qle ((2 # 1)%Q * C1 * a0) ((3 # 1)%Q * C0 * a1)).
  { assert (H1 : Qle ((Z.of_nat (2 * bkC (Datatypes.S (n + k)) n
                          * Datatypes.S (Datatypes.S k)) # 1)%Q)
                     ((Z.of_nat (3 * bkC (n + k) n
                          * Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q))
      by (apply w_Qle_nat; exact Hnat).
    assert (HassocL : (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k))
                    = 2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S (Datatypes.S k)))
      by ring.
    assert (HassocR : (3 * bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k)))
                    = 3 * (bkC (n + k) n * Datatypes.S (Datatypes.S (Datatypes.S k))))
      by ring.
    rewrite HassocL, HassocR in H1.
    assert (E1 : (Z.of_nat (bkC (Datatypes.S (n + k)) n
                    * Datatypes.S (Datatypes.S k)) # 1)%Q
                 == (C1 * a0)%Q) by (symmetry; apply w_Qmul_nat).
    assert (E2 : (Z.of_nat (bkC (n + k) n
                    * Datatypes.S (Datatypes.S (Datatypes.S k))) # 1)%Q
                 == (C0 * a1)%Q) by (symmetry; apply w_Qmul_nat).
    rewrite <- (w_Qmul_nat 2 (bkC (Datatypes.S (n + k)) n
                   * Datatypes.S (Datatypes.S k))) in H1.
    rewrite <- (w_Qmul_nat 3 (bkC (n + k) n
                   * Datatypes.S (Datatypes.S (Datatypes.S k)))) in H1.
    rewrite E1, E2 in H1.
    change (Z.of_nat 2 # 1)%Q with (2 # 1)%Q in H1.
    change (Z.of_nat 3 # 1)%Q with (3 # 1)%Q in H1.
    assert (E3 : ((2 # 1)%Q * (C1 * a0))%Q == ((2 # 1)%Q * C1 * a0)%Q) by ring.
    assert (E4 : ((3 # 1)%Q * (C0 * a1))%Q == ((3 # 1)%Q * C0 * a1)%Q) by ring.
    rewrite E3, E4 in H1. exact H1. }
  assert (Hmain : Qle ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
                      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)).
  { assert (Hxz : ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == (C1 * (a0 * Qp))%Q).
    { assert (Hcert : Qinv (a1 * ((2 # 1)%Q * Qp))
                        * (a1 * ((2 # 1)%Q * Qp)) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha1HQ).
      rewrite <- Qmult_assoc.
      transitivity (C1 * ((Qinv (a1 * ((2 # 1)%Q * Qp))
                            * (a1 * ((2 # 1)%Q * Qp))) * (a0 * Qp)))%Q.
      - ring.
      - rewrite Hcert. ring. }
    assert (Hyz : (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == ((3 # 4)%Q * C0 * a1 * ((2 # 1)%Q * Qp))%Q).
    { assert (Hcert0 : Qinv (a0 * Qp) * (a0 * Qp) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha0Q).
      rewrite <- Qmult_assoc, <- Qmult_assoc.
      transitivity ((3 # 4)%Q * C0
                      * ((Qinv (a0 * Qp) * (a0 * Qp))
                           * (a1 * ((2 # 1)%Q * Qp))))%Q.
      - ring.
      - rewrite Hcert0. ring. }
    apply (lnt_qle_mul_cancel_r
      ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)
      (((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp))%Q)).
    - apply Qmult_lt_0_compat; [exact Ha1HQ | exact Ha0Q].
    - apply (Qle_trans ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                (C1 * (a0 * Qp))%Q
                (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q).
      + apply qeqQ_le. exact Hxz.
      + apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qmult_lt_0_compat;
            [apply w_Qlt_Z1; lia | exact HQp].
        * apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- apply qeqQ_le. ring.
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                        * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ apply qeqQ_le. rewrite Hyz. ring. }
  apply (Qle_trans (lnw_uterm n (Datatypes.S k))
           (C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q
           ((3 # 4)%Q * lnw_uterm n k)%Q).
  - apply qeqQ_le. exact HsS.
  - apply (Qle_trans _ ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q _).
    + exact Hmain.
    + apply qeqQ_le.
      assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnw_uterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact Ey.
Qed.

Theorem lnt2_pterm_ratio34 : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnt_pterm n (Datatypes.S k)) ((3 # 4)%Q * lnt_pterm n k)%Q.
Proof.
  intros n k H. apply lnt_pterm_ratio.
  pose proof (lnt2_key_lin n k H). lia.
Qed.

Theorem lnt2_wterm_step : forall n k : nat,
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_wterm n (Datatypes.S k)) ((3 # 4)%Q * lnw_wterm n k)%Q.
Proof.
  intros n k H.
  apply (qleT'_trans (lnw_wterm n (Datatypes.S k))
           ((lnt_pterm n (Datatypes.S k) + lnw_uterm n (Datatypes.S k))%Q)
           ((3 # 4)%Q * lnw_wterm n k)%Q).
  - apply w_qeq_leT'. reflexivity.
  - apply (qleT'_trans
             ((lnt_pterm n (Datatypes.S k) + lnw_uterm n (Datatypes.S k))%Q)
             (((3 # 4)%Q * lnt_pterm n k + (3 # 4)%Q * lnw_uterm n k)%Q)
             ((3 # 4)%Q * lnw_wterm n k)%Q).
    + apply qleT'_plus_compat;
        [apply lnt2_pterm_ratio34; exact H | apply lnt2_uterm_ratio34; exact H].
    + apply w_qeq_leT'. unfold lnw_wterm. ring.
Defined.

Theorem lnt2_wterm_pow_pure : forall (n k j : nat),
  2 * n * (k + 2) <= (k + 1) * (k + 5) ->
  QleT' (lnw_wterm n (k + j)) (lnw_wterm n k * q_pow (3 # 4)%Q j)%Q.
Proof.
  intros n k j H. induction j as [| j IHj].
  - apply lnt_leT'_eq_r with (y := (lnw_wterm n k * 1)%Q).
    + cbn [q_pow]. ring.
    + replace (k + 0) with k by lia. apply w_qeq_leT'. ring.
  - replace (k + Datatypes.S j) with (Datatypes.S (k + j)) by lia.
    apply lnt_leT'_eq_r with
      (y := (lnw_wterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
    + rewrite w_qpow_succ. apply Qeq_refl.
    + apply (qleT'_trans (lnw_wterm n (Datatypes.S (k + j)))
               ((3 # 4)%Q * lnw_wterm n (k + j))%Q
               (lnw_wterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
      * apply lnt2_wterm_step.
        apply (lnt2_key_at n k (k + j)); [lia | exact H].
      * apply lnt_leT'_eq_r with
          (y := ((3 # 4)%Q * (lnw_wterm n k * q_pow (3 # 4)%Q j))%Q).
        -- ring.
        -- apply (qleT'_mult_compat_l (lnw_wterm n (k + j))
                     (lnw_wterm n k * q_pow (3 # 4)%Q j) (3 # 4)%Q
                     lnt_rho_le0 IHj).
Defined.

Theorem lnt2_wterm_tail_pure : forall (n M d : nat),
  2 * n <= M + 1 ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  assert (Hkey : 2 * n * (Datatypes.S M + 2)
               <= (Datatypes.S M + 1) * (Datatypes.S M + 5))
    by (apply lnt2_key_of_ge; lia).
  apply qleT'_trans with
    (lnw_wterm n (Datatypes.S M)
       * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q.
  - apply lnt_leT'_eq_r with
      (y := sum_upto d (fun i : nat =>
                              (lnw_wterm n (Datatypes.S M)
                                  * q_pow (3 # 4)%Q i)%Q)).
    + rewrite lnt_sum_scale, lnt_geo_partial. apply Qeq_refl.
    + apply lnt_sum_le. intros i Hi.
      apply (qleT'_trans (lnw_wterm n (M + Datatypes.S i))
              (lnw_wterm n (Datatypes.S M + i))
              (lnw_wterm n (Datatypes.S M) * q_pow (3 # 4)%Q i)).
      * apply w_qeq_leT'.
        replace (M + Datatypes.S i) with (Datatypes.S M + i) by lia.
        apply Qeq_refl.
      * apply (lnt2_wterm_pow_pure n (Datatypes.S M) i).
        exact Hkey.
  - apply qleT'_trans with
      (lnw_wterm n (Datatypes.S M) * ((4 # 1)%Q * 1)%Q)%Q.
    + apply (qleT'_mult_compat_l ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)
               ((4 # 1)%Q * 1)%Q (lnw_wterm n (Datatypes.S M))).
      * apply qltT_leT'. apply lnw_wterm_pos.
      * apply qleT'_mult_compat_l.
        { apply lnt_q4_le0. }
        { apply lnt_sub_le1. apply lnt_pow_pos_le. }
    + apply w_qeq_leT'. ring.
Defined.

Theorem lnt2_wgap_pure : forall (n M d : nat),
  2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + (4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply Qle_to_QleT'. apply Qplus_le_compat.
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnt2_wterm_tail_pure. exact H.
Qed.

Theorem lnt2_wgap_geo_quarter : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q)%Q.
  - apply lnt2_wgap_pure. exact HM.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hkey2n : 2 * n * (2 * n + 2) <= (2 * n + 1) * (2 * n + 5))
        by (apply lnt2_key_of_ge; lia).
      assert (Hpow := lnt2_wterm_pow_pure n (2 * n)
                        (Datatypes.S M - 2 * n) Hkey2n).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnw_wterm n (2 * n)) (q_pow (2 # 1)%Q n))
        by (apply lnw_wterm_peak; exact Hn).
      assert (Hchain : QleT' (lnw_wterm n (Datatypes.S M))
                         (q_pow (2 # 1)%Q n
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))).
      { apply qleT'_trans with
          ((lnw_wterm n (2 * n))
             * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q.
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnw_wterm n (2 * n))
                   (q_pow (2 # 1)%Q n)
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))
                      (((4 # 1)%Q * q_pow (2 # 1)%Q n)
                         * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      { apply qleT'_trans with
          ((4 # 1)%Q
             * (q_pow (2 # 1)%Q n
                  * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
        - apply (qleT'_mult_compat_l (lnw_wterm n (Datatypes.S M))
                   (q_pow (2 # 1)%Q n
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)) (4 # 1)%Q
                   (lnt_q4_le0) Hchain).
        - apply w_qeq_leT'. ring. }
      assert (E42 : ((4 # 1)%Q * q_pow (2 # 1)%Q n)%Q
                   == q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))).
      { replace (Datatypes.S (Datatypes.S n)) with (2 + n) by lia.
        rewrite w_qpow_add. cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        ((4 # 1)%Q * lnw_wterm n (Datatypes.S M))%Q
        (((4 # 1)%Q * q_pow (2 # 1)%Q n)
           * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q
        (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
           * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      * rewrite E42. apply Qeq_refl.
      * exact Hxy.
Defined.

(* ============================================================ *)
(* Section G: discrete transport generics and the full-container band. *)
(* ============================================================ *)

Definition lnt3_nlt (k M : nat) : Set := Id (Nat.ltb k M) true.

Lemma lnt3_nlt_drop : forall k M : nat, lnt3_nlt k M -> (k < M)%nat.
Proof.
  intros k M H. unfold lnt3_nlt in H. destruct (Nat.ltb k M) eqn:E.
  - apply (proj1 (Nat.ltb_lt k M)). exact E.
  - inversion H.
Qed.

Lemma lnt3_nlt_lift : forall k M : nat, (k < M)%nat -> lnt3_nlt k M.
Proof.
  intros k M H. unfold lnt3_nlt. destruct (Nat.ltb k M) eqn:E.
  - apply id_refl.
  - exfalso. apply (proj2 (Nat.ltb_lt k M)) in H. rewrite H in E. discriminate E.
Defined.

Lemma lnt3_qscale_succ : forall (M : nat) (B : Q),
  ((Z.of_nat (Datatypes.S M) # 1) * B)%Q == (((Z.of_nat M # 1) * B + B)%Q).
Proof.
  intros M B.
  assert (Hz : (Z.of_nat (Datatypes.S M) # 1)%Q == ((Z.of_nat M # 1)%Q + 1)%Q).
  { assert (Hn : Z.of_nat (Datatypes.S M) = (Z.of_nat M + 1)%Z) by lia.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult]. rewrite Hn. lia. }
  rewrite Hz. ring.
Qed.

Lemma lnt3_rho_pow_anti : forall d e : nat, d <= e ->
  QleT' (q_pow (3 # 4)%Q e) (q_pow (3 # 4)%Q d).
Proof.
  intros d e. revert d. induction e as [| e IHe]; intros d Hde.
  - replace d with 0%nat by lia. apply qleT'_refl.
  - destruct (Nat.eq_dec d (Datatypes.S e)) as [Hd | Hd].
    + rewrite Hd. apply qleT'_refl.
    + assert (Hle : d <= e) by lia.
      apply (qleT'_trans (q_pow (3 # 4)%Q (Datatypes.S e))
              ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q (q_pow (3 # 4)%Q d)).
      * apply lnt_leT'_eq_l with (x := ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q).
        -- rewrite w_qpow_succ. apply Qeq_refl.
        -- apply qleT'_refl.
      * apply (qleT'_trans ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q
                (q_pow (3 # 4)%Q e) (q_pow (3 # 4)%Q d)).
        -- apply lnt_leT'_eq_r with (y := (1 * q_pow (3 # 4)%Q e)%Q).
           ++ ring.
           ++ apply Qle_to_QleT'. apply Qmult_le_compat_r.
              ** unfold Qle. cbn [Qnum Qden]. lia.
              ** apply QleT'_to_Qle. apply lnt_pow_pos_le.
        -- apply IHe. exact Hle.
Defined.

Theorem lnt3_sum_bmax : forall (M : nat) (P : nat -> Q) (B : Q),
  (forall k : nat, lnt3_nlt k M -> QleT' (P k) B) ->
  QleT' (sum_upto M P) ((Z.of_nat M # 1) * B)%Q.
Proof.
  intros M P B. induction M as [| M IH]; intros Hpt.
  - apply lnt_leT'_eq_r with (y := 0%Q).
    + cbn [Z.of_nat]. ring.
    + cbn [sum_upto]. apply qleT'_refl.
  - cbn [sum_upto].
    apply (qleT'_trans (sum_upto M P + P M)%Q
            ((Z.of_nat M # 1) * B + B)%Q
            ((Z.of_nat (Datatypes.S M) # 1) * B)%Q).
    + apply qleT'_plus_compat.
      * apply IH. intros k Hk. apply Hpt. apply lnt3_nlt_lift.
        pose proof (lnt3_nlt_drop k M Hk). lia.
      * apply Hpt. apply lnt3_nlt_lift. lia.
    + apply w_qeq_leT'. symmetry. apply lnt3_qscale_succ.
Defined.

Theorem lnt3_wsum_peak : forall (n M : nat), 1 <= n ->
  QleT' (sum_upto M (lnw_wterm n))
        ((Z.of_nat M # 1) * q_pow (2 # 1)%Q n)%Q.
Proof.
  intros n M Hn. apply lnt3_sum_bmax. intros k Hk.
  apply lnw_wterm_peak. exact Hn.
Defined.

Theorem lnt3_wpt_band : forall (n m : nat), 1 <= n -> 2 * n <= m ->
  QleT' (lnw_wterm n m)
        (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (m - 2 * n))%Q.
Proof.
  intros n m Hn Hm.
  assert (Hkey : 2 * n * (2 * n + 2) <= (2 * n + 1) * (2 * n + 5))
    by (apply lnt2_key_of_ge; lia).
  pose proof (lnt2_wterm_pow_pure n (2 * n) (m - 2 * n) Hkey) as Hp.
  replace (2 * n + (m - 2 * n)) with m in Hp by lia.
  apply (qleT'_trans (lnw_wterm n m)
          (lnw_wterm n (2 * n) * q_pow (3 # 4)%Q (m - 2 * n))%Q
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (m - 2 * n))%Q).
  - exact Hp.
  - apply (qleT'_mult_compat_r (lnw_wterm n (2 * n)) (q_pow (2 # 1)%Q n)
             (q_pow (3 # 4)%Q (m - 2 * n)) (lnt_pow_pos_le (m - 2 * n))).
    apply lnw_wterm_peak. exact Hn.
Defined.

Theorem lnt3_wtail_window : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((Z.of_nat d # 1)
           * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
Proof.
  intros n M d Hn HM. apply lnt3_sum_bmax. intros i Hi.
  assert (Hp2 : QleT' 0 (q_pow (2 # 1)%Q n))
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply lnt_pow2_pos).
  apply (qleT'_trans (lnw_wterm n (M + Datatypes.S i))
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (M + Datatypes.S i - 2 * n))%Q
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
  - apply lnt3_wpt_band; [exact Hn | lia].
  - apply (qleT'_mult_compat_l
             (q_pow (3 # 4)%Q (M + Datatypes.S i - 2 * n))
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
             (q_pow (2 # 1)%Q n) Hp2).
    apply lnt3_rho_pow_anti. lia.
Defined.

Theorem lnt3_wsum_band_total : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
        ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
         + (Z.of_nat d # 1)
             * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
Proof.
  intros n M d Hn HM.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (lnw_wterm n)
       + sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
    ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
     + (Z.of_nat d # 1)
         * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply qleT'_plus_compat.
    + apply lnt3_wsum_peak. exact Hn.
    + exact (lnt3_wtail_window n M d Hn HM).
Defined.

(* ============================================================ *)
(* Section H: growth budget A_n := 2^n * q~_n and its compose form.    *)
(* ============================================================ *)

Lemma lng2_psd_scale : forall (N c : nat) (f : nat -> nat),
  bk_psd (fun k => c * f k) N = c * bk_psd f N.
Proof.
  induction N as [| N IH]; intros c f.
  - cbn [bk_psd]. ring.
  - cbn [bk_psd]. rewrite (IH c f). ring.
Qed.

Lemma lng2_pow_mul_l : forall a b n : nat, (a * b) ^ n = a ^ n * b ^ n.
Proof.
  intros a b n. induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

Lemma lng2_qtilde_le_6pow : forall n : nat, bk_Qn_qtilde n <= 6 ^ n.
Proof.
  intro n. unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, NatLe (Datatypes.S k) (Datatypes.S n) ->
            NatLe (bkC n k * bkC n k) (2 ^ n * bkC n k)).
  { intro k. intro Hk. apply NatLe_lift. apply Nat.mul_le_mono_r.
    apply lng2_bkC_le_pow2. }
  pose proof (bk_psd_mono (Datatypes.S n) (fun k => bkC n k * bkC n k)
              (fun k => 2 ^ n * bkC n k) Hpt) as Hmono.
  transitivity (2 ^ n * bk_psd (fun k => bkC n k) (Datatypes.S n))%nat.
  - rewrite <- (lng2_psd_scale (Datatypes.S n) (2 ^ n) (fun k => bkC n k)).
    apply NatLe_drop. exact Hmono.
  - rewrite (S07_RealSetoidExpLog.RealSetoid.Id_eq _ _ (bk_psd_binom n)).
    replace 6 with (2 * 3)%nat by lia.
    rewrite lng2_pow_mul_l. lia.
Qed.

Definition lng2_An (n : nat) : nat := 2 ^ n * bk_Qn_qtilde n.

Theorem lng2_An_le_12pow : forall n : nat, lng2_An n <= 12 ^ n.
Proof.
  intro n. unfold lng2_An.
  transitivity (2 ^ n * 6 ^ n)%nat.
  - apply Nat.mul_le_mono_l. apply lng2_qtilde_le_6pow.
  - replace 12 with (2 * 6)%nat by lia.
    rewrite lng2_pow_mul_l. lia.
Qed.

Lemma lng2_qpow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b) == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction a as [| a IH].
  - cbn [Nat.add q_pow]. ring.
  - cbn [Nat.add q_pow]. rewrite IH. ring.
Qed.

Lemma lng2_qpow_Znat : forall (c n : nat),
  q_pow ((Z.of_nat c # 1)%Q) n == ((Z.of_nat (c ^ n) # 1)%Q).
Proof.
  intros c n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH. apply w_Qmul_nat.
Qed.

Lemma lng2_budget_rhs_eq : forall (n m : nat), 2 * n <= m ->
  (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)
  == ((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n)).
Proof.
  intros n m Hm.
  pose proof (lng2_qpow_add (3 # 4)%Q (2 * n) (m - 2 * n)) as Hsplit.
  replace (2 * n + (m - 2 * n)) with m in Hsplit by lia.
  pose proof (lng2_qpow_add (3 # 4)%Q n n) as Hnn.
  replace (n + n) with (2 * n) in Hnn by lia.
  assert (Eb : ((64 # 3) * ((3 # 4) * (3 # 4)))%Q == (12 # 1)%Q) by reflexivity.
  transitivity ((q_pow (64 # 3)%Q n * (q_pow (3 # 4)%Q n * q_pow (3 # 4)%Q n))
                * q_pow (3 # 4)%Q (m - 2 * n))%Q.
  - rewrite Hsplit. rewrite Hnn. ring.
  - rewrite <- (lng2_qpow_Znat 12 n).
    transitivity (q_pow ((64 # 3) * ((3 # 4) * (3 # 4)))%Q n
                  * q_pow (3 # 4)%Q (m - 2 * n))%Q.
    + rewrite (w_qpow_mul_eq (64 # 3)%Q ((3 # 4) * (3 # 4))%Q n).
      rewrite <- (w_qpow_mul_eq (3 # 4)%Q (3 # 4)%Q n).
      reflexivity.
    + rewrite (lng_qpow_congr ((64 # 3) * ((3 # 4) * (3 # 4)))%Q (12 # 1)%Q n Eb).
      reflexivity.
Qed.

Theorem lng2_budget_compose : forall (n m : nat), 2 * n <= m ->
  QleT' ((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q)%Q)
        ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q).
Proof.
  intros n m Hm.
  assert (Hwpos : QleT' 0%Q (q_pow (3 # 4)%Q (m - 2 * n))).
  { apply Qle_to_QleT'. apply lnt2_pow_nonneg.
    unfold Qle. cbn [Qnum Qden]. lia. }
  eapply qleT'_trans.
  - apply qleT'_mult_compat_l.
    + exact Hwpos.
    + apply w_QleT'_nat. apply lng2_An_le_12pow.
  - apply w_qeq_leT'.
    symmetry.
    transitivity ((Z.of_nat (12 ^ n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q.
    + apply (lng2_budget_rhs_eq n m Hm).
    + apply Qmult_comm.
Defined.

(* ============================================================ *)
(* Section I: the theta^n terminal assembly (this piece's own faces).  *)
(* ============================================================ *)

(** nat-to-Q nonnegativity bridge: QleT' 0 (k#1). *)
Lemma lnt4_Znat_nonneg : forall k : nat, QleT' 0 ((Z.of_nat k # 1)%Q).
Proof.
  intro k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Defined.

Lemma lnt4_pow2_nonneg : forall k : nat, QleT' 0 (q_pow (2 # 1)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply Qlt_le_weak. apply lnt_pow2_pos.
Defined.

Lemma lnt4_pow64_nonneg : forall k : nat, QleT' 0 (q_pow (64 # 3)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply lnt2_pow_nonneg.
  unfold Qle. cbn [Qnum Qden]. lia.
Defined.

Lemma lnt4_pow128_nonneg : forall k : nat, QleT' 0 (q_pow (128 # 3)%Q k).
Proof.
  intro k. apply Qle_to_QleT'. apply lnt2_pow_nonneg.
  unfold Qle. cbn [Qnum Qden]. lia.
Defined.

Lemma lnt4_pow2_SS : forall n : nat,
  q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
  == ((4 # 1)%Q * q_pow (2 # 1)%Q n)%Q.
Proof.
  intro n. replace (Datatypes.S (Datatypes.S n)) with (2 + n) by lia.
  rewrite w_qpow_add. cbn [q_pow]. ring.
Qed.

Lemma lnt4_fold_24 : forall (n : nat) (c : Q),
  (q_pow (2 # 1)%Q n * (c * q_pow (12 # 1)%Q n))%Q == (c * q_pow (24 # 1)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (q_pow (2 # 1)%Q n * q_pow (12 # 1)%Q n))%Q).
  - ring.
  - rewrite <- (w_qpow_mul_eq (2 # 1)%Q (12 # 1)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (12 # 1)%Q) (24 # 1)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

Lemma lnt4_fold_128 : forall (n : nat) (c : Q),
  (q_pow (2 # 1)%Q n * (c * q_pow (64 # 3)%Q n))%Q == (c * q_pow (128 # 3)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (q_pow (2 # 1)%Q n * q_pow (64 # 3)%Q n))%Q).
  - ring.
  - rewrite <- (w_qpow_mul_eq (2 # 1)%Q (64 # 3)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (64 # 3)%Q) (128 # 3)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

Lemma lnt4_fold_128r : forall (n : nat) (c r : Q),
  (q_pow (2 # 1)%Q n * (c * (q_pow (64 # 3)%Q n * r)))%Q
  == (c * (q_pow (128 # 3)%Q n * r))%Q.
Proof.
  intros n c r.
  transitivity ((c * ((q_pow (2 # 1)%Q n * q_pow (64 # 3)%Q n) * r))%Q).
  - ring.
  - rewrite <- (w_qpow_mul_eq (2 # 1)%Q (64 # 3)%Q n).
    rewrite (lng_qpow_congr ((2 # 1)%Q * (64 # 3)%Q) (128 # 3)%Q n).
    + reflexivity.
    + reflexivity.
Qed.

Lemma lnt4_qpow2_Z : forall n : nat,
  q_pow (2 # 1)%Q n == ((Z.of_nat (2 ^ n) # 1)%Q).
Proof. exact lnt_qpow_Zofnat. Qed.

Lemma lnt4_qpow24_Z : forall n : nat,
  q_pow (24 # 1)%Q n == ((Z.of_nat (24 ^ n) # 1)%Q).
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    change (24 # 1)%Q with ((Z.of_nat 24 # 1)%Q). apply w_Qmul_nat.
Qed.

Lemma lnt4_24fold_eq : forall (n : nat) (c : Q),
  (c * (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q
  == (c * q_pow (24 # 1)%Q n)%Q.
Proof.
  intros n c.
  transitivity ((c * (((Z.of_nat (2 ^ n) # 1)%Q) *
                        ((Z.of_nat (12 ^ n) # 1)%Q)))%Q).
  - rewrite (lnt4_qpow2_Z n). reflexivity.
  - transitivity ((c * ((Z.of_nat (2 ^ n * 12 ^ n) # 1)%Q))%Q).
    + rewrite (w_Qmul_nat (2 ^ n) (12 ^ n)). reflexivity.
    + assert (HE : 2 ^ n * 12 ^ n = 24 ^ n)
        by (symmetry; change (24 ^ n) with ((2 * 12) ^ n); apply lng2_pow_mul_l).
      rewrite HE. rewrite <- (lnt4_qpow24_Z n). reflexivity.
Qed.

Lemma lnt4_qpow_scale : forall (a b : Q) (k n : nat),
  q_pow (a * q_pow b k)%Q n == (q_pow a n * q_pow b (k * n))%Q.
Proof.
  intros a b k n. induction n as [| n IH].
  - cbn [q_pow]. rewrite Nat.mul_0_r. cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite Nat.mul_succ_r, w_qpow_add. rewrite IH. ring.
Qed.

Lemma lnt4_pow_le_self : forall (x : Q) (k : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x (Datatypes.S k)) x.
Proof.
  intros x k H0 H1.
  assert (Hpk : Qle (q_pow x k) 1%Q).
  { pose proof (lnt2_pow_mono k x (1 # 1)%Q (QleT'_to_Qle _ _ H0)
                  (QleT'_to_Qle _ _ H1)) as Hp.
    rewrite w_qpow_one in Hp. exact Hp. }
  apply (lnt_leT'_eq_l ((x * q_pow x k)%Q) (q_pow x (Datatypes.S k)) x).
  - apply Qeq_sym. apply w_qpow_succ.
  - apply (lnt_leT'_eq_r ((x * q_pow x k)%Q) ((x * 1)%Q) x).
    + ring.
    + apply (qleT'_mult_compat_l (q_pow x k) 1%Q x H0).
      apply Qle_to_QleT'. exact Hpk.
Defined.

Lemma lnt4_gap_lhs_eq : forall (n m : nat),
  ((Z.of_nat (lng2_An n) # 1)%Q *
     (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
        q_pow (3 # 4)%Q (m - 2 * n)))%Q
  == ((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q) *
        q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q.
Proof. intros n m. ring. Qed.

(** Layer 1 main piece: 2n <= m entails
    A_n * 2^(n+2) * rho^(m-2n) <= 4 * (128/3)^n * rho^m. *)
Theorem lnt4_An_gap_compose : forall (n m : nat), 2 * n <= m ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
               q_pow (3 # 4)%Q (m - 2 * n)))%Q)
        (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q).
Proof.
  intros n m Hm.
  pose proof (lng2_budget_compose n m Hm) as Hbc.
  pose proof (lnt4_pow2_nonneg (Datatypes.S (Datatypes.S n))) as H2p.
  assert (Hsc : QleT' (((q_pow (3 # 4)%Q (m - 2 * n) *
                          (Z.of_nat (lng2_An n) # 1)%Q))%Q
                         * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q
                      (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m))%Q
                         * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q).
  { apply (qleT'_mult_compat_r
             (q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)%Q
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))) H2p Hbc). }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                q_pow (3 # 4)%Q (m - 2 * n)))%Q)
          (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
             q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
          (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)).
  - apply (lnt_leT'_eq_l
             (((q_pow (3 # 4)%Q (m - 2 * n) * (Z.of_nat (lng2_An n) # 1)%Q) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (m - 2 * n)))%Q)
             (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)).
    + apply (Qeq_sym _ _ (lnt4_gap_lhs_eq n m)).
    + exact Hsc.
  - apply (lnt_leT'_eq_r
             (((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m) *
                q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
             ((q_pow (2 # 1)%Q n *
                ((4 # 1)%Q * (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q m)))%Q)
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)).
    + rewrite (lnt4_fold_128r n (4 # 1)%Q (q_pow (3 # 4)%Q m)). reflexivity.
    + apply w_qeq_leT'. rewrite (lnt4_pow2_SS n). ring.
Defined.

(** DH theta budget consumption: 4^n*(7/40)^n = (7/10)^n <= (4/5)^n. *)
Theorem lnt4_theta_budget_consume : forall n : nat,
  QleT' (q_pow (7 # 10)%Q n) (q_pow (4 # 5)%Q n).
Proof.
  intro n.
  pose proof (lnt2_theta_budget n) as Htb.
  assert (Heq : q_pow (7 # 10)%Q n
                == (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q).
  { rewrite <- (w_qpow_mul_eq (4 # 1)%Q (7 # 40)%Q n).
    apply (lng_qpow_congr (7 # 10)%Q ((4 # 1)%Q * (7 # 40)%Q)%Q n).
    reflexivity. }
  apply (lnt_leT'_eq_l
           ((q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q)
           (q_pow (7 # 10)%Q n) (q_pow (4 # 5)%Q n)).
  - exact (Qeq_sym _ _ Heq).
  - exact Htb.
Defined.

(** Strict theta budget: 1 <= n entails (4/5)^n < 1. *)
Theorem lnt4_theta_budget_lt : forall n : nat, 1 <= n -> QltT (q_pow (4 # 5)%Q n) 1%Q.
Proof.
  intros n Hn. destruct n as [| k].
  - exfalso. lia.
  - eapply qleT'_ltT_ltT.
    + apply (lnt4_pow_le_self _ k); vm_compute; reflexivity.
    + vm_compute. reflexivity.
Defined.

Lemma lnt4_anchor_C18_0 : QleT' 0 ((128 # 3)%Q * q_pow (3 # 4)%Q 18)%Q.
Proof. vm_compute. reflexivity. Defined.

Lemma lnt4_anchor_C18_le1 : QleT' ((128 # 3)%Q * q_pow (3 # 4)%Q 18) 1%Q.
Proof. vm_compute. reflexivity. Defined.

Lemma lnt4_anchor_B18_lt1 :
  QltT (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q) 1%Q.
Proof. vm_compute. reflexivity. Defined.

Lemma lnt4_anchor_C11_0 : QleT' 0 ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q.
Proof. vm_compute. reflexivity. Defined.

Lemma lnt4_anchor_C11_le1 : QleT' ((64 # 3)%Q * q_pow (3 # 4)%Q 11) 1%Q.
Proof. vm_compute. reflexivity. Defined.

Lemma lnt4_anchor_C11_lt1 : QltT ((64 # 3)%Q * q_pow (3 # 4)%Q 11) 1%Q.
Proof. vm_compute. reflexivity. Defined.

(** Layer 1 slope race: 18n <= m entails
    A_n * 2^(n+2) * rho^(m-2n) <= 4 * C18^n with C18 := (128/3)*(3/4)^18. *)
Theorem lnt4_compete_exp : forall (n m : nat), 18 * n <= m ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
               q_pow (3 # 4)%Q (m - 2 * n)))%Q)
        (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q).
Proof.
  intros n m Hm.
  assert (Hm2 : 2 * n <= m) by lia.
  pose proof (lnt4_An_gap_compose n m Hm2) as Hg.
  pose proof (lnt3_rho_pow_anti (18 * n) m Hm) as Hra.
  pose proof (qleT'_mult_compat_l (q_pow (3 # 4)%Q m) (q_pow (3 # 4)%Q (18 * n))
                (q_pow (128 # 3)%Q n) (lnt4_pow128_nonneg n) Hra) as Hs.
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                q_pow (3 # 4)%Q (m - 2 * n)))%Q)
          (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)
          (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
  - exact Hg.
  - apply (lnt_leT'_eq_r
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m))%Q)
             (((4 # 1)%Q * (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n)))%Q)
             (((4 # 1)%Q * q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
    + rewrite <- (lnt4_qpow_scale (128 # 3)%Q (3 # 4)%Q 18 n). reflexivity.
    + apply (qleT'_mult_compat_l
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q m)%Q
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n))%Q
                (4 # 1)%Q lnt_q4_le0 Hs).
Defined.

(** Layer 1 strict terminal bound: 1 <= n, 18n <= m entails
    A_n * 2^(n+2) * rho^(m-2n) < 1. *)
Theorem lnt4_theta_lt : forall (n m : nat), 1 <= n -> 18 * n <= m ->
  QltT (((Z.of_nat (lng2_An n) # 1)%Q *
           (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
              q_pow (3 # 4)%Q (m - 2 * n)))%Q) 1%Q.
Proof.
  intros n m Hn Hm. destruct n as [| k].
  - exfalso. lia.
  - apply (qleT'_ltT_ltT
              (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                  (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                     q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
              (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q) 1%Q).
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                   (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                      q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
                (((4 # 1)%Q *
                    q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))%Q)
                (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q)).
      * apply (lnt4_compete_exp (Datatypes.S k) m Hm).
      * apply (qleT'_mult_compat_l
                  (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))
                  ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (4 # 1)%Q lnt_q4_le0).
        apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C18_0.
        -- exact lnt4_anchor_C18_le1.
    + exact lnt4_anchor_B18_lt1.
Defined.

(** Layer 1 pure-budget strict bound: 1 <= n, 11n <= m entails
    A_n * rho^(m-2n) < 1 with C11 := (64/3)*(3/4)^11. *)
Theorem lnt4_budget_lt : forall (n m : nat), 1 <= n -> 11 * n <= m ->
  QltT (((Z.of_nat (lng2_An n) # 1)%Q * q_pow (3 # 4)%Q (m - 2 * n))%Q) 1%Q.
Proof.
  intros n m Hn Hm. destruct n as [| k].
  - exfalso. lia.
  - assert (Hm2 : 2 * Datatypes.S k <= m) by lia.
    pose proof (lng2_budget_compose (Datatypes.S k) m Hm2) as Hbc.
    assert (Hm11 : 11 * Datatypes.S k <= m) by exact Hm.
    pose proof (lnt3_rho_pow_anti (11 * Datatypes.S k) m Hm11) as Hra.
    pose proof (qleT'_mult_compat_l (q_pow (3 # 4)%Q m)
                  (q_pow (3 # 4)%Q (11 * Datatypes.S k)) (q_pow (64 # 3)%Q (Datatypes.S k))
                  (lnt4_pow64_nonneg (Datatypes.S k)) Hra) as Hs.
    apply (qleT'_ltT_ltT
              (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                  q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
              ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q 1%Q).
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                    q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                (q_pow ((64 # 3)%Q * q_pow (3 # 4)%Q 11) (Datatypes.S k))
                ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q).
      * apply (lnt_leT'_eq_r
                  (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                      q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                  ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q (11 * Datatypes.S k))%Q)
                  (q_pow ((64 # 3)%Q * q_pow (3 # 4)%Q 11) (Datatypes.S k))).
        -- rewrite <- (lnt4_qpow_scale (64 # 3)%Q (3 # 4)%Q 11 (Datatypes.S k)).
           reflexivity.
        -- apply (qleT'_trans
                     (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                        q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                     ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q m)%Q)
                     ((q_pow (64 # 3)%Q (Datatypes.S k) * q_pow (3 # 4)%Q (11 * Datatypes.S k))%Q)).
           ++ apply (lnt_leT'_eq_l
                       ((q_pow (3 # 4)%Q (m - 2 * Datatypes.S k) *
                          (Z.of_nat (lng2_An (Datatypes.S k)) # 1))%Q)
                       (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                          q_pow (3 # 4)%Q (m - 2 * Datatypes.S k))%Q)
                       ((q_pow (64 # 3)%Q (Datatypes.S k) *
                           q_pow (3 # 4)%Q m)%Q)).
              ** ring.
              ** exact Hbc.
           ++ exact Hs.
      * apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C11_0.
        -- exact lnt4_anchor_C11_le1.
    + exact lnt4_anchor_C11_lt1.
Defined.

(** Layer 2 full-container RHS transport: 1 <= n, 2n <= M+1 entails
    A_n * S_{M+d} <= SM * 24^n + d * (128/3)^n * rho^SM. *)
Theorem lnt4_total_budget : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
          + (Z.of_nat d # 1) *
              (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
Proof.
  intros n M d Hn HM.
  pose proof (lnt3_wsum_band_total n M d Hn HM) as Hwt.
  assert (HAn : QleT' ((Z.of_nat (lng2_An n) # 1)%Q) ((Z.of_nat (12 ^ n) # 1)%Q)).
  { apply (w_QleT'_nat _ _ (lng2_An_le_12pow n)). }
  assert (Hscale : QleT' ((q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q)%Q)
                         ((q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q))%Q)).
  { apply (qleT'_mult_compat_l (Z.of_nat (lng2_An n) # 1) (Z.of_nat (12 ^ n) # 1)
             (q_pow (2 # 1)%Q n) (lnt4_pow2_nonneg n) HAn). }
  assert (Hsm2 : QleT' (((Z.of_nat (Datatypes.S M) # 1) *
                           (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                       (((Z.of_nat (Datatypes.S M) # 1) *
                           (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q)).
  { apply (qleT'_mult_compat_l
             (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q))%Q
             (Z.of_nat (Datatypes.S M) # 1)
             (lnt4_Znat_nonneg (Datatypes.S M)) Hscale). }
  assert (Hp1 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          ((Z.of_nat (Datatypes.S M) # 1) *
                             q_pow (2 # 1)%Q n))%Q)
                      (((Z.of_nat (Datatypes.S M) # 1) *
                          q_pow (24 # 1)%Q n))%Q).
  { apply (lnt_leT'_eq_l
             (((Z.of_nat (Datatypes.S M) # 1) *
                (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n))%Q)
             (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n))%Q).
    - ring.
    - apply (lnt_leT'_eq_r
                (((Z.of_nat (Datatypes.S M) # 1) *
                   (q_pow (2 # 1)%Q n * (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                (((Z.of_nat (Datatypes.S M) # 1) *
                   (q_pow (2 # 1)%Q n * ((Z.of_nat (12 ^ n) # 1)%Q)))%Q)
                (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n))%Q).
      + exact (lnt4_24fold_eq n (Z.of_nat (Datatypes.S M) # 1)).
      + exact Hsm2.
  }
  assert (Hbc : QleT' ((q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                          (Z.of_nat (lng2_An n) # 1)%Q)%Q)
                      ((q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
  { apply (lng2_budget_compose n (Datatypes.S M)). lia. }
  assert (Hs1 : QleT' (((Z.of_nat d # 1) *
                          (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                             (Z.of_nat (lng2_An n) # 1)%Q))%Q)
                      (((Z.of_nat d # 1) *
                          (q_pow (64 # 3)%Q n *
                             q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  { apply (qleT'_mult_compat_l
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                (Z.of_nat (lng2_An n) # 1)%Q)%Q
             (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q
             (Z.of_nat d # 1) (lnt4_Znat_nonneg d) Hbc). }
  assert (Hs2 : QleT' ((q_pow (2 # 1)%Q n *
                          ((Z.of_nat d # 1) *
                             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                                (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
                      ((q_pow (2 # 1)%Q n *
                          ((Z.of_nat d # 1) *
                             (q_pow (64 # 3)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M))))%Q)).
  { apply (qleT'_mult_compat_l
             ((Z.of_nat d # 1) *
                (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                   (Z.of_nat (lng2_An n) # 1)%Q))%Q
             ((Z.of_nat d # 1) *
                (q_pow (64 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M)))%Q
             (q_pow (2 # 1)%Q n) (lnt4_pow2_nonneg n) Hs1). }
  assert (Hp2 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          ((Z.of_nat d # 1) *
                             (q_pow (2 # 1)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
                      (((Z.of_nat d # 1) *
                          (q_pow (128 # 3)%Q n *
                             q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  { apply (lnt_leT'_eq_l
             ((q_pow (2 # 1)%Q n *
                ((Z.of_nat d # 1) *
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                      (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
             (((Z.of_nat (lng2_An n) # 1)%Q *
                ((Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
             (((Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
    - ring.
    - apply (lnt_leT'_eq_r
                ((q_pow (2 # 1)%Q n *
                   ((Z.of_nat d # 1) *
                      (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                         (Z.of_nat (lng2_An n) # 1)%Q)))%Q)
                ((q_pow (2 # 1)%Q n *
                   ((Z.of_nat d # 1) *
                      (q_pow (64 # 3)%Q n *
                         q_pow (3 # 4)%Q (Datatypes.S M))))%Q)
                (((Z.of_nat d # 1) *
                    (q_pow (128 # 3)%Q n *
                       q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
      + rewrite (lnt4_fold_128r n (Z.of_nat d # 1)
                   (q_pow (3 # 4)%Q (Datatypes.S M))). reflexivity.
      + exact Hs2.
  }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q *
              ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
               + (Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
  - apply (qleT'_mult_compat_l
              (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
              ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
               + (Z.of_nat d # 1) *
                   (q_pow (2 # 1)%Q n *
                      q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
              (Z.of_nat (lng2_An n) # 1)
              (lnt4_Znat_nonneg (lng2_An n)) Hwt).
  - apply (lnt_leT'_eq_l
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    ((Z.of_nat d # 1) *
                       (q_pow (2 # 1)%Q n *
                          q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
                   + (Z.of_nat d # 1) *
                       (q_pow (2 # 1)%Q n *
                          q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))))%Q)
              (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
                + (Z.of_nat d # 1) *
                    (q_pow (128 # 3)%Q n *
                       q_pow (3 # 4)%Q (Datatypes.S M)))%Q)).
    + ring.
    + apply (qleT'_plus_compat _ _ _ _ Hp1 Hp2).
Defined.

(** Layer 2 DH additive-gap twin: 1 <= n, 2n <= M+1 entails
    A_n * S_{M+d} <= A_n * S_M + 4 * (128/3)^n * rho^SM. *)
Theorem lnt4_total_gap_budget : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S M) (lnw_wterm n)
          + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                              q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q).
Proof.
  intros n M d Hn HM.
  assert (Hm2 : 2 * n <= Datatypes.S M) by lia.
  pose proof (lnt2_wgap_geo_quarter n M d Hn HM) as Hgap.
  pose proof (lnt4_An_gap_compose n (Datatypes.S M) Hm2) as Hbc.
  pose proof (lnt4_Znat_nonneg (lng2_An n)) as HAn0.
  assert (H1 : QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                          sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
                     (((Z.of_nat (lng2_An n) # 1)%Q *
                         (sum_upto (Datatypes.S M) (lnw_wterm n)
                            + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                                 q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)%Q)).
  { apply (qleT'_mult_compat_l _ _ _ HAn0 Hgap). }
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
            + (Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
          (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
            + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q)).
  - apply (lnt_leT'_eq_r
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q *
                  (sum_upto (Datatypes.S M) (lnw_wterm n)
                 + q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                     q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                       q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)).
    + ring.
    + exact H1.
  - apply (lnt_leT'_eq_l
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                     (Z.of_nat (lng2_An n) # 1)%Q) *
                     q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + (Z.of_nat (lng2_An n) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                       q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q)
              (((Z.of_nat (lng2_An n) # 1)%Q * sum_upto (Datatypes.S M) (lnw_wterm n)
                + ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                    q_pow (3 # 4)%Q (Datatypes.S M)))%Q)%Q)).
    + rewrite (lnt4_gap_lhs_eq n (Datatypes.S M)). ring.
    + apply (qleT'_plus_compat).
      * apply qleT'_refl.
      * apply (lnt_leT'_eq_l
                  ((Z.of_nat (lng2_An n) # 1)%Q *
                     (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                        q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
                  (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n) *
                     (Z.of_nat (lng2_An n) # 1)%Q *
                     q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q
                  ((4 # 1)%Q * (q_pow (128 # 3)%Q n *
                                  q_pow (3 # 4)%Q (Datatypes.S M)))%Q).
        -- ring.
        -- exact Hbc.
Defined.

(** Layer 2 slope form: 1 <= n, 18n <= SM entails
    A_n * S_{M+d} <= SM * 24^n + d * C18^n. *)
Theorem lnt4_total_slope : forall (n M d : nat), 1 <= n -> 18 * n <= Datatypes.S M ->
  QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
            sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
        (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
          + (Z.of_nat d # 1) *
              q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q).
Proof.
  intros n M d Hn Hm.
  assert (Hm2 : 2 * n <= M + 1) by lia.
  pose proof (lnt4_total_budget n M d Hn Hm2) as Htb.
  pose proof (lnt3_rho_pow_anti (18 * n) (Datatypes.S M) Hm) as Hra.
  apply (qleT'_trans
          (((Z.of_nat (lng2_An n) # 1)%Q *
              sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                (q_pow (128 # 3)%Q n *
                   q_pow (3 # 4)%Q (Datatypes.S M)))%Q)
          (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
            + (Z.of_nat d # 1) *
                q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
  - exact Htb.
  - apply (qleT'_plus_compat).
    + apply qleT'_refl.
    + apply (qleT'_mult_compat_l
                (q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q
                (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)
                (Z.of_nat d # 1) (lnt4_Znat_nonneg d)).
      apply (lnt_leT'_eq_r
                ((q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (Datatypes.S M))%Q)
                ((q_pow (128 # 3)%Q n * q_pow (3 # 4)%Q (18 * n))%Q)
                (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)).
      * rewrite <- (lnt4_qpow_scale (128 # 3)%Q (3 # 4)%Q 18 n). reflexivity.
      * apply (qleT'_mult_compat_l (q_pow (3 # 4)%Q (Datatypes.S M))
                  (q_pow (3 # 4)%Q (18 * n)) (q_pow (128 # 3)%Q n)
                  (lnt4_pow128_nonneg n) Hra).
Defined.

(** Layer 3 sigT witness face: 1 <= n, 18n <= m entails there is a closed
    rational witness B := 4*C18 = 3^17/2^27 < 1 with A_n*tail <= B. *)
Theorem lnt4_remainder_sig : forall (n m : nat), 1 <= n -> 18 * n <= m ->
  sigT (fun B : Q => And (QltT B 1%Q)
            (QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                       (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                          q_pow (3 # 4)%Q (m - 2 * n)))%Q) B)).
Proof.
  intros n m Hn Hm.
  exists (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q).
  split.
  - exact lnt4_anchor_B18_lt1.
  - destruct n as [| k].
    + exfalso. lia.
    + apply (qleT'_trans
                (((Z.of_nat (lng2_An (Datatypes.S k)) # 1)%Q *
                    (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S k))) *
                       q_pow (3 # 4)%Q (m - 2 * Datatypes.S k)))%Q)
                (((4 # 1)%Q *
                    q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))%Q)
                (((4 # 1)%Q * ((128 # 3)%Q * q_pow (3 # 4)%Q 18))%Q)).
      * apply (lnt4_compete_exp (Datatypes.S k) m Hm).
      * apply (qleT'_mult_compat_l
                  (q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (Datatypes.S k))
                  ((128 # 3)%Q * q_pow (3 # 4)%Q 18) (4 # 1)%Q lnt_q4_le0).
        apply (lnt4_pow_le_self _ k).
        -- exact lnt4_anchor_C18_0.
        -- exact lnt4_anchor_C18_le1.
Defined.

(** Layer 3 final And face: 1 <= n, 18n <= SM entails
    (strict remainder < 1) x (A_n*S_{M+d} <= SM*24^n + d*C18^n). *)
Theorem lnt4_theta_final : forall (n M d : nat), 1 <= n -> 18 * n <= Datatypes.S M ->
  And (QltT (((Z.of_nat (lng2_An n) # 1)%Q *
                (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)) *
                   q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q) 1%Q)
      (QleT' (((Z.of_nat (lng2_An n) # 1)%Q *
                  sum_upto (Datatypes.S (M + d)) (lnw_wterm n))%Q)
             (((Z.of_nat (Datatypes.S M) # 1) * q_pow (24 # 1)%Q n
               + (Z.of_nat d # 1) *
                   q_pow ((128 # 3)%Q * q_pow (3 # 4)%Q 18) n)%Q)).
Proof.
  intros n M d Hn Hm. split.
  - apply (lnt4_theta_lt n (Datatypes.S M) Hn Hm).
  - apply (lnt4_total_slope n M d Hn Hm).
Defined.

(* ============================================================ *)
(* Numeric pins (vm_compute on concrete values only).                 *)
(* ============================================================ *)

Theorem lnt4_anchor_C18_val :
  QeqT ((128 # 3)%Q * q_pow (3 # 4)%Q 18)%Q ((129140163 # 536870912)%Q).
Proof. vm_compute. reflexivity. Defined.

Theorem lnt4_anchor_C11_val :
  QeqT ((64 # 3)%Q * q_pow (3 # 4)%Q 11)%Q ((59049 # 65536)%Q).
Proof. vm_compute. reflexivity. Defined.

Theorem lnt4_anchor_budget :
  QltT (((Z.of_nat (lng2_An 2) # 1)%Q * q_pow (3 # 4)%Q 20)%Q) 1%Q.
Proof. vm_compute. reflexivity. Defined.

Theorem lnt4_anchor_gap18 :
  QltT (((Z.of_nat (lng2_An 2) # 1)%Q *
           (q_pow (2 # 1)%Q 4 * q_pow (3 # 4)%Q 32))%Q) 1%Q.
Proof. vm_compute. reflexivity. Defined.

Theorem lnt4_anchor_total :
  QleT' (((Z.of_nat (lng2_An 2) # 1)%Q * sum_upto 9 (lnw_wterm 2))%Q)
        ((4428 # 1)%Q).
Proof. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per named statement.        *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction lnt4_An_gap_compose lnt4_compete_exp lnt4_budget_lt
  lnt4_theta_lt lnt4_total_budget lnt4_total_gap_budget lnt4_total_slope
  lnt4_remainder_sig lnt4_theta_final lnt4_theta_budget_consume
  lnt4_theta_budget_lt.

Print Assumptions qeqQ_le.
Print Assumptions w_qeq_leT'.
Print Assumptions w_qpow_succ.
Print Assumptions w_qpow_add.
Print Assumptions w_qpow_one.
Print Assumptions w_qpow_mul_eq.
Print Assumptions w_Qmul_nat.
Print Assumptions w_Qle_nat.
Print Assumptions w_QleT'_nat.
Print Assumptions w_Qlt_Z1.
Print Assumptions w_bkC_pos.
Print Assumptions w_pow2_ge1.
Print Assumptions lng_qpow_congr.
Print Assumptions lnt_bkC_step.
Print Assumptions lnt_leT'_eq_l.
Print Assumptions lnt_leT'_eq_r.
Print Assumptions lnt_qneq_of_eq0.
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
Print Assumptions lng2_bkC_le_pow2.
Print Assumptions lnt_sum_le.
Print Assumptions lnt_sum_scale.
Print Assumptions lnt_sum_range.
Print Assumptions lnt_geo_partial.
Print Assumptions lnt_pterm_pos.
Print Assumptions lnt_pterm_ratio.
Print Assumptions lnt_pterm_pow.
Print Assumptions lnt_pterm_peak.
Print Assumptions lnw_zpos_of_bkC.
Print Assumptions lnw_uterm_pos.
Print Assumptions lnw_qZ_le0.
Print Assumptions lnw_q2_le0.
Print Assumptions lnw_qinv_den_le.
Print Assumptions lnw_uterm_le.
Print Assumptions lnw_wterm_pos.
Print Assumptions lnw_wterm_ge.
Print Assumptions lnw_wterm_le2.
Print Assumptions lnw_wterm_peak.
Print Assumptions lnt2_sq_nonneg.
Print Assumptions lnt2_nat_cancel_r.
Print Assumptions lnt2_key_of_ge.
Print Assumptions lnt2_key_lin.
Print Assumptions lnt2_key_mono.
Print Assumptions lnt2_key_shift.
Print Assumptions lnt2_key_at.
Print Assumptions lnt2_pow_nonneg.
Print Assumptions lnt2_pow_mono.
Print Assumptions lnt2_pow_mul.
Print Assumptions lnt2_hquad.
Print Assumptions lnt2_hquad_pow.
Print Assumptions lnt2_theta_budget.
Print Assumptions lnt2_uterm_ratio34.
Print Assumptions lnt2_pterm_ratio34.
Print Assumptions lnt2_wterm_step.
Print Assumptions lnt2_wterm_pow_pure.
Print Assumptions lnt2_wterm_tail_pure.
Print Assumptions lnt2_wgap_pure.
Print Assumptions lnt2_wgap_geo_quarter.
Print Assumptions lnt3_nlt_drop.
Print Assumptions lnt3_nlt_lift.
Print Assumptions lnt3_qscale_succ.
Print Assumptions lnt3_rho_pow_anti.
Print Assumptions lnt3_sum_bmax.
Print Assumptions lnt3_wsum_peak.
Print Assumptions lnt3_wpt_band.
Print Assumptions lnt3_wtail_window.
Print Assumptions lnt3_wsum_band_total.
Print Assumptions lng2_bkC_le_pow2.
Print Assumptions lng2_psd_scale.
Print Assumptions lng2_pow_mul_l.
Print Assumptions lng2_qtilde_le_6pow.
Print Assumptions lng2_An_le_12pow.
Print Assumptions lng2_qpow_add.
Print Assumptions lng2_qpow_Znat.
Print Assumptions lng2_budget_rhs_eq.
Print Assumptions lng2_budget_compose.
Print Assumptions lnt4_Znat_nonneg.
Print Assumptions lnt4_pow2_nonneg.
Print Assumptions lnt4_pow64_nonneg.
Print Assumptions lnt4_pow128_nonneg.
Print Assumptions lnt4_pow2_SS.
Print Assumptions lnt4_fold_24.
Print Assumptions lnt4_fold_128.
Print Assumptions lnt4_fold_128r.
Print Assumptions lnt4_qpow2_Z.
Print Assumptions lnt4_qpow24_Z.
Print Assumptions lnt4_24fold_eq.
Print Assumptions lnt4_qpow_scale.
Print Assumptions lnt4_pow_le_self.
Print Assumptions lnt4_gap_lhs_eq.
Print Assumptions lnt4_An_gap_compose.
Print Assumptions lnt4_theta_budget_consume.
Print Assumptions lnt4_theta_budget_lt.
Print Assumptions lnt4_anchor_C18_0.
Print Assumptions lnt4_anchor_C18_le1.
Print Assumptions lnt4_anchor_B18_lt1.
Print Assumptions lnt4_anchor_C11_0.
Print Assumptions lnt4_anchor_C11_le1.
Print Assumptions lnt4_anchor_C11_lt1.
Print Assumptions lnt4_compete_exp.
Print Assumptions lnt4_theta_lt.
Print Assumptions lnt4_budget_lt.
Print Assumptions lnt4_total_budget.
Print Assumptions lnt4_total_gap_budget.
Print Assumptions lnt4_total_slope.
Print Assumptions lnt4_remainder_sig.
Print Assumptions lnt4_theta_final.
Print Assumptions lnt4_anchor_C18_val.
Print Assumptions lnt4_anchor_C11_val.
Print Assumptions lnt4_anchor_budget.
Print Assumptions lnt4_anchor_gap18.
Print Assumptions lnt4_anchor_total.
