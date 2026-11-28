(* ===================================================================== *)
(* Module   : abl_ln2_numer_int                                          *)
(* Mission.  Integral supply core for the ln 2 numerator family: with    *)
(*   p_n the signed Laurent numerator closed form (bv_p) and             *)
(*   L_n := lcm(1..n), the modified numerator L_n * p_n is integral,     *)
(*   with an explicit integer witness built term by term over the        *)
(*   finite rational sum.  Low segment (j < n): 2^(n-j) cancels against  *)
(*   (2^d - 1) with d = n - j; high segment (n < j <= 2n): coefficients  *)
(*   integral directly; every denominator d <= n divides L_n.  Also      *)
(*   delivered: the plain limb L_n * q~_n (q~_n := bk_Qn_qtilde) and the *)
(*   integer pair (L_n * q~_n, L_n * p_n) for the remodeled supply       *)
(*   interface; anchors L_k * p_k = 0, 2, 18, 262, 2670, 69994 (k <= 5). *)
(* Dependencies. Stdlib QArith/ZArith/Arith/List/Lia; landed modules     *)
(*   S01_BaseRing, S02_CauchyComplete (QeqT, qeq_imp_qeqT, qeqT_imp_qeq),*)
(*   S03_QExp (q_pow), BeukersLists (bk_psQ, bk_Qn_qtilde, bk_Qmul_nat), *)
(*   HansonLcm (hl_lcm_upto, hl_lcm_divide_all, hl_pow2_ge1, hl_le_t),   *)
(*   BeukersVariant (bv_p, bv_c, bv_q2, bv_negpow), Ln2Integrality (pi_).*)
(* Constructivity. Statement faces are Set-carried: witnesses as sigT    *)
(*   over Z, equalities as QeqT, nat order premises as the decidable     *)
(*   face hl_le_t; no Prop statement and no sigT embedding of a Prop     *)
(*   component.  Proof bodies use constructive Prop reasoning (ring,     *)
(*   lia, stdlib Q lemmas).  Every lemma closes with Defined for         *)
(*   extraction transparency; no opaque closer is used, since no         *)
(*   pure-Prop bridge lemma stands alone.  vm_compute is confined to     *)
(*   concrete numeric pins (the six anchors and the zero branch of the   *)
(*   inverse-sign lemma).  Zero axioms, zero classical logic, no proof   *)
(*   abandonment.                                                        *)
(* Build. rocq c -native-compiler no -q -Q <world root> "" abl_ln2_numer_int.v *)
(*   (Rocq 9.3), single shot on the same-world dependency .vo chain.     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm BeukersVariant Ln2Integrality.

Open Scope nat_scope.

(* ============================================================ *)
(* Sec 0.  Q-layer micro bridges (QeqT face; Qopp transport by  *)
(* the numeric route).                                          *)
(* ============================================================ *)

(* QeqT transport under Qopp (Qeq itself is unfolded; the Z face is a ring identity). *)
Lemma lni_Qopp_cong : forall x y : Q, QeqT x y -> QeqT (Qopp x) (Qopp y).
Proof.
  intros x y H. apply qeq_imp_qeqT. apply qeqT_imp_qeq in H.
  unfold Qeq in *. cbn [Qopp Qnum Qden] in *.
  transitivity (Z.opp (Qnum x * Z.pos (Qden y))).
  - ring.
  - rewrite H. ring.
Defined.

(* Qopp on integer-valued Q in explicit form: Qopp (u#1) == (-u)#1. *)
Lemma lni_QoppZ : forall u : Z, QeqT (Qopp (u # 1)) ((Z.opp u) # 1)%Q.
Proof.
  intro u. apply qeq_imp_qeqT. unfold Qeq. cbn [Qopp Qnum Qden Pos.mul]. ring.
Defined.

Lemma lni_Qmul_cong_r : forall x y z : Q, QeqT x y -> QeqT (x * z) (y * z).
Proof.
  intros x y z H. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ H). reflexivity.
Defined.

Lemma lni_Qmul_cong_l : forall x y z : Q, QeqT x y -> QeqT (z * x) (z * y).
Proof.
  intros x y z H. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ H). reflexivity.
Defined.

Lemma lni_Qplus_cong_l : forall x y c : Q, QeqT x y -> QeqT (c + x) (c + y).
Proof.
  intros x y c H. apply qeq_imp_qeqT. rewrite (qeqT_imp_qeq _ _ H). reflexivity.
Defined.

Lemma lni_Qminus_cong_l : forall x y c : Q, QeqT x y -> QeqT (x - c) (y - c).
Proof.
  intros x y c H. apply qeq_imp_qeqT. unfold Qminus.
  rewrite (qeqT_imp_qeq _ _ H). reflexivity.
Defined.

Lemma lni_Qdiv_cong_l : forall x y z : Q, QeqT x y -> QeqT (x / z) (y / z).
Proof.
  intros x y z H. apply qeq_imp_qeqT. unfold Qdiv.
  rewrite (qeqT_imp_qeq _ _ H). reflexivity.
Defined.

(* Z-level numeric bridges for integer-valued Q. *)
Lemma lni_QmulZ : forall u v : Z, QeqT (((u # 1) * (v # 1))%Q) (((u * v) # 1)%Q).
Proof.
  intros u v. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Defined.

Lemma lni_QaddZ : forall u v : Z, QeqT (((u # 1) + (v # 1))%Q) (((u + v) # 1)%Q).
Proof.
  intros u v. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring.
Defined.

Lemma lni_QsubZ : forall u v : Z, QeqT (((u # 1) - (v # 1))%Q) (((u - v) # 1)%Q).
Proof.
  intros u v. apply qeq_imp_qeqT. unfold Qeq, Qminus.
  cbn [Qopp Qnum Qden Qplus Pos.mul]. ring.
Defined.

(* nat closed forms of q_pow at the two concrete bases. *)
Lemma lni_qpow1 : forall N : nat, QeqT (q_pow (1 # 1)%Q N) 1%Q.
Proof.
  intros N. apply qeq_imp_qeqT. induction N as [| N IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. ring.
Defined.

Lemma lni_qpow2_nat : forall k : nat, QeqT (q_pow (2 # 1)%Q k) ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  intros k. apply qeq_imp_qeqT. induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH.
    transitivity (((Z.of_nat 2) # 1) * ((Z.of_nat (2 ^ k)) # 1))%Q.
    { reflexivity. }
    pose proof (qeqT_imp_qeq _ _ (bk_Qmul_nat 2 (2 ^ k))) as Hbm.
    rewrite Hbm. cbn [Nat.pow]. reflexivity.
Defined.

(* Sign export for the reciprocal of a negative denominator: the zero
   branch is a concrete numeric pin, the nonzero branch cancels through
   the stdlib inverse supplied on both sides. *)
Lemma lni_qinv_opp : forall u : Z, QeqT ((/ (Qopp (u # 1)))%Q) ((Qopp (/ (u # 1)))%Q).
Proof.
  intro u. apply qeq_imp_qeqT.
  destruct (Z.eq_dec u 0) as [Hu0 | Hne].
  - subst u. vm_compute. reflexivity.
  - assert (Hu : ~ ((u # 1) == 0)%Q).
    { intro Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
      rewrite !Z.mul_1_r in Hc. lia. }
    assert (Hnz : ~ (Qopp (u # 1) == 0)%Q).
    { intro H0. unfold Qeq in H0. cbn [Qopp Qnum Qden] in H0.
      rewrite !Z.mul_1_r in H0.
      apply Hu. unfold Qeq. cbn [Qnum Qden]. rewrite !Z.mul_1_r. lia. }
    apply (pi_Qmul_cancel_r_to ((/ (Qopp (u # 1)))) ((Qopp (/ (u # 1))))
                               ((Qopp (u # 1)))).
    + exact Hnz.
    + transitivity (1%Q).
      * rewrite Qmult_comm. exact (Qmult_inv_r (Qopp (u # 1)) Hnz).
      * transitivity ((u # 1) * (/ (u # 1)))%Q.
        -- symmetry. exact (Qmult_inv_r (u # 1) Hu).
        -- ring.
Defined.

(* Core algebra leaf for the two-power cancellation: with 1 <= m,
   m * (1/m - 1) == 1 - m, stated at the m := 2^d use face with the
   decidable order premise. *)
Lemma lni_qmul_inv_sub : forall m : nat, hl_le_t 1 m ->
  QeqT (((Z.of_nat m # 1) * ((/ (Z.of_nat m # 1)) - 1%Q))%Q)
       ((1%Q - (Z.of_nat m # 1))%Q).
Proof.
  intros m Hm. apply qeq_imp_qeqT.
  assert (Hx : ~ ((Z.of_nat m # 1) == 0)%Q)
    by (apply (pi_Qneq0_nat m); apply hl_le_t_to_le; exact Hm).
  apply (proj1 (Qplus_inj_r ((Z.of_nat m # 1) * ((/ (Z.of_nat m # 1)) - 1%Q))
                            (1%Q - (Z.of_nat m # 1)) (Z.of_nat m # 1))).
  transitivity (1%Q).
  - transitivity ((Z.of_nat m # 1) * (/ (Z.of_nat m # 1)))%Q.
    + ring.
    + exact (Qmult_inv_r (Z.of_nat m # 1) Hx).
  - ring.
Defined.

(* The Q carrier of the sign factor times an integer stays integral,
   with the integer witness explicit. *)
Lemma lni_negpow_Zmul : forall (s : nat) (u : Z),
  sigT (fun u' : Z => QeqT ((bv_negpow s * (u # 1))%Q) ((u' # 1)%Q)).
Proof.
  induction s as [| s IH]; intro u.
  - exists u. apply qeq_imp_qeqT. cbn [bv_negpow]. ring.
  - destruct (IH u) as [u' Hu'].
    exists (Z.opp u'). apply qeq_imp_qeqT. cbn [bv_negpow].
    transitivity ((Qopp (bv_negpow s * (u # 1)))%Q).
    { ring. }
    transitivity ((Qopp ((u' # 1)%Q))).
    { apply (qeqT_imp_qeq _ _). apply lni_Qopp_cong. exact Hu'. }
    exact (qeqT_imp_qeq _ _ (lni_QoppZ u')).
Defined.

(* ============================================================ *)
(* Sec 1.  Finite-sum carrier: termwise integralization of      *)
(* bk_psQ (. , N, 1) lifts to the whole sum.                    *)
(* ============================================================ *)

Lemma lni_psQ_zsum_ex : forall (N : nat) (f : nat -> Q),
  (forall k : nat, hl_le_t (Datatypes.S k) N ->
     sigT (fun z : Z => QeqT (f k) ((z # 1)%Q))) ->
  sigT (fun z : Z => QeqT (bk_psQ f N 1%Q) ((z # 1)%Q)).
Proof.
  induction N as [| N IH]; intros f H.
  - exists 0%Z. apply qeq_imp_qeqT. cbn [bk_psQ]. ring.
  - assert (Hpre : forall k : nat, hl_le_t (Datatypes.S k) N ->
              sigT (fun z : Z => QeqT (f k) ((z # 1)%Q))).
    { intros k Hk. apply H. apply hl_le_to_le_t.
      apply hl_le_t_to_le in Hk. lia. }
    destruct (IH f Hpre) as [z0 Hz0].
    destruct (H N (hl_le_to_le_t (Datatypes.S N) (Datatypes.S N)
                                 (Nat.lt_succ_diag_r N))) as [z1 Hz1].
    exists (z0 + z1)%Z. apply qeq_imp_qeqT.
    pose proof (qeqT_imp_qeq _ _ (lni_qpow1 N)) as Hq1.
    pose proof (qeqT_imp_qeq _ _ Hz0) as Hz0'.
    pose proof (qeqT_imp_qeq _ _ Hz1) as Hz1'.
    cbn [bk_psQ]. rewrite Hq1. rewrite Hz0', Hz1'.
    transitivity (((z0 # 1)%Q + (z1 # 1)%Q)%Q).
    { ring. }
    exact (qeqT_imp_qeq _ _ (lni_QaddZ z0 z1)).
Defined.

(* ============================================================ *)
(* Sec 2.  Segment closed forms of the Laurent coefficients     *)
(* (both integrality faces of bv_c).                            *)
(* ============================================================ *)

(* Low segment (j < n): bv_c n j == sign * 2^(n-j) * T_j with T_j an
   explicit integer; the per-term two-power split uses Nat.pow_add_r. *)
Lemma lni_bvc_low : forall n j : nat, hl_le_t (Datatypes.S j) n ->
  sigT (fun t : Z =>
    QeqT (bv_c n j)
         ((bv_negpow (n + j) * ((Z.of_nat (2 ^ (n - j)) # 1) * (t # 1))%Q)%Q)).
Proof.
  intros n j Hj.
  assert (Hjn : Datatypes.S j <= n) by (apply hl_le_t_to_le; exact Hj).
  unfold bv_c.
  assert (Hpt : forall a : nat, hl_le_t (Datatypes.S a) (Datatypes.S j) ->
            sigT (fun z : Z => QeqT (((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
                                ((z # 1)%Q))).
  { intros a Ha. exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)).
    apply qeq_imp_qeqT. reflexivity. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q) Hpt)
    as [t Ht].
  pose proof (qeqT_imp_qeq _ _ Ht) as Ht'.
  exists t. apply qeq_imp_qeqT.
  transitivity (bv_negpow (n + j) *
    bk_psQ (fun a : nat => ((Z.of_nat (2 ^ (n - j)) # 1) *
              ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1))%Q)
            (Datatypes.S j) 1%Q)%Q.
  { assert (Hcm : forall a b c : Q, a == b -> (c * a == c * b)%Q)
      by (intros a b c Hc; rewrite Hc; reflexivity).
    apply Hcm. apply pi_psQ_ext. intros a Ha.
    assert (Ha1 : Nat.leb a n = true) by (apply Nat.leb_le; lia).
    assert (Ha2 : Nat.leb (j - a) n = true) by (apply Nat.leb_le; lia).
    rewrite Ha1, Ha2. cbn [andb].
    replace (n - (j - a)) with ((n - j) + a) by lia.
    pose proof (qeqT_imp_qeq _ _ (lni_qpow2_nat ((n - j) + a))) as Hq2.
    rewrite Hq2, Nat.pow_add_r.
    rewrite (Nat2Z.inj_mul (2 ^ (n - j)) (2 ^ a)).
    pose proof (qeqT_imp_qeq _ _ (lni_QmulZ (Z.of_nat (2 ^ (n - j))) (Z.of_nat (2 ^ a))))
      as HmZ.
    rewrite <- HmZ.
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) *
                    ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                     (Z.of_nat (2 ^ a) # 1)))%Q).
    { ring. }
    pose proof (qeqT_imp_qeq _ _ (bk_Qmul_nat (bkC n a * bkC n (j - a)) (2 ^ a))) as Hbm.
    rewrite Hbm. reflexivity. }
  transitivity (bv_negpow (n + j) *
    ((Z.of_nat (2 ^ (n - j)) # 1) *
       bk_psQ (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
              (Datatypes.S j) 1%Q))%Q.
  { assert (Hcm : forall a b c : Q, a == b -> (c * a == c * b)%Q)
      by (intros a b c Hc; rewrite Hc; reflexivity).
    apply Hcm.
    exact (pi_psQ_mul (Datatypes.S j) ((Z.of_nat (2 ^ (n - j)) # 1)%Q)
                      (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
                      1%Q). }
  rewrite Ht'. reflexivity.
Defined.

(* High segment (n < j <= 2n): bv_c n j == sign * S_j with S_j an
   explicit integer (the guard truncates a to [j-n, n]). *)
Lemma lni_bvc_high : forall n j : nat, hl_le_t (Datatypes.S n) j -> hl_le_t j (2 * n) ->
  sigT (fun t : Z => QeqT (bv_c n j) ((bv_negpow (n + j) * (t # 1))%Q)).
Proof.
  intros n j Hj1 Hj2.
  unfold bv_c.
  assert (Hpt : forall a : nat, hl_le_t (Datatypes.S a) (Datatypes.S j) ->
            sigT (fun z : Z =>
              QeqT (if andb (Nat.leb a n) (Nat.leb (j - a) n)
                    then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                          q_pow (2 # 1)%Q (n - (j - a)))%Q
                    else 0%Q)
                   ((z # 1)%Q))).
  { intros a Ha.
    destruct (andb (Nat.leb a n) (Nat.leb (j - a) n)) eqn:Eg.
    - apply andb_true_iff in Eg as [Eg1 Eg2].
      apply Nat.leb_le in Eg1. apply Nat.leb_le in Eg2.
      exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ (n - (j - a)))).
      apply qeq_imp_qeqT. cbv beta iota.
      pose proof (qeqT_imp_qeq _ _ (lni_qpow2_nat (n - (j - a)))) as Hq2.
      rewrite Hq2.
      pose proof (qeqT_imp_qeq _ _
                   (bk_Qmul_nat (bkC n a * bkC n (j - a)) (2 ^ (n - (j - a))))) as Hbm.
      rewrite Hbm. reflexivity.
    - exists 0%Z. apply qeq_imp_qeqT. cbv beta iota. reflexivity. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat =>
                 if andb (Nat.leb a n) (Nat.leb (j - a) n)
                 then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                       q_pow (2 # 1)%Q (n - (j - a)))%Q
                 else 0%Q) Hpt) as [t Ht].
  pose proof (qeqT_imp_qeq _ _ Ht) as Ht'.
  exists t. apply qeq_imp_qeqT. rewrite Ht'. reflexivity.
Defined.

(* ============================================================ *)
(* Sec 3.  Per-term integralization: the denominator d = |j-n|  *)
(* is absorbed by L_n (the main algebra).                       *)
(* ============================================================ *)

(* Explicit per-term body, equal on the definition face to the lambda
   inside bv_p. *)
Definition lni_bvpt (n : nat) : nat -> Q :=
  fun j : nat =>
    if Nat.eqb j n then 0%Q
    else (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1)))%Q.

(* Low-segment algebra (j < n, d := n - j >= 1): the two-power cancels
   and d divides L_n; witness explicit. *)
Lemma lni_low_branch : forall n j : nat, hl_le_t (Datatypes.S j) n ->
  sigT (fun z : Z =>
    QeqT (((Z.of_nat (hl_lcm_upto n) # 1) *
             (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                          ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q)
          ((z # 1)%Q)).
Proof.
  intros n j Hj.
  assert (Hjn : Datatypes.S j <= n) by (apply hl_le_t_to_le; exact Hj).
  assert (Hd1 : 1 <= n - j) by lia.
  assert (Hdn : n - j <= n) by lia.
  assert (Hp : 1 <= 2 ^ (n - j))
    by (apply hl_le_t_to_le; apply hl_pow2_ge1).
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.opp (Z.of_nat (n - j))) by lia.
  assert (Hcm : forall a b c : Q, a == b -> (c * a == c * b)%Q)
    by (intros a b c Hc; rewrite Hc; reflexivity).
  assert (Hcr : forall a b c : Q, a == b -> (a * c == b * c)%Q)
    by (intros a b c Hc; rewrite Hc; reflexivity).
  assert (Hmi : forall a b c : Q, a == b -> ((a - c) == (b - c))%Q)
    by (intros a b c Hc; unfold Qminus; rewrite Hc; reflexivity).
  assert (Hdv : forall a b c : Q, a == b -> ((a / c) == (b / c))%Q)
    by (intros a b c Hc; unfold Qdiv; rewrite Hc; reflexivity).
  destruct (lni_bvc_low n j Hj) as [t Ht].
  pose proof (qeqT_imp_qeq _ _ Ht) as Ht'.
  pose proof (qeqT_imp_qeq _ _ (lni_QsubZ (Z.of_nat (2 ^ (n - j))) 1%Z)) as HsubZ.
  assert (Hsub1 : (((Z.of_nat (2 ^ (n - j)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (n - j) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (n - j)) - 1)%Z) # 1)%Q).
    { exact HsubZ. }
    replace (Z.of_nat (2 ^ (n - j)) - 1)%Z with (Z.of_nat (2 ^ (n - j) - 1))%Z by lia.
    reflexivity. }
  pose proof (qeqT_imp_qeq _ _ (lni_qinv_opp (Z.of_nat (n - j)))) as Hden.
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (n - j)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (n - j)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (n - j) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  pose proof (qeqT_imp_qeq _ _
               (lni_qmul_inv_sub (2 ^ (n - j)) (hl_pow2_ge1 (n - j)))) as Himul.
  pose proof (qeqT_imp_qeq _ _ (lni_qpow2_nat (n - j))) as Hq2d.
  assert (Hbq : bv_q2 (Z.opp (Z.of_nat (n - j))) == ((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q)).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.opp (Z.of_nat (n - j)))) with false
      by (symmetry; apply Z.leb_gt; lia).
    rewrite Z.opp_involutive. rewrite Nat2Z.id. cbv beta iota.
    rewrite Hq2d. unfold Qdiv. ring. }
  assert (HL2 : ((Z.of_nat (2 ^ (n - j)) # 1) *
                   ((Z.of_nat (hl_lcm_upto n) # 1) *
                      ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                       ((Z.opp (Z.of_nat (n - j))) # 1))))%Q
                == (((Z.of_nat (2 ^ (n - j) - 1)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n / (n - j)) # 1)))%Q).
  { transitivity ((Z.of_nat (2 ^ (n - j)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) *
                       (((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q) *
                        (Qopp (/ ((Z.of_nat (n - j)) # 1))))))%Q.
    { apply Hcm. apply Hcm.
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) /
                    ((Z.opp (Z.of_nat (n - j))) # 1))%Q.
      { apply Hdv. apply Hmi. exact Hbq. }
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) *
                    (/ ((Z.opp (Z.of_nat (n - j))) # 1)))%Q.
      { unfold Qdiv. ring. }
      apply Hcm. exact Hden. }
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) * ((/ (Z.of_nat (2 ^ (n - j)) # 1)) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) *
                     (Qopp (/ ((Z.of_nat (n - j)) # 1)))))%Q.
    { ring. }
    rewrite Himul.
    transitivity ((((Z.of_nat (2 ^ (n - j)) # 1) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (n - j)) # 1))))%Q.
    { ring. }
    rewrite Hdiv2, Hsub1. reflexivity. }
  assert (Hcore : ((Z.of_nat (hl_lcm_upto n) # 1) *
                    (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                                 ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
                  == ((bv_negpow (n + j)) *
                      ((t * Z.of_nat (2 ^ (n - j) - 1) *
                        Z.of_nat (hl_lcm_upto n / (n - j))) # 1))%Q).
  { rewrite E.
    transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((bv_negpow (n + j) *
                      ((Z.of_nat (2 ^ (n - j)) # 1) * (t # 1))) *
                     ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                      ((Z.opp (Z.of_nat (n - j))) # 1))))%Q.
    { apply Hcm. apply Hcr. exact Ht'. }
    transitivity ((bv_negpow (n + j)) *
                    ((t # 1) * ((Z.of_nat (2 ^ (n - j)) # 1) *
                       ((Z.of_nat (hl_lcm_upto n) # 1) *
                          ((bv_q2 (Z.opp (Z.of_nat (n - j))) - 1%Q) /
                           ((Z.opp (Z.of_nat (n - j))) # 1))))))%Q.
    { ring. }
    rewrite HL2.
    transitivity ((bv_negpow (n + j)) *
                    (((t # 1) * ((Z.of_nat (2 ^ (n - j) - 1)) # 1)) *
                     ((Z.of_nat (hl_lcm_upto n / (n - j))) # 1)))%Q.
    { ring. }
    pose proof (qeqT_imp_qeq _ _ (lni_QmulZ t (Z.of_nat (2 ^ (n - j) - 1)))) as HmZ1.
    pose proof (qeqT_imp_qeq _ _
                 (lni_QmulZ (t * Z.of_nat (2 ^ (n - j) - 1))
                            (Z.of_nat (hl_lcm_upto n / (n - j))))) as HmZ2.
    rewrite HmZ1, HmZ2. reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (n - j) - 1) * Z.of_nat (hl_lcm_upto n / (n - j))))
    as [z Hz].
  exists z. apply qeq_imp_qeqT.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (n - j) - 1) *
                  Z.of_nat (hl_lcm_upto n / (n - j))) # 1))%Q.
  { exact Hcore. }
  exact (qeqT_imp_qeq _ _ Hz).
Defined.

(* High-segment algebra (n < j, d := j - n >= 1, d <= n): no two-power
   cancellation needed; d divides L_n directly; witness explicit. *)
Lemma lni_high_branch : forall n j : nat, hl_le_t (Datatypes.S n) j -> hl_le_t j (2 * n) ->
  sigT (fun z : Z =>
    QeqT (((Z.of_nat (hl_lcm_upto n) # 1) *
             (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                          ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q)
          ((z # 1)%Q)).
Proof.
  intros n j Hj1 Hj2.
  assert (Hn1 : n < j) by (apply hl_le_t_to_le in Hj1; lia).
  assert (Hk2 : j <= 2 * n) by (apply hl_le_t_to_le; exact Hj2).
  assert (Hd1 : 1 <= j - n) by lia.
  assert (Hdn : j - n <= n) by lia.
  assert (Hp : 1 <= 2 ^ (j - n))
    by (apply hl_le_t_to_le; apply hl_pow2_ge1).
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.of_nat (j - n)) by lia.
  assert (Hcm : forall a b c : Q, a == b -> (c * a == c * b)%Q)
    by (intros a b c Hc; rewrite Hc; reflexivity).
  assert (Hcr : forall a b c : Q, a == b -> (a * c == b * c)%Q)
    by (intros a b c Hc; rewrite Hc; reflexivity).
  assert (Hmi : forall a b c : Q, a == b -> ((a - c) == (b - c))%Q)
    by (intros a b c Hc; unfold Qminus; rewrite Hc; reflexivity).
  assert (Hdv : forall a b c : Q, a == b -> ((a / c) == (b / c))%Q)
    by (intros a b c Hc; unfold Qdiv; rewrite Hc; reflexivity).
  destruct (lni_bvc_high n j Hj1 Hj2) as [t Ht].
  pose proof (qeqT_imp_qeq _ _ Ht) as Ht'.
  pose proof (qeqT_imp_qeq _ _ (lni_QsubZ (Z.of_nat (2 ^ (j - n))) 1%Z)) as HsubZ.
  assert (Hsub1 : (((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (j - n) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (j - n)) - 1)%Z) # 1)%Q).
    { exact HsubZ. }
    replace (Z.of_nat (2 ^ (j - n)) - 1)%Z with (Z.of_nat (2 ^ (j - n) - 1))%Z by lia.
    reflexivity. }
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (j - n)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (j - n) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  pose proof (qeqT_imp_qeq _ _ (lni_qpow2_nat (j - n))) as Hq2d.
  assert (Hbq2 : bv_q2 (Z.of_nat (j - n)) == ((Z.of_nat (2 ^ (j - n)) # 1))%Q).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.of_nat (j - n))) with true
      by (symmetry; apply Z.leb_le; exact (Nat2Z.is_nonneg (j - n))).
    rewrite Nat2Z.id. cbv beta iota.
    rewrite Hq2d. reflexivity. }
  assert (HL3 : ((Z.of_nat (hl_lcm_upto n) # 1) *
                   ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1)))%Q
                == (((Z.of_nat (2 ^ (j - n) - 1)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1)))%Q).
  { transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) *
                     (/ ((Z.of_nat (j - n)) # 1))))%Q.
    { apply Hcm.
      transitivity ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) /
                    ((Z.of_nat (j - n)) # 1))%Q.
      { apply Hdv. apply Hmi. exact Hbq2. }
      unfold Qdiv. reflexivity. }
    transitivity ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (j - n)) # 1))))%Q.
    { ring. }
    rewrite Hdiv2, Hsub1. reflexivity. }
  assert (Hcore : ((Z.of_nat (hl_lcm_upto n) # 1) *
                    (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                                 ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
                  == ((bv_negpow (n + j)) *
                      ((t * Z.of_nat (2 ^ (j - n) - 1) *
                        Z.of_nat (hl_lcm_upto n / (j - n))) # 1))%Q).
  { rewrite E.
    transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((bv_negpow (n + j) * (t # 1)) *
                     ((bv_q2 (Z.of_nat (j - n)) - 1%Q) /
                      ((Z.of_nat (j - n)) # 1))))%Q.
    { apply Hcm. apply Hcr. exact Ht'. }
    transitivity ((bv_negpow (n + j)) *
                    ((t # 1) * ((Z.of_nat (hl_lcm_upto n) # 1) *
                       ((bv_q2 (Z.of_nat (j - n)) - 1%Q) /
                        ((Z.of_nat (j - n)) # 1)))))%Q.
    { ring. }
    rewrite HL3.
    transitivity ((bv_negpow (n + j)) *
                    (((t # 1) * ((Z.of_nat (2 ^ (j - n) - 1)) # 1)) *
                     ((Z.of_nat (hl_lcm_upto n / (j - n))) # 1)))%Q.
    { ring. }
    pose proof (qeqT_imp_qeq _ _ (lni_QmulZ t (Z.of_nat (2 ^ (j - n) - 1)))) as HmZ1.
    pose proof (qeqT_imp_qeq _ _
                 (lni_QmulZ (t * Z.of_nat (2 ^ (j - n) - 1))
                            (Z.of_nat (hl_lcm_upto n / (j - n))))) as HmZ2.
    rewrite HmZ1, HmZ2. reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (j - n) - 1) * Z.of_nat (hl_lcm_upto n / (j - n))))
    as [z Hz].
  exists z. apply qeq_imp_qeqT.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (j - n) - 1) *
                  Z.of_nat (hl_lcm_upto n / (j - n))) # 1))%Q.
  { exact Hcore. }
  exact (qeqT_imp_qeq _ _ Hz).
Defined.

(* ============================================================ *)
(* Sec 4.  Main supply theorems: the modified numerator B * L_n *)
(* and the plain limb A * L_n, both with explicit integer       *)
(* witnesses, plus the assembled integer pair.                  *)
(* ============================================================ *)

Definition lni_lbvp (n : nat) : Q := ((Z.of_nat (hl_lcm_upto n) # 1) * bv_p n)%Q.

(* Per-term bridge: k <= 2n implies L_n times the bv_p summand at k is
   integral, witness explicit. *)
Lemma lni_term_int : forall n k : nat, hl_le_t k (2 * n) ->
  sigT (fun z : Z => QeqT (((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q)
                       ((z # 1)%Q)).
Proof.
  intros n k Hk. assert (Hk2 : k <= 2 * n) by (apply hl_le_t_to_le; exact Hk).
  unfold lni_bvpt.
  destruct (Nat.eq_dec k n) as [Heq | Hne].
  - subst k. exists 0%Z. apply qeq_imp_qeqT. rewrite Nat.eqb_refl. ring.
  - assert (Eb : Nat.eqb k n = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite Eb.
    destruct (Nat.compare k n) eqn:Ecmp.
    + exfalso. apply Hne. apply Nat.compare_eq_iff. exact Ecmp.
    + apply (lni_low_branch n k). apply hl_le_to_le_t.
      assert (Hlt : k < n) by (apply Nat.compare_lt_iff; exact Ecmp). lia.
    + apply (lni_high_branch n k).
      * apply hl_le_to_le_t.
        assert (Hgt : n < k) by (apply (proj1 (Nat.compare_gt_iff k n)); exact Ecmp).
        lia.
      * apply hl_le_to_le_t. exact Hk2.
Defined.

(* Master integrality of the modified numerator L_n * p_n. *)
Theorem lni_bvp_lcm_int : forall n : nat,
  sigT (fun z : Z => QeqT (lni_lbvp n) ((z # 1)%Q)).
Proof.
  intro n.
  assert (Hpt : forall k : nat, hl_le_t (Datatypes.S k) (Datatypes.S (2 * n)) ->
            sigT (fun z : Z => QeqT (((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q)
                                ((z # 1)%Q))).
  { intros k Hk. apply (lni_term_int n k). apply hl_le_to_le_t.
    apply hl_le_t_to_le in Hk. lia. }
  destruct (lni_psQ_zsum_ex (Datatypes.S (2 * n))
              (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n j)%Q) Hpt)
    as [w Hw].
  exists (Z.opp w). apply qeq_imp_qeqT.
  unfold lni_lbvp.
  change (bv_p n) with (Qopp (bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)).
  transitivity ((Qopp ((Z.of_nat (hl_lcm_upto n) # 1) *
                        bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)))%Q.
  { ring. }
  transitivity ((Qopp (bk_psQ (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) *
                                              lni_bvpt n j)%Q)
                              (Datatypes.S (2 * n)) 1%Q)))%Q.
  { apply (qeqT_imp_qeq _ _). apply lni_Qopp_cong. apply qeq_imp_qeqT. symmetry.
    exact (pi_psQ_mul (Datatypes.S (2 * n)) ((Z.of_nat (hl_lcm_upto n) # 1)%Q)
                      (lni_bvpt n) 1%Q). }
  transitivity ((Qopp ((w # 1)%Q))).
  { apply (qeqT_imp_qeq _ _). apply lni_Qopp_cong. exact Hw. }
  exact (qeqT_imp_qeq _ _ (lni_QoppZ w)).
Defined.

(* Plain limb: L_n * q~_n is integral (one product bridge). *)
Theorem lni_qlcm_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1))
         ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n)).
  apply bk_Qmul_nat.
Defined.

(* Assembled pair of integers (L_n * q~_n, L_n * p_n) for the remodeled
   supply interface. *)
Theorem lni_supply_pair : forall n : nat,
  sigT (fun z : Z =>
    sigT (fun w : Z =>
      (QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1))
            ((z # 1)%Q)
        * QeqT (lni_lbvp n) ((w # 1)%Q))%type)).
Proof.
  intro n.
  destruct (lni_qlcm_int n) as [z Hz].
  destruct (lni_bvp_lcm_int n) as [w Hw].
  exists z, w. split; assumption.
Defined.

(* ============================================================ *)
(* Sec 5.  Numeric anchors (vm_compute on concrete pins; the    *)
(* k = 3 pin reads L_3 * p_3 = 262).                            *)
(* ============================================================ *)

Theorem lni_lbvp_anchor0 : QeqT (lni_lbvp 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

Theorem lni_lbvp_anchor1 : QeqT (lni_lbvp 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

Theorem lni_lbvp_anchor2 : QeqT (lni_lbvp 2) (18 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

Theorem lni_lbvp_anchor3 : QeqT (lni_lbvp 3) (262 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

Theorem lni_lbvp_anchor4 : QeqT (lni_lbvp 4) (2670 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

Theorem lni_lbvp_anchor5 : QeqT (lni_lbvp 5) (69994 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Defined.

(* ============================================================ *)
(* Premise audit: one Print Assumptions line per lemma and      *)
(* theorem of this piece.                                       *)
(* ============================================================ *)

Print Assumptions lni_Qopp_cong.
Print Assumptions lni_QoppZ.
Print Assumptions lni_Qmul_cong_r.
Print Assumptions lni_Qmul_cong_l.
Print Assumptions lni_Qplus_cong_l.
Print Assumptions lni_Qminus_cong_l.
Print Assumptions lni_Qdiv_cong_l.
Print Assumptions lni_QmulZ.
Print Assumptions lni_QaddZ.
Print Assumptions lni_QsubZ.
Print Assumptions lni_qpow1.
Print Assumptions lni_qpow2_nat.
Print Assumptions lni_qinv_opp.
Print Assumptions lni_qmul_inv_sub.
Print Assumptions lni_negpow_Zmul.
Print Assumptions lni_psQ_zsum_ex.
Print Assumptions lni_bvc_low.
Print Assumptions lni_bvc_high.
Print Assumptions lni_low_branch.
Print Assumptions lni_high_branch.
Print Assumptions lni_term_int.
Print Assumptions lni_bvp_lcm_int.
Print Assumptions lni_qlcm_int.
Print Assumptions lni_supply_pair.
Print Assumptions lni_lbvp_anchor0.
Print Assumptions lni_lbvp_anchor1.
Print Assumptions lni_lbvp_anchor2.
Print Assumptions lni_lbvp_anchor3.
Print Assumptions lni_lbvp_anchor4.
Print Assumptions lni_lbvp_anchor5.
