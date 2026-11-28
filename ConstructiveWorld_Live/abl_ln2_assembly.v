(* ========================================================================= *)
(* Module   : abl_ln2_assembly                                               *)
(* Mission. Assembly block for the ln2 irrationality chain. The pole series  *)
(*            u(n,k) = C(n+k,n)/((k+1)2^(k+1)) gets: (i) integer witnesses   *)
(*            z_n, w_n for A_n := L_n q~_n, B_n := L_n p_n (L_n=lcm(1..n));  *)
(*            (ii) the Real docking |A_n X - B_n| with the Ln2Bridge line;  *)
(*            (iii) the tail modulus |S_(M+d)-S_M| <= 2^(p+1)(3/4)^(SM-2p)  *)
(*            (p >= 1) and the p = 0 companion; (iv) positivity of the Real *)
(*            limit I_p; (v) the chain witness lna_supply_chain_core (sigT, *)
(*            six components). Also: the two dockings (pair and A-face),    *)
(*            lna_supply_rem' (B side filled by the witness; its two Real   *)
(*            limbs remain premise-fed, stated as such), head limbs (theta  *)
(*            = 4/5 < 1, 0 < |A_n|, 0 < clo_n), n = 1 anchors, hook.        *)
(* Dependencies. Stdlib QArith/Qabs/Arith/ZArith/Setoid/Lia/Extraction;      *)
(*            S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists          *)
(*            HansonLcm BeukersVariant Ln2Integrality Ln2Escape Ln2Bridge   *)
(*            RealIdentity UpReqLn2Irrational PsQReindex. The lnt_/lnr_/lni_ *)
(*            faces are rebuilt locally (R1-R3) from these landed faces     *)
(*            under their canonical names (upstream carriers not landed).   *)
(* Constructivity. Statement faces entirely Set-carried (QeqT/QltT/QleT',   *)
(*            real_eq/real_lt per-eps Bishop forms, sigT, pair-And); no Prop *)
(*            statement, no Prop component inside any Set carrier (the      *)
(*            QltT-nested-in-sigT shape of real_lt mirrors the landed S02   *)
(*            form). Definitions and Set-conclusion lemmas end in Defined;  *)
(*            Qed only on pure Prop reasoning bridges (== / Qle / Qlt / eq  *)
(*            / Not conclusions), all constructive. Prop premises on        *)
(*            nat/Z/Q; vm_compute only on concrete numeric pins (the u = 0  *)
(*            branch and the two n = 1 anchors); one audit line per lemma.  *)
(* Build. rocq c -native-compiler no -q -Q <Set Live root> "" <this file>.  *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm BeukersVariant Ln2Integrality.
Require Import Ln2Escape Ln2Bridge.
Require Import RealIdentity UpReqLn2Irrational.
Require Import PsQReindex.

Open Scope nat_scope.

(* ============================================================ *)
(* Section S: premise-form shims. The landed modules supply some leaf          *)
(* faces in Id/QeqT/NatLe form; the rebuilt chain faces consume them in       *)
(* the == / Qle / QleT' / eq form, so the conversions are fixed here.         *)
(* ============================================================ *)

Lemma lnz_id_eq : forall (A : Set) (x y : A), Id x y -> x = y.
Proof. intros A x y H. destruct H. reflexivity. Qed.

Lemma lnz_qlt_Z1 : forall z : Z, (0 < z)%Z -> Qlt 0 (z # 1)%Q.
Proof. intros z Hz. unfold Qlt. destruct z as [| p | p]; cbn [Qnum Qden]; lia. Qed.

Lemma lnz_Qeq_le : forall x y : Q, x == y -> Qle x y.
Proof. intros x y H. unfold Qle, Qeq in *. cbn in H |- *. lia. Qed.

Lemma lnz_qeq_leT' : forall x y : Q, x == y -> QleT' x y.
Proof. intros x y H. apply qeq_leT'. apply qeq_imp_qeqT. exact H. Defined.

Lemma lnz_Qmul_nat : forall a b : nat,
  ((Z.of_nat a # 1) * (Z.of_nat b # 1))%Q == (Z.of_nat (a * b) # 1)%Q.
Proof. intros a b. apply qeqT_imp_qeq. apply bk_Qmul_nat. Qed.

Lemma lnz_Qle_nat : forall a b : nat, (a <= b)%nat -> Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof. intros a b H. apply QleT'_to_Qle. apply bk_Qle_nat. apply NatLe_lift. exact H. Qed.

Lemma lnz_bkC_ratio : forall j k : nat, (k <= j)%nat ->
  bkC (Datatypes.S j) k * (Datatypes.S j - k) = bkC j k * Datatypes.S j.
Proof. intros j k H. apply (lnz_id_eq nat). apply rx_bkC_ratio. apply NatLe_lift. exact H. Qed.

Lemma lnz_qpow_succ : forall (x : Q) (n : nat), q_pow x (Datatypes.S n) == (x * q_pow x n)%Q.
Proof. intros x n. reflexivity. Qed.

Lemma lnz_qpow_add : forall (x : Q) (a b : nat), q_pow x (a + b) == (q_pow x a * q_pow x b)%Q.
Proof.
  intros x a b. induction a as [| a IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma lnt_pow2_ge1 : forall N : nat, 1 <= 2 ^ N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [Nat.pow]. lia.
Qed.

Print Assumptions lnz_id_eq.
Print Assumptions lnz_qlt_Z1.
Print Assumptions lnz_Qeq_le.
Print Assumptions lnz_qeq_leT'.
Print Assumptions lnz_Qmul_nat.
Print Assumptions lnz_Qle_nat.
Print Assumptions lnz_bkC_ratio.
Print Assumptions lnz_qpow_succ.
Print Assumptions lnz_qpow_add.

(* ============================================================ *)
(* Section R1: integrality supply (lni_ faces). Per-term integrality of the    *)
(* B-side summands under L_n, assembled into the integer supply pair.         *)
(* ============================================================ *)

Lemma lni_Qopp_cong : forall x y : Q, x == y -> (Qopp x) == (Qopp y).
Proof.
  intros x y H. unfold Qeq in *. cbn [Qopp Qnum Qden] in *.
  transitivity (Z.opp (Qnum x * Z.pos (Qden y))).
  - ring.
  - rewrite H. ring.
Qed.

Lemma lni_QoppZ : forall u : Z, (Qopp (u # 1))%Q == ((Z.opp u) # 1)%Q.
Proof. intro u. unfold Qeq. cbn [Qopp Qnum Qden Pos.mul]. ring. Qed.

Lemma lni_Qmul_cong_r : forall x y z : Q, x == y -> (x * z) == (y * z).
Proof. intros x y z H. rewrite H. reflexivity. Qed.

Lemma lni_Qmul_cong_l : forall x y z : Q, x == y -> (z * x) == (z * y).
Proof. intros x y z H. rewrite H. reflexivity. Qed.

Lemma lni_Qminus_cong_l : forall x y c : Q, x == y -> (x - c) == (y - c).
Proof. intros x y c H. unfold Qminus. rewrite H. reflexivity. Qed.

Lemma lni_Qdiv_cong_l : forall x y z : Q, x == y -> (x / z) == (y / z).
Proof. intros x y z H. unfold Qdiv. rewrite H. reflexivity. Qed.

Lemma lni_QmulZ : forall u v : Z, ((u # 1) * (v # 1))%Q == ((u * v) # 1)%Q.
Proof. intros u v. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring. Qed.

Lemma lni_QaddZ : forall u v : Z, ((u # 1) + (v # 1))%Q == ((u + v) # 1)%Q.
Proof. intros u v. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring. Qed.

Lemma lni_QsubZ : forall u v : Z, ((u # 1) - (v # 1))%Q == ((u - v) # 1)%Q.
Proof. intros u v. unfold Qeq, Qminus. cbn [Qopp Qnum Qden Qplus Pos.mul]. ring. Qed.

Lemma lni_qpow1 : forall N : nat, q_pow (1 # 1)%Q N == 1%Q.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma lni_qpow2_nat : forall k : nat, q_pow (2 # 1)%Q k == ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH.
    transitivity (((Z.of_nat 2) # 1) * ((Z.of_nat (2 ^ k)) # 1))%Q.
    { reflexivity. }
    rewrite lnz_Qmul_nat. cbn [Nat.pow]. reflexivity.
Qed.

Lemma lni_qinv_opp : forall u : Z, (/ (Qopp (u # 1)))%Q == (Qopp (/ (u # 1)))%Q.
Proof.
  intro u.
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
Qed.

Lemma lni_qmul_inv_sub : forall x : Q, ~ (x == 0)%Q -> (x * ((/ x) - 1))%Q == (1%Q - x)%Q.
Proof.
  intros x Hx.
  assert (Hinv : (x * (/ x))%Q == 1%Q) by (apply Qmult_inv_r; exact Hx).
  apply (proj1 (Qplus_inj_r (x * ((/ x) - 1)) (1%Q - x) x)).
  transitivity (1%Q).
  - transitivity (x * (/ x))%Q.
    + ring.
    + exact Hinv.
  - ring.
Qed.

Lemma lni_negpow_Zmul : forall (s : nat) (u : Z),
  sigT (fun u' : Z => (bv_negpow s * (u # 1))%Q == ((u' # 1)%Q)).
Proof.
  induction s as [| s IH]; intro u.
  - exists u. cbn [bv_negpow]. ring.
  - destruct (IH u) as [u' Hu'].
    exists (Z.opp u').
    cbn [bv_negpow].
    transitivity ((Qopp (bv_negpow s * (u # 1)))%Q).
    { ring. }
    transitivity ((Qopp ((u' # 1)%Q))).
    { apply lni_Qopp_cong. exact Hu'. }
    apply lni_QoppZ.
Defined.

Lemma lni_psQ_zsum_ex : forall (N : nat) (f : nat -> Q),
  (forall k : nat, k < N -> sigT (fun z : Z => f k == ((z # 1)%Q))) ->
  sigT (fun z : Z => bk_psQ f N 1%Q == ((z # 1)%Q)).
Proof.
  induction N as [| N IH]; intros f H.
  - exists 0%Z. cbn [bk_psQ]. ring.
  - assert (Hpre : forall k : nat, k < N -> sigT (fun z : Z => f k == ((z # 1)%Q))).
    { intros k Hk. apply H. lia. }
    destruct (IH f Hpre) as [z0 Hz0].
    destruct (H N (Nat.lt_succ_diag_r N)) as [z1 Hz1].
    exists (z0 + z1)%Z.
    cbn [bk_psQ].
    rewrite (lni_qpow1 N).
    rewrite Hz0, Hz1.
    transitivity (((z0 # 1)%Q + (z1 # 1)%Q)%Q).
    { ring. }
    apply lni_QaddZ.
Defined.

Lemma lni_bvc_low : forall n j : nat, j < n ->
  sigT (fun t : Z =>
    bv_c n j == (bv_negpow (n + j) * ((Z.of_nat (2 ^ (n - j)) # 1) * (t # 1))%Q)%Q).
Proof.
  intros n j Hj.
  unfold bv_c.
  assert (Hpt : forall a : nat, a < Datatypes.S j ->
            sigT (fun z : Z => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q
                         == ((z # 1)%Q))).
  { intros a Ha. exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)). ring. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q) Hpt)
    as [t Ht].
  exists t.
  transitivity (bv_negpow (n + j) *
    bk_psQ (fun a : nat => ((Z.of_nat (2 ^ (n - j)) # 1) *
              ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1))%Q)
            (Datatypes.S j) 1%Q)%Q.
  { apply lni_Qmul_cong_l. apply pi_psQ_ext. intros a Ha.
    assert (Ha1 : Nat.leb a n = true) by (apply Nat.leb_le; lia).
    assert (Ha2 : Nat.leb (j - a) n = true) by (apply Nat.leb_le; lia).
    rewrite Ha1, Ha2. cbn [andb].
    replace (n - (j - a)) with ((n - j) + a) by lia.
    rewrite lni_qpow2_nat, Nat.pow_add_r.
    rewrite (Nat2Z.inj_mul (2 ^ (n - j)) (2 ^ a)).
    rewrite <- (lni_QmulZ (Z.of_nat (2 ^ (n - j))) (Z.of_nat (2 ^ a))).
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) *
                    ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) * (Z.of_nat (2 ^ a) # 1)))%Q).
    { ring. }
    rewrite lnz_Qmul_nat. reflexivity. }
  transitivity (bv_negpow (n + j) *
    ((Z.of_nat (2 ^ (n - j)) # 1) *
       bk_psQ (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
              (Datatypes.S j) 1%Q))%Q.
  { apply lni_Qmul_cong_l.
    exact (pi_psQ_mul (Datatypes.S j) ((Z.of_nat (2 ^ (n - j)) # 1)%Q)
                      (fun a : nat => ((Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ a)) # 1)%Q)
                      1%Q). }
  rewrite Ht. ring.
Defined.

Lemma lni_bvc_high : forall n j : nat, n < j -> j <= 2 * n ->
  sigT (fun t : Z => bv_c n j == (bv_negpow (n + j) * (t # 1))%Q).
Proof.
  intros n j Hj1 Hj2.
  unfold bv_c.
  assert (Hpt : forall a : nat, a < Datatypes.S j ->
            sigT (fun z : Z => (if andb (Nat.leb a n) (Nat.leb (j - a) n)
                           then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                                 q_pow (2 # 1)%Q (n - (j - a)))%Q
                           else 0%Q) == ((z # 1)%Q))).
  { intros a Ha.
    destruct (andb (Nat.leb a n) (Nat.leb (j - a) n)) eqn:Eg.
    - apply andb_true_iff in Eg as [Eg1 Eg2].
      apply Nat.leb_le in Eg1. apply Nat.leb_le in Eg2.
      exists (Z.of_nat (bkC n a * bkC n (j - a) * 2 ^ (n - (j - a)))).
      cbv beta iota.
      rewrite lni_qpow2_nat, lnz_Qmul_nat. reflexivity.
    - exists 0%Z. cbv beta iota. reflexivity. }
  destruct (lni_psQ_zsum_ex (Datatypes.S j)
              (fun a : nat =>
                 if andb (Nat.leb a n) (Nat.leb (j - a) n)
                 then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                       q_pow (2 # 1)%Q (n - (j - a)))%Q
                 else 0%Q) Hpt) as [t Ht].
  exists t. rewrite Ht. reflexivity.
Defined.

Definition lni_bvpt (n : nat) : nat -> Q :=
  fun j : nat =>
    if Nat.eqb j n then 0%Q
    else (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1)))%Q.

Lemma lni_low_branch : forall n j : nat, j < n ->
  sigT (fun z : Z =>
    ((Z.of_nat (hl_lcm_upto n) # 1) *
       (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                    ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
    == ((z # 1)%Q)).
Proof.
  intros n j Hj.
  assert (Hd1 : 1 <= n - j) by lia.
  assert (Hdn : n - j <= n) by lia.
  assert (Hp : 1 <= 2 ^ (n - j)) by apply lnt_pow2_ge1.
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.opp (Z.of_nat (n - j))) by lia.
  destruct (lni_bvc_low n j Hj) as [t Ht].
  assert (HnzA2 : ~ (((Z.of_nat (2 ^ (n - j)) # 1)) == 0)%Q)
    by (apply (pi_Qneq0_nat (2 ^ (n - j))); exact Hp).
  assert (Hbq : bv_q2 (Z.opp (Z.of_nat (n - j))) == ((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q)).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.opp (Z.of_nat (n - j)))) with false
      by (symmetry; apply Z.leb_gt; lia).
    rewrite Z.opp_involutive. rewrite Nat2Z.id.
    rewrite lni_qpow2_nat. unfold Qdiv. ring. }
  assert (Hden : (/ ((Z.opp (Z.of_nat (n - j))) # 1))%Q
                 == (Qopp (/ ((Z.of_nat (n - j)) # 1)))%Q)
    by (apply (lni_qinv_opp (Z.of_nat (n - j)))).
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (n - j)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (n - j)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (n - j) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  assert (Hsub1 : (((Z.of_nat (2 ^ (n - j)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (n - j) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (n - j)) - 1)%Z) # 1)%Q).
    { apply lni_QsubZ. }
    replace (Z.of_nat (2 ^ (n - j)) - 1)%Z with (Z.of_nat (2 ^ (n - j) - 1))%Z by lia.
    reflexivity. }
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
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_l.
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) /
                    ((Z.opp (Z.of_nat (n - j))) # 1))%Q.
      { apply lni_Qdiv_cong_l. apply lni_Qminus_cong_l. exact Hbq. }
      transitivity ((((/ (Z.of_nat (2 ^ (n - j)) # 1))%Q - 1%Q)) *
                    (/ ((Z.opp (Z.of_nat (n - j))) # 1)))%Q.
      { unfold Qdiv. ring. }
      apply lni_Qmul_cong_l. exact Hden. }
    transitivity (((Z.of_nat (2 ^ (n - j)) # 1) * ((/ (Z.of_nat (2 ^ (n - j)) # 1)) - 1%Q)) *
                    ((Z.of_nat (hl_lcm_upto n) # 1) * (Qopp (/ ((Z.of_nat (n - j)) # 1)))))%Q.
    { ring. }
    rewrite (lni_qmul_inv_sub (Z.of_nat (2 ^ (n - j)) # 1) HnzA2).
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
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_r. exact Ht. }
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
    rewrite lni_QmulZ, lni_QmulZ.
    reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (n - j) - 1) * Z.of_nat (hl_lcm_upto n / (n - j))))
    as [z Hz].
  exists z.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (n - j) - 1) *
                  Z.of_nat (hl_lcm_upto n / (n - j))) # 1))%Q.
  { exact Hcore. }
  exact Hz.
Defined.

Lemma lni_high_branch : forall n j : nat, n < j -> j <= 2 * n ->
  sigT (fun z : Z =>
    ((Z.of_nat (hl_lcm_upto n) # 1) *
       (bv_c n j * ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                    ((Z.of_nat j - Z.of_nat n)%Z # 1))))%Q
    == ((z # 1)%Q)).
Proof.
  intros n j Hj1 Hj2.
  assert (Hd1 : 1 <= j - n) by lia.
  assert (Hdn : j - n <= n) by lia.
  assert (Hp : 1 <= 2 ^ (j - n)) by apply lnt_pow2_ge1.
  assert (E : (Z.of_nat j - Z.of_nat n)%Z = Z.of_nat (j - n)) by lia.
  destruct (lni_bvc_high n j Hj1 Hj2) as [t Ht].
  assert (Hbq2 : bv_q2 (Z.of_nat (j - n)) == ((Z.of_nat (2 ^ (j - n)) # 1))%Q).
  { unfold bv_q2.
    replace (Z.leb 0 (Z.of_nat (j - n))) with true
      by (symmetry; apply Z.leb_le; exact (Nat2Z.is_nonneg (j - n))).
    rewrite Nat2Z.id. apply lni_qpow2_nat. }
  assert (Hdiv2 : ((Z.of_nat (hl_lcm_upto n) # 1) * (/ ((Z.of_nat (j - n)) # 1)))%Q
                  == ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1))%Q).
  { transitivity (((Z.of_nat (hl_lcm_upto n) # 1) * ((1 # 1) / (Z.of_nat (j - n) # 1)))%Q).
    { unfold Qdiv. ring. }
    apply pi_div_Qeq; [lia | apply hl_lcm_divide_all; lia]. }
  assert (Hsub1 : (((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)%Q)
                  == (((Z.of_nat (2 ^ (j - n) - 1)) # 1)%Q)).
  { transitivity ((((Z.of_nat (2 ^ (j - n)) - 1)%Z) # 1)%Q).
    { apply lni_QsubZ. }
    replace (Z.of_nat (2 ^ (j - n)) - 1)%Z with (Z.of_nat (2 ^ (j - n) - 1))%Z by lia.
    reflexivity. }
  assert (HL3 : ((Z.of_nat (hl_lcm_upto n) # 1) *
                   ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1)))%Q
                == (((Z.of_nat (2 ^ (j - n) - 1)) # 1) *
                    ((Z.of_nat (hl_lcm_upto n / (j - n)) # 1)))%Q).
  { transitivity ((Z.of_nat (hl_lcm_upto n) # 1) *
                    ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) *
                     (/ ((Z.of_nat (j - n)) # 1))))%Q.
    { apply lni_Qmul_cong_l.
      transitivity ((((Z.of_nat (2 ^ (j - n)) # 1) - 1%Q)) /
                    ((Z.of_nat (j - n)) # 1))%Q.
      { apply lni_Qdiv_cong_l. apply lni_Qminus_cong_l. exact Hbq2. }
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
                     ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1))))%Q.
    { apply lni_Qmul_cong_l. apply lni_Qmul_cong_r. exact Ht. }
    transitivity ((bv_negpow (n + j)) *
                    ((t # 1) * ((Z.of_nat (hl_lcm_upto n) # 1) *
                       ((bv_q2 (Z.of_nat (j - n)) - 1%Q) / ((Z.of_nat (j - n)) # 1)))))%Q.
    { ring. }
    rewrite HL3.
    transitivity ((bv_negpow (n + j)) *
                    (((t # 1) * ((Z.of_nat (2 ^ (j - n) - 1)) # 1)) *
                     ((Z.of_nat (hl_lcm_upto n / (j - n))) # 1)))%Q.
    { ring. }
    rewrite lni_QmulZ, lni_QmulZ.
    reflexivity. }
  destruct (lni_negpow_Zmul (n + j)
              (t * Z.of_nat (2 ^ (j - n) - 1) * Z.of_nat (hl_lcm_upto n / (j - n))))
    as [z Hz].
  exists z.
  transitivity ((bv_negpow (n + j)) *
                ((t * Z.of_nat (2 ^ (j - n) - 1) * Z.of_nat (hl_lcm_upto n / (j - n))) # 1))%Q.
  { exact Hcore. }
  exact Hz.
Defined.

Definition lni_lbvp (n : nat) : Q := ((Z.of_nat (hl_lcm_upto n) # 1) * bv_p n)%Q.

Lemma lni_term_int : forall n k : nat, k <= 2 * n ->
  sigT (fun z : Z => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q == ((z # 1)%Q)).
Proof.
  intros n k Hk. unfold lni_bvpt.
  destruct (Nat.eq_dec k n) as [Heq | Hne].
  - subst k. exists 0%Z. rewrite Nat.eqb_refl. ring.
  - assert (Eb : Nat.eqb k n = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite Eb.
    destruct (Nat.compare k n) eqn:Ecmp.
    + exfalso. apply Hne. apply Nat.compare_eq_iff. exact Ecmp.
    + apply (lni_low_branch n k). apply Nat.compare_lt_iff. exact Ecmp.
    + apply (lni_high_branch n k).
      * apply (proj1 (Nat.compare_gt_iff k n)). exact Ecmp.
      * exact Hk.
Defined.

Lemma lni_bvp_lcm_int : forall n : nat,
  sigT (fun z : Z => QeqT (lni_lbvp n) ((z # 1)%Q)).
Proof.
  intro n.
  assert (Hpt : forall k : nat, k < Datatypes.S (2 * n) ->
            sigT (fun z : Z => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n k)%Q
                         == ((z # 1)%Q))).
  { intros k Hk. apply (lni_term_int n k). lia. }
  destruct (lni_psQ_zsum_ex (Datatypes.S (2 * n))
              (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n j)%Q) Hpt)
    as [w Hw].
  exists (Z.opp w). apply qeq_imp_qeqT.
  unfold lni_lbvp.
  change (bv_p n) with (Qopp (bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)).
  transitivity ((Qopp ((Z.of_nat (hl_lcm_upto n) # 1) *
                          bk_psQ (lni_bvpt n) (Datatypes.S (2 * n)) 1%Q)))%Q.
  { ring. }
  transitivity ((Qopp (bk_psQ (fun j : nat => ((Z.of_nat (hl_lcm_upto n) # 1) * lni_bvpt n j)%Q)
                              (Datatypes.S (2 * n)) 1%Q)))%Q.
  { apply lni_Qopp_cong. symmetry.
    exact (pi_psQ_mul (Datatypes.S (2 * n)) ((Z.of_nat (hl_lcm_upto n) # 1)%Q)
                      (lni_bvpt n) 1%Q). }
  transitivity ((Qopp ((w # 1)%Q))).
  { apply lni_Qopp_cong. exact Hw. }
  apply lni_QoppZ.
Defined.

Lemma lni_qlcm_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1)) ((z # 1)%Q)).
Proof.
  intro n.
  exists (Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n)).
  apply qeq_imp_qeqT. apply lnz_Qmul_nat.
Defined.

Theorem lni_supply_pair : forall n : nat,
  sigT (fun z : Z =>
    sigT (fun w : Z =>
      (QeqT ((Z.of_nat (hl_lcm_upto n) # 1) * (Z.of_nat (bk_Qn_qtilde n) # 1)) ((z # 1)%Q)
        * QeqT (lni_lbvp n) ((w # 1)%Q))%type)).
Proof.
  intro n.
  destruct (lni_qlcm_int n) as [z Hz].
  destruct (lni_bvp_lcm_int n) as [w Hw].
  exists z, w. split; [exact Hz | exact Hw].
Defined.

Print Assumptions lni_Qopp_cong.
Print Assumptions lni_QoppZ.
Print Assumptions lni_Qmul_cong_r.
Print Assumptions lni_Qmul_cong_l.
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

(* ============================================================ *)
(* Section R2: pole-series tail object (lnt_ faces). The term family and the   *)
(* ratio / power / partial-sum / gap chain up to the geometric modulus.       *)
(* ============================================================ *)

Lemma lnt_leT'_eq_l : forall x y z : Q, x == y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans y x z).
  - apply lnz_Qeq_le. apply Qeq_sym. exact H.
  - apply QleT'_to_Qle. exact Hq.
Defined.

Lemma lnt_leT'_eq_r : forall x y z : Q, y == z -> QleT' x y -> QleT' x z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact Hq.
  - apply lnz_Qeq_le. exact H.
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
    apply lnz_Qeq_le. exact H1. }
  apply (Qle_trans x (x * z * Qinv z)%Q y).
  - apply lnz_Qeq_le. exact E1.
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
  - apply lnz_Qeq_le. ring.
  - apply (Qle_trans (x * z) (y * z) (z * y)).
    + apply Qmult_le_compat_r; assumption.
    + apply lnz_Qeq_le. ring.
Qed.

Lemma lnt_qinv_mul_cancel : forall z : Q, ~ (z == 0%Q) -> Qinv z * z == 1.
Proof. intros z Hz. rewrite Qmult_comm. apply Qmult_inv_r. exact Hz. Qed.

Lemma lnt_pow2_pos : forall j : nat, Qlt 0 (q_pow (2 # 1)%Q j).
Proof.
  induction j as [| j IH].
  - cbn [q_pow]. apply lnz_qlt_Z1. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + apply lnz_qlt_Z1. lia.
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
    + rewrite lnz_qpow_succ. ring.
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
        -- apply lnz_Qeq_le. apply Qeq_sym. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. exact Hx.
      * assert (Er2 : ((- x) + x)%Q == 0%Q) by ring.
        apply lnz_Qeq_le. exact Er2.
  - assert (H1 : 1%Q == (1 + 0)%Q) by ring.
    apply lnz_Qeq_le. apply Qeq_sym. exact H1.
Defined.

Lemma lnt_qpow_Zofnat : forall j : nat,
  q_pow (2 # 1)%Q j == (Z.of_nat (2 ^ j) # 1)%Q.
Proof.
  induction j as [| j IH].
  - reflexivity.
  - rewrite lnz_qpow_succ, IH.
    change (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    apply lnz_Qmul_nat.
Qed.

Lemma lnt_key_pole : forall n k : nat,
  2 * n <= k + 4 -> 2 * (n + Datatypes.S k) <= 3 * (Datatypes.S (Datatypes.S k)).
Proof. intros n k H. lia. Qed.

Lemma lnt_bkC_le_pow2 : forall N k : nat, k <= N -> bkC N k <= 2 ^ N.
Proof.
  induction N as [| N IH]; intros k Hk.
  - assert (Hk0 : k = 0) by lia. subst k.
    cbn [bkC Nat.pow]. lia.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. assert (Hg := lnt_pow2_ge1 N). lia.
    + assert (Hk' : k' <= N) by lia.
      assert (H1 := IH k' Hk').
      destruct (le_lt_dec (Datatypes.S k') N) as [Hs | Hl].
      * assert (H2 := IH (Datatypes.S k') Hs).
        cbn [bkC Nat.pow]. assert (Hg := lnt_pow2_ge1 N). lia.
      * assert (H0 : bkC N (Datatypes.S k') = 0).
        { apply (lnz_id_eq nat). apply bkC_out. apply NatLe_lift. lia. }
        cbn [bkC Nat.pow]. rewrite H0.
        assert (Hg := lnt_pow2_ge1 N). lia.
Qed.

Lemma lnt_bkC_step : forall n m : nat,
  bkC (Datatypes.S (n + m)) n * Datatypes.S m = bkC (n + m) n * (n + Datatypes.S m).
Proof.
  intros n m.
  assert (Hsm : Datatypes.S (n + m) = n + Datatypes.S m) by lia.
  rewrite Hsm.
  assert (H1 := lnz_bkC_ratio (n + m) n (Nat.le_add_r n m)).
  replace (Datatypes.S (n + m) - n) with (Datatypes.S m) in H1 by lia.
  rewrite Hsm in H1. exact H1.
Qed.

Definition lnt_pterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

Theorem lnt_pterm_pos : forall n k : nat, QltT 0 (lnt_pterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnt_pterm, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : 1 <= bkC (n + k) n).
    { apply NatLe_drop. apply bkC_pos. apply NatLe_lift. lia. }
    assert (Hz : (0 <= Z.of_nat (bkC (n + k) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply lnz_qlt_Z1. lia.
    + apply lnt_pow2_pos.
Defined.

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
    rewrite (lnz_qpow_succ (2 # 1)%Q (Datatypes.S k)). reflexivity. }
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
  assert (Ha1 : Qlt 0 a1) by (apply lnz_qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply lnz_qlt_Z1; lia).
  assert (HQp : Qlt 0 Qp) by apply lnt_pow2_pos.
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat; [exact Ha1 | apply Qmult_lt_0_compat;
         [apply lnz_qlt_Z1; lia | exact HQp]]).
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
      by (apply lnz_Qle_nat; exact Hnat).
    assert (HassocL : (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
                    = 2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
    assert (HassocR : (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k))
                    = 3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HassocL, HassocR in H1.
    assert (E1 : (Z.of_nat (bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q
                 == (C1 * a0)%Q) by (symmetry; apply lnz_Qmul_nat).
    assert (E2 : (Z.of_nat (bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q
                 == (C0 * a1)%Q) by (symmetry; apply lnz_Qmul_nat).
    rewrite <- (lnz_Qmul_nat 2 (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) in H1.
    rewrite <- (lnz_Qmul_nat 3 (bkC (n + k) n * Datatypes.S (Datatypes.S k))) in H1.
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
      + apply lnz_Qeq_le. exact Hxz.
      + apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qmult_lt_0_compat;
            [apply lnz_qlt_Z1; lia | exact HQp].
        * apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- apply lnz_Qeq_le. ring.
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                         * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ apply lnz_Qeq_le. rewrite Hyz. ring. }
  apply (Qle_trans (lnt_pterm n (Datatypes.S k))
           (C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q
           ((3 # 4)%Q * lnt_pterm n k)%Q).
  - apply lnz_Qeq_le. exact HsS.
  - apply (Qle_trans _ ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q _).
    + exact Hmain.
    + apply lnz_Qeq_le.
      assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnt_pterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact Ey.
Defined.

Theorem lnt_pterm_pow : forall (n k j : nat),
  2 * n <= k + 4 -> QleT' (lnt_pterm n (k + j))
    ((lnt_pterm n k * q_pow (3 # 4)%Q j)%Q).
Proof.
  intros n k j H. induction j as [| j IH].
  - apply lnt_leT'_eq_r with (y := (lnt_pterm n k * 1)%Q).
    + cbn [q_pow]. rewrite Qmult_1_r. apply Qeq_refl.
    + apply lnz_qeq_leT'. replace (k + 0) with k by lia.
      rewrite Qmult_1_r. apply Qeq_refl.
  - apply lnt_leT'_eq_r with
      (y := (lnt_pterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
    + rewrite lnz_qpow_succ. ring.
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

Theorem lnt_geo_partial : forall d : nat,
  sum_upto d (fun i : nat => q_pow (3 # 4)%Q i)
  == (4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q.
Proof.
  induction d as [| d IH].
  - cbn [sum_upto q_pow]. ring.
  - cbn [sum_upto]. rewrite lnz_qpow_succ, IH. ring.
Qed.

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

Theorem lnt_pterm_tail : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M)).
Proof.
  intros n M d H.
  apply qleT'_trans with
    (lnt_pterm n (Datatypes.S M)
       * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q.
  - apply lnt_leT'_eq_r with
      (y := sum_upto d (fun i : nat =>
                              (lnt_pterm n (Datatypes.S M)
                                  * q_pow (3 # 4)%Q i)%Q)).
    + rewrite lnt_sum_scale, lnt_geo_partial. apply Qeq_refl.
    + apply lnt_sum_le. intros i Hi.
      apply (qleT'_trans (lnt_pterm n (M + Datatypes.S i))
              (lnt_pterm n (Datatypes.S M + i))
              (lnt_pterm n (Datatypes.S M) * q_pow (3 # 4)%Q i)).
      * apply lnz_qeq_leT'.
        replace (M + Datatypes.S i) with (Datatypes.S M + i) by lia.
        apply Qeq_refl.
      * apply lnt_pterm_pow. lia.
  - apply qleT'_trans with
      (lnt_pterm n (Datatypes.S M) * ((4 # 1)%Q * 1)%Q)%Q.
    + apply (qleT'_mult_compat_l ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)
               ((4 # 1)%Q * 1)%Q (lnt_pterm n (Datatypes.S M))).
      * apply qltT_leT'. apply lnt_pterm_pos.
      * apply qleT'_mult_compat_l.
        { apply lnt_q4_le0. }
        { apply lnt_sub_le1. apply lnt_pow_pos_le. }
    + apply lnz_qeq_leT'. ring.
Defined.

Theorem lnt_pterm_gap : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply Qle_to_QleT'.
    apply (Qplus_le_compat
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
      ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnt_pterm_tail. exact H.
Defined.

Theorem lnt_pterm_peak : forall n k : nat,
  1 <= n -> QleT' (lnt_pterm n k) (q_pow (2 # 1)%Q (n - 1)).
Proof.
  intros n k Hn. apply Qle_to_QleT'.
  assert (Ha0 : Qlt 0 (Z.of_nat (Datatypes.S k) # 1)%Q) by (apply lnz_qlt_Z1; lia).
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
    + apply lnz_Qeq_le.
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
        rewrite <- lnt_qpow_Zofnat, lnz_qpow_add. reflexivity. }
      apply (Qle_trans (Z.of_nat (bkC (n + k) n) # 1)%Q
              (Z.of_nat (2 ^ (n + k)) # 1)%Q
              ((q_pow (2 # 1)%Q (n - 1) *
                  ((Z.of_nat (Datatypes.S k) # 1) *
                      q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
      * apply lnz_Qle_nat. apply lnt_bkC_le_pow2. lia.
      * apply (Qle_trans _ (q_pow (2 # 1)%Q (n - 1) *
                               q_pow (2 # 1)%Q (Datatypes.S k))%Q _).
        -- apply lnz_Qeq_le. exact Hbr.
        -- apply (Qle_trans
              (q_pow (2 # 1)%Q (n - 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 (1 * q_pow (2 # 1)%Q (Datatypes.S k)))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 ((Z.of_nat (Datatypes.S k) # 1) *
                    q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** apply lnz_Qeq_le. ring.
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** assert (H1a0 : Qle 1 (Z.of_nat (Datatypes.S k) # 1)%Q)
                   by (apply (lnz_Qle_nat 1 (Datatypes.S k)); lia).
                 apply Qmult_le_compat_r;
                   [exact H1a0 | apply Qlt_le_weak; exact HQp].
Defined.

Theorem lnt_gap_geo : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S n)
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)%Q.
  - apply lnt_pterm_gap. lia.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hpow := lnt_pterm_pow n (2 * n) (Datatypes.S M - 2 * n) ltac:(lia)).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnt_pterm n (2 * n)) (q_pow (2 # 1)%Q (n - 1)))
        by (apply lnt_pterm_peak; exact Hn).
      assert (Hchain : QleT' (lnt_pterm n (Datatypes.S M))
                         (q_pow (2 # 1)%Q (n - 1)
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))).
      { apply qleT'_trans with
          ((lnt_pterm n (2 * n)) * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q.
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnt_pterm n (2 * n))
                   (q_pow (2 # 1)%Q (n - 1))
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))
                      ((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
                          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q).
      { apply (qleT'_mult_compat_l (lnt_pterm n (Datatypes.S M))
                 (q_pow (2 # 1)%Q (n - 1)
                    * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)) (4 # 1)%Q
                 lnt_rho_le0 Hchain). }
      assert (E42 : ((4 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q
                    == q_pow (2 # 1)%Q (Datatypes.S n)).
      { replace (Datatypes.S n) with (2 + (n - 1)) by lia.
        rewrite lnz_qpow_add. cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q
        ((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
        ((q_pow (2 # 1)%Q (Datatypes.S n)) *
            q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      * rewrite <- E42. ring.
      * exact Hxy.
Defined.

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
Print Assumptions lnt_pow2_ge1.
Print Assumptions lnt_bkC_le_pow2.
Print Assumptions lnt_bkC_step.
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

(* ============================================================ *)
(* Section R3: Real wrap of the pole series (lnr_ faces). Partial sums, the    *)
(* vanishing engine, the Cauchy modulus, the Real carrier and its strict       *)
(* positivity, the identity-leg transfer, and the line object.                *)
(* ============================================================ *)

Lemma lnr_qmult_lt_compat_l : forall x y z : Q,
  Qlt 0 z -> Qlt x y -> Qlt (z * x) (z * y).
Proof.
  intros x y z Hz Hxy.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_lt_compat_r; assumption.
Qed.

Lemma lnr_qhalf_lt : forall q : Q, Qlt 0 q -> Qlt ((1 # 2)%Q * q) q.
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  unfold Qlt in Hq |- *. cbn [Qnum Qden Qmult] in *.
  lia.
Qed.

Lemma lnr_pterm_pos_Qle : forall p k : nat, Qle 0 (lnt_pterm p k).
Proof.
  intros p k. apply Qlt_le_weak. apply QltT_to_Qlt. apply lnt_pterm_pos.
Qed.

Lemma lnr_qlt_transfer_l : forall x y z : Q, Qeq x y -> Qlt y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. apply (Qle_lt_trans x y z).
  - apply lnz_Qeq_le. exact Hxy.
  - exact Hyz.
Qed.

Lemma lnr_qlt_transfer_r : forall x y z : Q, Qlt x y -> Qeq y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. apply (Qlt_le_trans x y z).
  - exact Hxy.
  - apply lnz_Qeq_le. exact Hyz.
Qed.

Lemma lnr_qltT_transfer_l : forall x y z : Q, Qeq x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. apply Qlt_to_QltT. apply (Qle_lt_trans x y z).
  - apply lnz_Qeq_le. exact Hxy.
  - apply QltT_to_Qlt. exact Hyz.
Defined.

Lemma lnr_qltT_transfer_r : forall x y z : Q, Qeq y z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hxy. apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hxy.
  - apply lnz_Qeq_le. exact Hyz.
Defined.

Lemma lnr_qdiv_lt_intro_pre : forall a b eps dv : Q,
  Qlt 0 dv -> Qlt (a * b) (eps * dv) -> Qlt (a * (b * Qinv dv)) eps.
Proof.
  intros a b eps dv Hdv H.
  assert (Hinv : (Qinv dv * dv)%Q == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hdv).
  apply (lnr_qlt_transfer_l _ ((a * b) * Qinv dv)%Q).
  - ring.
  - apply (lnr_qlt_transfer_r _ ((eps * dv) * Qinv dv)%Q).
    + apply Qmult_lt_compat_r.
      * apply Qinv_lt_0_compat. exact Hdv.
      * exact H.
    + transitivity (eps * (Qinv dv * dv))%Q.
      * ring.
      * rewrite Hinv. ring.
Qed.

Lemma lnr_q3divz_lt : forall (c z pn : Z) (pd : positive),
  (0 < c)%Z -> (0 < z)%Z -> (0 < pn)%Z ->
  (c * 3 * Z.pos pd < pn * z)%Z ->
  Qlt ((c # 1)%Q * ((3 # 1)%Q / ((z # 1)%Q))) ((pn # pd)%Q).
Proof.
  intros c z pn pd Hc Hz Hpn H.
  unfold Qlt, Qdiv.
  destruct z as [| p | p]; cbn in Hz |- *.
  all: try lia.
  all: cbn [Qnum Qden Qmult Qinv Pos.mul]; lia.
Qed.

Lemma lnr_qdivint_antitone : forall (c z1 z2 : Z),
  (0 < c)%Z -> (0 < z2)%Z -> (z2 < z1)%Z ->
  Qlt ((c # 1)%Q / ((z1 # 1)%Q)) ((c # 1)%Q / ((z2 # 1)%Q)).
Proof.
  intros c z1 z2 Hc H2 Hlt.
  unfold Qlt, Qdiv.
  destruct z1 as [| p | p] eqn:E1; cbn in Hlt, E1 |- *;
    destruct z2 as [| q | q] eqn:E2; cbn in H2, E2 |- *.
  all: try lia.
  all: cbn [Qnum Qden Qmult Qinv Pos.mul]; nia.
Qed.

Definition lnr_psum (p M : nat) : Q := sum_upto (Datatypes.S M) (lnt_pterm p).

Lemma lnr_psum_head : forall p : nat, lnr_psum p 0 == lnt_pterm p 0.
Proof.
  intro p. unfold lnr_psum. cbn [sum_upto]. ring.
Qed.

Lemma lnr_psum_mono : forall p m k : nat,
  (m <= k)%nat -> Qle (lnr_psum p m) (lnr_psum p k).
Proof.
  intros p m k H.
  assert (Hk : (k = m + (k - m))%nat) by lia.
  remember (k - m)%nat as d eqn:Hd.
  subst k. clear Hd H.
  induction d as [| d IH].
  - replace (m + 0) with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d) with (Datatypes.S (m + d)) by lia.
    unfold lnr_psum in IH |- *. cbn [sum_upto].
    apply (Qle_trans _ (sum_upto (m + d) (lnt_pterm p)
                        + lnt_pterm p (m + d))%Q).
    + exact IH.
    + apply (Qle_trans _ (sum_upto (m + d) (lnt_pterm p)
                          + lnt_pterm p (m + d) + 0)%Q).
      * apply lnz_Qeq_le. ring.
      * exact (Qplus_le_compat
                 (sum_upto (m + d) (lnt_pterm p) + lnt_pterm p (m + d))%Q
                 (sum_upto (m + d) (lnt_pterm p) + lnt_pterm p (m + d))%Q
                 0%Q (lnt_pterm p (Datatypes.S (m + d)))
                 (Qle_refl _)
                 (lnr_pterm_pos_Qle p (Datatypes.S (m + d)))).
Qed.

Lemma lnr_q34_pow_le3 : forall K : nat,
  Qle (q_pow (3 # 4)%Q K) ((3 # 1)%Q / ((Z.of_nat K + 3) # 1)%Q)%Q.
Proof.
  induction K as [| K IH].
  - cbn [q_pow]. unfold Qle, Qdiv. cbn. lia.
  - rewrite lnz_qpow_succ.
    apply (Qle_trans _ ((3 # 4)%Q * ((3 # 1)%Q / ((Z.of_nat K + 3) # 1)%Q))%Q).
    + apply lnt_Qmult_le_compat_l.
      * apply Qlt_le_weak. apply lnz_qlt_Z1. lia.
      * exact IH.
    + unfold Qle, Qdiv.
      destruct (Z.of_nat K + 3)%Z as [| p1 | p1] eqn:E1; cbn in E1 |- *;
        destruct (Z.of_nat (Datatypes.S K) + 3)%Z as [| p2 | p2] eqn:E2;
          cbn in E2 |- *.
      all: try lia.
      all: cbn [Qnum Qden Qmult Qinv Pos.mul]; lia.
Qed.

Definition lnr_gapbound (p m : nat) : Q :=
  (q_pow (2 # 1)%Q (Datatypes.S p) * q_pow (3 # 4)%Q (Datatypes.S m - 2 * p))%Q.

Theorem lnr_vanish : forall (p : nat) (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, (N <= m)%nat -> QltT (lnr_gapbound p m) eps).
Proof.
  intros p [pn pd] Heps.
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (2 * p + (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd)))%nat.
  intros m Hm.
  assert (HE : (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd) + 1
                <= Datatypes.S m - 2 * p)%nat) by lia.
  assert (HA1 : (0 < Z.of_nat (2 ^ Datatypes.S p))%Z).
  { apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S p))).
    assert (Hg := lnt_pow2_ge1 (Datatypes.S p)). lia. }
  assert (HApos : Qlt 0 ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q))
    by (apply lnz_qlt_Z1; exact HA1).
  assert (HAw : (1 <= Z.of_nat (2 ^ Datatypes.S p))%Z) by lia.
  assert (HZK : (Z.of_nat (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd))
                = 3 * Z.of_nat (2 ^ Datatypes.S p) * Z.pos pd)%Z).
  { rewrite (Nat2Z.inj_mul (3 * 2 ^ Datatypes.S p) (Z.to_nat (Z.pos pd))).
    rewrite (Z2Nat.id (Z.pos pd)) by lia.
    rewrite (Nat2Z.inj_mul 3 (2 ^ Datatypes.S p)). lia. }
  apply Qlt_to_QltT.
  unfold lnr_gapbound. rewrite lnt_qpow_Zofnat.
  apply (Qlt_trans _ ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q
                      * ((3 # 1)%Q / ((Z.of_nat (3 * 2 ^ Datatypes.S p
                                            * Z.to_nat (Z.pos pd)) + 3) # 1)%Q))%Q).
  - apply (Qle_lt_trans _ ((Z.of_nat (2 ^ Datatypes.S p) # 1)%Q
                           * ((3 # 1)%Q / ((Z.of_nat (Datatypes.S m - 2 * p) + 3) # 1)%Q))%Q).
    + apply lnt_Qmult_le_compat_l.
      * apply Qlt_le_weak. exact HApos.
      * apply lnr_q34_pow_le3.
    + apply lnr_qmult_lt_compat_l.
      * exact HApos.
      * apply lnr_qdivint_antitone.
        -- lia.
        -- lia.
        -- lia.
  - apply (lnr_q3divz_lt (Z.of_nat (2 ^ Datatypes.S p))
            (Z.of_nat (3 * 2 ^ Datatypes.S p * Z.to_nat (Z.pos pd)) + 3)%Z
            pn pd).
    + exact HA1.
    + lia.
    + exact Hpn.
    + rewrite HZK. nia.
Defined.

Lemma lnr_gap_modulus : forall (p M d : nat),
  (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
  QleT' (lnr_psum p (M + d) - lnr_psum p M)%Q (lnr_gapbound p M).
Proof.
  intros p M d Hp HM.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (lnr_psum p M + lnr_gapbound p M - lnr_psum p M)%Q).
  - apply (Qplus_le_compat (lnr_psum p (M + d))
                           (lnr_psum p M + lnr_gapbound p M)%Q
                           (- lnr_psum p M)%Q (- lnr_psum p M)%Q).
    + apply QleT'_to_Qle. exact (lnt_gap_geo p M d Hp HM).
    + apply Qle_refl.
  - apply lnz_Qeq_le. ring.
Defined.

Lemma lnr_gap_mod0 : forall (M d : nat),
  QleT' (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q
        ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q.
Proof.
  intros M d.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (lnr_psum 0 M + (4 # 1)%Q * lnt_pterm 0 (Datatypes.S M)
                      - lnr_psum 0 M)%Q).
  - apply (Qplus_le_compat (lnr_psum 0 (M + d))
                           (lnr_psum 0 M + (4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q
                           (- lnr_psum 0 M)%Q (- lnr_psum 0 M)%Q).
    + apply QleT'_to_Qle. exact (lnt_pterm_gap 0 M d ltac:(lia)).
    + apply Qle_refl.
  - apply lnz_Qeq_le. ring.
Defined.

Theorem lnr_cauchy : forall p : nat, cauchy (lnr_psum p).
Proof.
  intro p. destruct p as [| p'].
  - intros eps Heps.
    destruct eps as [pn pd].
    pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
    unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
    assert (Hpn : (0 < pn)%Z) by lia.
    assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
    exists (2 * Z.to_nat (Z.pos pd)).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum 0 m - lnr_psum 0 n)%Q
                     == (lnr_psum 0 m - lnr_psum 0 n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lnr_psum 0 n - lnr_psum 0 n)%Q).
        - apply lnz_Qeq_le. ring.
        - apply (Qplus_le_compat (lnr_psum 0 n) (lnr_psum 0 m)
                                 (- lnr_psum 0 n)%Q (- lnr_psum 0 n)%Q).
          + apply lnr_psum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S n))%Q).
      * apply QleT'_to_Qle. apply lnr_gap_mod0.
      * assert (HM2 : (2 * Z.to_nat (Z.pos pd) <= Datatypes.S n)%nat) by lia.
        assert (Eb : bkC (0 + Datatypes.S n) 0 = 1%nat) by reflexivity.
        assert (Hw2z : (2 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z).
        { assert (Hw2 : (2 <= 2 ^ Datatypes.S (Datatypes.S n))%nat).
          { assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S n))).
            cbn [Nat.pow] in Hg |- *. lia. }
          apply (proj1 (Nat2Z.inj_le 2 (2 ^ Datatypes.S (Datatypes.S n)))).
          exact Hw2. }
        assert (Hmul : (2 * Z.of_nat (Datatypes.S (Datatypes.S n))
                        <= Z.of_nat (Datatypes.S (Datatypes.S n))
                          * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z) by nia.
        unfold lnt_pterm, Qdiv.
        rewrite Eb, lnt_qpow_Zofnat.
        apply (lnr_qdiv_lt_intro_pre ((4 # 1)%Q) ((Z.of_nat 1 # 1)%Q)
                                     ((pn # pd)%Q)
                                     (((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)%Q
                                       * ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) # 1)%Q)%Q))).
        -- apply Qmult_lt_0_compat.
           ++ apply lnz_qlt_Z1. lia.
           ++ apply lnz_qlt_Z1.
              apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S (Datatypes.S n)))).
              assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S n))). lia.
        -- unfold Qlt. change (Z.of_nat 1) with 1%Z.
           cbn [Qnum Qden Qmult Pos.mul]. rewrite Pos.mul_1_r.
           assert (HM : (Z.of_nat (Datatypes.S (Datatypes.S n))
                         * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                         <= pn * (Z.of_nat (Datatypes.S (Datatypes.S n))
                                  * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))))%Z) by nia.
           lia.
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum 0 m - lnr_psum 0 n)%Q
                     == (lnr_psum 0 n - lnr_psum 0 m)%Q).
      { assert (Hmono : Qle (lnr_psum 0 m) (lnr_psum 0 n))
          by (apply lnr_psum_mono; lia).
        assert (Hneg : Qle (lnr_psum 0 m - lnr_psum 0 n)%Q 0%Q).
        { apply (Qle_trans _ (lnr_psum 0 n - lnr_psum 0 n)%Q).
          - apply (Qplus_le_compat (lnr_psum 0 m) (lnr_psum 0 n)
                                   (- lnr_psum 0 n)%Q (- lnr_psum 0 n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply lnz_Qeq_le. ring. }
        apply Qeq_trans with (-(lnr_psum 0 m - lnr_psum 0 n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ ((4 # 1)%Q * lnt_pterm 0 (Datatypes.S m))%Q).
      * apply QleT'_to_Qle. apply lnr_gap_mod0.
      * assert (HM2 : (2 * Z.to_nat (Z.pos pd) <= Datatypes.S m)%nat) by lia.
        assert (Eb : bkC (0 + Datatypes.S m) 0 = 1%nat) by reflexivity.
        assert (Hw2z : (2 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)))%Z).
        { assert (Hw2 : (2 <= 2 ^ Datatypes.S (Datatypes.S m))%nat).
          { assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S m))).
            cbn [Nat.pow] in Hg |- *. lia. }
          apply (proj1 (Nat2Z.inj_le 2 (2 ^ Datatypes.S (Datatypes.S m)))).
          exact Hw2. }
        assert (Hmul : (2 * Z.of_nat (Datatypes.S (Datatypes.S m))
                        <= Z.of_nat (Datatypes.S (Datatypes.S m))
                          * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)))%Z) by nia.
        unfold lnt_pterm, Qdiv.
        rewrite Eb, lnt_qpow_Zofnat.
        apply (lnr_qdiv_lt_intro_pre ((4 # 1)%Q) ((Z.of_nat 1 # 1)%Q)
                                     ((pn # pd)%Q)
                                     (((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                                       * ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S m)) # 1)%Q)%Q))).
        -- apply Qmult_lt_0_compat.
           ++ apply lnz_qlt_Z1. lia.
           ++ apply lnz_qlt_Z1.
              apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S (Datatypes.S m)))).
              assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S m))). lia.
        -- unfold Qlt. change (Z.of_nat 1) with 1%Z.
           cbn [Qnum Qden Qmult Pos.mul]. rewrite Pos.mul_1_r.
           assert (HM : (Z.of_nat (Datatypes.S (Datatypes.S m))
                         * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m))
                         <= pn * (Z.of_nat (Datatypes.S (Datatypes.S m))
                                  * Z.of_nat (2 ^ Datatypes.S (Datatypes.S m))))%Z) by nia.
           lia.
  - intros eps Heps.
    destruct (lnr_vanish (Datatypes.S p') eps Heps) as [N Hv].
    exists (Nat.max N (2 * Datatypes.S p')).
    intros m n Hm Hn.
    apply NatLe_drop in Hm. apply NatLe_drop in Hn.
    destruct (Nat.leb n m) eqn:Hleb.
    + apply Nat.leb_le in Hleb.
      assert (Hd : (m = n + (m - n))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q
                     == (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q).
      { apply Qabs_pos.
        apply (Qle_trans _ (lnr_psum (Datatypes.S p') n - lnr_psum (Datatypes.S p') n)%Q).
        - apply lnz_Qeq_le. ring.
        - apply (Qplus_le_compat (lnr_psum (Datatypes.S p') n) (lnr_psum (Datatypes.S p') m)
                                 (- lnr_psum (Datatypes.S p') n)%Q (- lnr_psum (Datatypes.S p') n)%Q).
          + apply lnr_psum_mono. exact Hleb.
          + apply Qle_refl. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ (lnr_gapbound (Datatypes.S p') n)).
      * apply QleT'_to_Qle. apply lnr_gap_modulus; lia.
      * apply QltT_to_Qlt. apply Hv. lia.
    + apply Nat.leb_gt in Hleb.
      assert (Hd : (n = m + (n - m))%nat) by lia.
      assert (Eabs : Qabs (lnr_psum (Datatypes.S p') m - lnr_psum (Datatypes.S p') n)%Q
                     == (lnr_psum (Datatypes.S p') n - lnr_psum (Datatypes.S p') m)%Q).
      { assert (Hmono : Qle (lnr_psum (Datatypes.S p') m) (lnr_psum (Datatypes.S p') n))
          by (apply lnr_psum_mono; lia).
        assert (Hneg : Qle (lnr_psum (Datatypes.S p') m
                            - lnr_psum (Datatypes.S p') n)%Q 0%Q).
        { apply (Qle_trans _ (lnr_psum (Datatypes.S p') n
                              - lnr_psum (Datatypes.S p') n)%Q).
          - apply (Qplus_le_compat (lnr_psum (Datatypes.S p') m)
                                   (lnr_psum (Datatypes.S p') n)
                                   (- lnr_psum (Datatypes.S p') n)%Q
                                   (- lnr_psum (Datatypes.S p') n)%Q).
            + exact Hmono.
            + apply Qle_refl.
          - apply lnz_Qeq_le. ring. }
        apply Qeq_trans with (-(lnr_psum (Datatypes.S p') m
                                 - lnr_psum (Datatypes.S p') n)%Q).
        - apply Qabs_neg. exact Hneg.
        - ring. }
      apply (lnr_qltT_transfer_l _ _ _ Eabs). rewrite Hd.
      apply Qlt_to_QltT.
      apply (Qle_lt_trans _ (lnr_gapbound (Datatypes.S p') m)).
      * apply QleT'_to_Qle. apply lnr_gap_modulus; lia.
      * apply QltT_to_Qlt. apply Hv. lia.
Defined.

Definition lnr_Ireal_pack (u : Qseq) (Hu : cauchy u) : Real :=
  existT (fun u : Qseq => cauchy u) u Hu.

Definition lnr_Ireal (p : nat) : Real := lnr_Ireal_pack (lnr_psum p) (lnr_cauchy p).

Theorem lnr_Ireal_pos : forall p : nat, real_lt real_zero (lnr_Ireal p).
Proof.
  intro p.
  assert (Hpt0 : Qlt 0 (lnt_pterm p 0)) by (apply QltT_to_Qlt; apply lnt_pterm_pos).
  exists ((1 # 2)%Q * lnt_pterm p 0)%Q.
  split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + apply lnz_qlt_Z1. lia.
    + exact Hpt0.
  - exists 0%nat. intros k Hk.
    apply NatLe_drop in Hk.
    unfold lnr_Ireal, lnr_Ireal_pack, real_zero. cbn [projT1].
    assert (Ez : lnr_psum p k == (lnr_psum p k - 0)%Q) by ring.
    apply (lnr_qltT_transfer_r _ _ _ Ez).
    apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1 # 2)%Q * lnt_pterm p 0)%Q (lnt_pterm p 0)
                        (lnr_psum p k)).
    + apply lnr_qhalf_lt. exact Hpt0.
    + rewrite <- (lnr_psum_head p). apply lnr_psum_mono. lia.
Defined.

Theorem lnr_identity_leg_transfer : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnr_Ireal p)) ->
  ri_identity_leg lnr_Ireal -> ri_identity_leg I.
Proof.
  intros I HI Hleg n.
  apply (real_eq_trans (I n) (lnr_Ireal n) (ri_lineabs n)).
  - apply HI.
  - apply Hleg.
Defined.

Definition lnr_lA (n : nat) : Q :=
  (Z.of_nat (hl_lcm_upto n) # 1)%Q * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.
Definition lnr_lB (n : nat) : Q :=
  (Z.of_nat (hl_lcm_upto n) # 1)%Q * bv_p n.

Definition lnr_lineL (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const (lnr_lA n)) ri_real)
                      (real_opp (real_const (lnr_lB n)))).

Lemma lnr_lineL_proj : forall (n k : nat),
  projT1 (lnr_lineL n) k == Qabs ((lnr_lA n * ln2i_x k - lnr_lB n)%Q).
Proof.
  intros n k. unfold lnr_lineL.
  rewrite (qeqT_imp_qeq _ _ (real_abs_proj _ _)), (qeqT_imp_qeq _ _ (real_plus_proj _ _ _)),
          (qeqT_imp_qeq _ _ (real_mult_const_proj _ _ _)), (qeqT_imp_qeq _ _ (real_opp_proj _ _)),
          (qeqT_imp_qeq _ _ (real_const_proj _ _)), ri_real_proj.
  reflexivity.
Qed.

Lemma lnr_hlcm_ge1 : forall n : nat, (1 <= hl_lcm_upto n)%nat.
Proof.
  induction n as [| m IH].
  - cbn. lia.
  - cbn [hl_lcm_upto].
    assert (Hdiv : Nat.divide (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)) (Datatypes.S m))
      by apply Nat.gcd_divide_r.
    destruct Hdiv as [k Hk].
    assert (Hk0 : (k <> 0)%nat).
    { intro Hk0. subst k. rewrite Nat.mul_0_l in Hk. discriminate. }
    assert (Hk1 : (1 <= k)%nat) by lia.
    assert (Hg0 : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m) <> 0)%nat).
    { intro Hg. rewrite Hg, Nat.mul_0_r in Hk. discriminate. }
    assert (Hgpos : (0 < Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat)
      by (apply Nat.neq_0_lt_0; exact Hg0).
    assert (Hgle : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m) <= Datatypes.S m)%nat).
    { pose proof (Nat.gcd_divide_r (hl_lcm_upto m) (Datatypes.S m)) as Hdv.
      destruct Hdv as [t Ht].
      assert (Ht0 : (0 < t)%nat).
      { apply Nat.neq_0_lt_0. intro Ht0. subst t.
        rewrite Nat.mul_0_l in Ht. discriminate. }
      assert (Hleg1 : (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)
                       <= t * Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat).
      { pose proof (Nat.mul_le_mono_r 1 t
                      (Nat.gcd (hl_lcm_upto m) (Datatypes.S m)) Ht0) as Hx.
        rewrite Nat.mul_1_l in Hx. exact Hx. }
      apply (Nat.le_trans _ (t * Nat.gcd (hl_lcm_upto m) (Datatypes.S m))).
      - exact Hleg1.
      - rewrite <- Ht. apply Nat.le_refl. }
    assert (Hd1 : (0 < Datatypes.S m / Nat.gcd (hl_lcm_upto m) (Datatypes.S m))%nat)
      by (apply Nat.div_str_pos; split; lia).
    unfold Nat.lcm. nia.
Qed.

Print Assumptions lnr_qmult_lt_compat_l.
Print Assumptions lnr_qhalf_lt.
Print Assumptions lnr_pterm_pos_Qle.
Print Assumptions lnr_qlt_transfer_l.
Print Assumptions lnr_qlt_transfer_r.
Print Assumptions lnr_qltT_transfer_l.
Print Assumptions lnr_qltT_transfer_r.
Print Assumptions lnr_qdiv_lt_intro_pre.
Print Assumptions lnr_q3divz_lt.
Print Assumptions lnr_qdivint_antitone.
Print Assumptions lnr_psum_head.
Print Assumptions lnr_psum_mono.
Print Assumptions lnr_q34_pow_le3.
Print Assumptions lnr_vanish.
Print Assumptions lnr_gap_modulus.
Print Assumptions lnr_gap_mod0.
Print Assumptions lnr_cauchy.
Print Assumptions lnr_Ireal_pos.
Print Assumptions lnr_identity_leg_transfer.
Print Assumptions lnr_lineL_proj.
Print Assumptions lnr_hlcm_ge1.

(* ============================================================ *)
(* Section A: the assembly itself. QeqT transfer micro-bridges, the integer    *)
(* supply pair projections, the two dockings, the head limbs, the refit        *)
(* supply interface, the chain-level core witness, the numeric anchors and     *)
(* the identity-leg hook.                                                     *)
(* ============================================================ *)

Lemma lna_qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply qeq_imp_qeqT.
  apply Qeq_sym. apply qeqT_imp_qeq. exact H.
Defined.

Lemma lna_qeqT_trans : forall a b c : Q, QeqT a b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c H1 H2. apply qeq_imp_qeqT.
  apply (Qeq_trans a b c).
  - apply qeqT_imp_qeq. exact H1.
  - apply qeqT_imp_qeq. exact H2.
Defined.

Definition lna_Amod (n : nat) : Z := projT1 (lni_supply_pair n).
Definition lna_Bmod (n : nat) : Z := projT1 (projT2 (lni_supply_pair n)).

Lemma lna_lA_z : forall n : nat, QeqT (lnr_lA n) ((lna_Amod n) # 1)%Q.
Proof.
  intro n. unfold lnr_lA, lna_Amod.
  exact (fst (projT2 (projT2 (lni_supply_pair n)))).
Defined.

Lemma lna_lB_z : forall n : nat, QeqT (lnr_lB n) ((lna_Bmod n) # 1)%Q.
Proof.
  intro n. unfold lnr_lB, lna_Bmod.
  exact (snd (projT2 (projT2 (lni_supply_pair n)))).
Defined.

Theorem lna_supply_pair_dock : forall n : nat,
  real_eq (lnr_lineL n) (ln2b_line lna_Amod lna_Bmod n).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k. apply qeq_imp_qeqT.
  rewrite lnr_lineL_proj, (qeqT_imp_qeq _ _ (ln2b_line_pt lna_Amod lna_Bmod n k)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lA_z n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lB_z n)).
  ring.
Defined.

Definition lna_Aface (n : nat) : Z := Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n).

Lemma lna_Aface_eq : forall n : nat, QeqT ((lna_Aface n) # 1)%Q (lnr_lA n).
Proof.
  intro n. apply qeq_imp_qeqT. unfold lna_Aface, lnr_lA.
  apply Qeq_sym. apply lnz_Qmul_nat.
Defined.

Theorem lna_supply_pair_dock_face : forall n : nat,
  real_eq (lnr_lineL n) (ln2b_line lna_Aface lna_Bmod n).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k. apply qeq_imp_qeqT.
  rewrite lnr_lineL_proj, (qeqT_imp_qeq _ _ (ln2b_line_pt lna_Aface lna_Bmod n k)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_lB_z n)).
  setoid_rewrite (qeqT_imp_qeq _ _ (lna_Aface_eq n)).
  ring.
Defined.

Theorem lna_ireal_tail_dock : forall (p M d : nat),
  (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
  QleT' (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q) (lnr_gapbound p M).
Proof.
  intros p M d Hp HM.
  assert (Hmono : Qle (lnr_psum p M) (lnr_psum p (M + d)))
    by (apply lnr_psum_mono; lia).
  assert (H0 : Qle 0 ((lnr_psum p (M + d) - lnr_psum p M)%Q)).
  { apply (Qle_trans 0%Q ((lnr_psum p M - lnr_psum p M)%Q)
                      ((lnr_psum p (M + d) - lnr_psum p M)%Q)).
    - apply lnz_Qeq_le. ring.
    - apply (Qplus_le_compat (lnr_psum p M) (lnr_psum p (M + d))
                             (- lnr_psum p M)%Q (- lnr_psum p M)%Q
                             Hmono (Qle_refl ((- lnr_psum p M)%Q))). }
  apply (lnt_leT'_eq_l (lnr_psum p (M + d) - lnr_psum p M)%Q
                       (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q)
                       (lnr_gapbound p M)).
  - apply Qeq_sym. exact (Qabs_pos (lnr_psum p (M + d) - lnr_psum p M)%Q H0).
  - apply lnr_gap_modulus; assumption.
Defined.

Theorem lna_ireal_tail_dock0 : forall (M d : nat),
  QleT' (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
        (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q).
Proof.
  intros M d.
  assert (Hmono : Qle (lnr_psum 0 M) (lnr_psum 0 (M + d)))
    by (apply lnr_psum_mono; lia).
  assert (H0 : Qle 0 ((lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)).
  { apply (Qle_trans 0%Q ((lnr_psum 0 M - lnr_psum 0 M)%Q)
                      ((lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)).
    - apply lnz_Qeq_le. ring.
    - apply (Qplus_le_compat (lnr_psum 0 M) (lnr_psum 0 (M + d))
                             (- lnr_psum 0 M)%Q (- lnr_psum 0 M)%Q
                             Hmono (Qle_refl ((- lnr_psum 0 M)%Q))). }
  apply (lnt_leT'_eq_l (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q
                       (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
                       (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)).
  - apply Qeq_sym. exact (Qabs_pos (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q H0).
  - apply lnr_gap_mod0.
Defined.

Definition lna_theta_mod : Q := (4 # 5)%Q.
Definition lna_clo_mod (n : nat) : Q :=
  (lne_B n / q_pow (2 # 1)%Q (Datatypes.S n))%Q.

Theorem lna_head_three_legs :
  And (QltT lna_theta_mod (1 # 1)%Q)
    (And (forall n : nat, QltT 0 (Qabs ((lna_Aface n) # 1)%Q))
         (forall n : nat, QltT 0 (lna_clo_mod n))).
Proof.
  split.
  - apply Qlt_to_QltT. unfold lna_theta_mod, Qlt. cbn [Qnum Qden]. lia.
  - split.
    + intro n. apply Qlt_to_QltT.
      assert (H1 : (1 <= hl_lcm_upto n)%nat) by apply lnr_hlcm_ge1.
      assert (H2 : (1 <= bk_Qn_qtilde n)%nat) by apply ri_qtilde_ge1.
      assert (H3 : (1 <= hl_lcm_upto n * bk_Qn_qtilde n)%nat) by nia.
      assert (Hx : (0 <= Z.of_nat (hl_lcm_upto n * bk_Qn_qtilde n))%Z)
        by apply Nat2Z.is_nonneg.
      assert (HQ : Qle 0 ((lna_Aface n) # 1)%Q).
      { unfold Qle. cbn [Qnum Qden]. unfold lna_Aface. lia. }
      rewrite (Qabs_pos ((lna_Aface n) # 1)%Q HQ).
      unfold Qlt, lna_Aface. cbn [Qnum Qden]. lia.
    + intro n. apply Qlt_to_QltT. unfold lna_clo_mod, Qdiv.
      apply Qmult_lt_0_compat.
      * exact (QltT_to_Qlt 0%Q (lne_B n) (lne_B_posT n)).
      * apply Qinv_lt_0_compat. apply lnt_pow2_pos.
Defined.

Definition lna_supply_rem' : Set :=
  sigT (fun B : nat -> Z =>
    And (ln2b_line_lower lna_Amod B lna_clo_mod)
        (ln2b_line_upper lna_Amod B lna_theta_mod)).

Theorem lna_supply_rem'_assemble :
  And (ln2b_line_lower lna_Amod lna_Bmod lna_clo_mod)
      (ln2b_line_upper lna_Amod lna_Bmod lna_theta_mod) ->
  lna_supply_rem'.
Proof.
  intros [Hlo Hup]. exists lna_Bmod. split; [exact Hlo | exact Hup].
Defined.

Theorem lna_supply_chain_core :
  sigT (fun A : nat -> Z =>
    sigT (fun B : nat -> Z =>
      And (forall n : nat, QeqT (lnr_lA n) ((A n) # 1)%Q)
        (And (forall n : nat, QeqT (lnr_lB n) ((B n) # 1)%Q)
          (And (forall n : nat, real_eq (lnr_lineL n) (ln2b_line A B n))
            (And (forall p : nat, real_lt real_zero (lnr_Ireal p))
              (And (forall (p M d : nat),
                      (1 <= p)%nat -> (2 * p <= M + 1)%nat ->
                      QleT' (Qabs (lnr_psum p (M + d) - lnr_psum p M)%Q)
                            (lnr_gapbound p M))
                   (forall (M d : nat),
                      QleT' (Qabs (lnr_psum 0 (M + d) - lnr_psum 0 M)%Q)
                            (((4 # 1)%Q * lnt_pterm 0 (Datatypes.S M))%Q)))))))).
Proof.
  exists lna_Amod. exists lna_Bmod. split.
  - apply lna_lA_z.
  - split.
    + apply lna_lB_z.
    + split.
      * intro n. apply lna_supply_pair_dock.
      * split.
        -- intro p. apply lnr_Ireal_pos.
        -- split.
           ++ intros p M d Hp HM. apply lna_ireal_tail_dock; assumption.
           ++ intros M d. apply lna_ireal_tail_dock0.
Defined.

Theorem lna_A1_anchor : QeqT (3 # 1)%Q ((lna_Amod 1) # 1)%Q.
Proof.
  apply lna_qeqT_trans with (b := lnr_lA 1).
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - apply lna_lA_z.
Defined.

Theorem lna_B1_anchor : QeqT (4 # 2)%Q ((lna_Bmod 1) # 1)%Q.
Proof.
  apply lna_qeqT_trans with (b := lnr_lB 1).
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - apply lna_lB_z.
Defined.

Theorem lna_tail1_anchor :
  QleT' (Qabs (lnr_psum 1 (1 + 1) - lnr_psum 1 1)%Q) (lnr_gapbound 1 1).
Proof.
  apply lna_ireal_tail_dock; lia.
Defined.

Theorem lna_leg_transfer_hook : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnr_Ireal p)) ->
  ri_identity_leg lnr_Ireal -> ri_identity_leg I.
Proof. exact lnr_identity_leg_transfer. Defined.

Print Assumptions lna_qeqT_sym.
Print Assumptions lna_qeqT_trans.
Print Assumptions lna_lA_z.
Print Assumptions lna_lB_z.
Print Assumptions lna_supply_pair_dock.
Print Assumptions lna_Aface_eq.
Print Assumptions lna_supply_pair_dock_face.
Print Assumptions lna_ireal_tail_dock.
Print Assumptions lna_ireal_tail_dock0.
Print Assumptions lna_head_three_legs.
Print Assumptions lna_supply_rem'.
Print Assumptions lna_supply_rem'_assemble.
Print Assumptions lna_supply_chain_core.
Print Assumptions lna_A1_anchor.
Print Assumptions lna_B1_anchor.
Print Assumptions lna_tail1_anchor.
Print Assumptions lna_leg_transfer_hook.

(* ============================================================ *)
(* Extractable closure (Set-layer witness faces, plain definitions only).      *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction lna_Amod lna_Bmod lna_Aface lna_theta_mod lna_clo_mod
  lnt_pterm lnr_psum lnr_gapbound lnr_lA lnr_lB lni_bvpt.
