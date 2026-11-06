(* ConstructiveWorld-Set -- integrality closure of the Beukers/Hermite Pade [n/n] approximants to ln 2. *)

(** * Ln2Integrality: Pade integrality closure for the ln 2 irrationality proof.

    Mission.  For the Beukers/Hermite Pade [n/n] forms [P_n] and [Q_n] to ln 2
      with common denominator [D_n], the nat carrier [pi_ptilde] realizes the
      integer p~_n with [2^n * D_n * P_n(1/2) == Q#p~_n] ([pi_Pn_int]), the
      denominator obeys [q~_n <= (n+1) * 8^n] ([pi_Qn_le_8pow]), and the
      fraction closes as [x'_n == p~_n / (2 * D_n * q~_n)] with an explicitly
      constructed positive denominator ([pi_x_n_frac]) and in the weak
      positive-denominator sigT form ([pi_den_divide]); the Pascal bridge
      [pi_bkC_hl] and the harmonic bridge [pi_hsum_spec] support the argument.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Arith.Arith],
      [Lia], [Lists.List].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [BeukersLists], [HansonLcm] of this development.

    References.  This development, Ln2Integrality.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  Per-item carrier face table below (before section A).  Main
      statements are [Set]-carried: [pi_Pn_int]/[pi_den_divide] ([sigT] witnesses
      over [Z]/[positive]), [pi_x_n_frac] ([QeqT]), [pi_Qn_le_8pow] ([QleT']);
      both carriers are declared [: Set] in S02_CauchyComplete; [pi_hsum]/
      [pi_ptilde] are [nat]-valued data; support lemmas are [Prop]-face
      ([le]/[eq]/[Qeq]) for reasoning only.  Extraction [Obj.magic] = 0, no [Set]-carried name erased; coqchk reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" Ln2Integrality.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Lists.List.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import BeukersLists HansonLcm.

Open Scope nat_scope.

(* Carrier face table (per-item disclosure; every named statement ascribed
   under Rocq 9.3.0): [Set]-carried statements and data --
     pi_Pn_int      (Theorem)    sigT witness in Z, equality via QeqT (: Set)
     pi_Qn_le_8pow  (Theorem)    order via QleT' (: Set)
     pi_x_n_frac    (Theorem)    equality via QeqT (: Set)
     pi_den_divide  (Theorem)    sigT witness in positive, via QeqT (: Set)
     pi_hsum        (Fixpoint)   nat-valued data
     pi_ptilde      (Definition) nat-valued data
   [Prop]-face support lemmas (statements in [le]/[eq]/[Qeq]; used inside
   proofs for reasoning only, no extraction duty) --
     pi_pow3_ge1 pi_pow4b pi_pow8 pi_psd_const pi_bkC_hl pi_Qden_cancel
     pi_Qneq0_Zpos pi_Qneq0_nat pi_Qmul_cancel_r_to pi_Qdiv_eq_intro
     pi_Qmul_inv_r_eq pi_div_Qeq pi_hsum_spec pi_psQ_ext pi_psQ_mul
     pi_coeff_Zeq pi_Pn_eval_eq pi_Pn_half pi_lcm_pos pi_lcm_upto_pos
     pi_qtilde_pos pi_Qn_nz pi_x_cross. *)

(* ============================================================ *)
(* section A. Elementary lemmas on powers and positivity over nat. *)
(* ============================================================ *)

Lemma pi_pow3_ge1 : forall n : nat, 1 <= 3 ^ n.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pi_pow4b : forall n : nat, 4 ^ n = 2 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

Lemma pi_pow8 : forall n : nat, 8 ^ n = 4 ^ n * 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite !Nat.pow_succ_r'. rewrite IH. ring.
Qed.

(* closed form for constant coefficients in bk_psd: the sum of c * 2^(N-1-k) over k < N equals c * (2^N - 1). *)
Lemma pi_psd_const : forall (N c : nat),
  bk_psd (fun _ : nat => c) N = c * (2 ^ N - 1).
Proof.
  induction N as [| N IH]; intro c.
  - cbn [bk_psd Nat.pow]. lia.
  - cbn [bk_psd]. rewrite IH. rewrite Nat.pow_succ_r'.
    pose proof (hl_le_t_to_le 1 (2 ^ N) (hl_pow2_ge1 N)). nia.
Qed.

(* ============================================================ *)
(* section B. The double Pascal bridge [pi_bkC_hl] between bkC and hl_binom. *)
(* ============================================================ *)

Lemma pi_bkC_hl : forall n k : nat, bkC n k = hl_binom n k.
Proof.
  induction n as [| n IH]; intro k.
  - destruct k as [| k'].
    + reflexivity.
    + reflexivity.
  - destruct k as [| k'].
    + reflexivity.
    + cbn [bkC]. rewrite (IH k'). rewrite (IH (Datatypes.S k')).
      symmetry. exact (hl_id_eq nat _ _ (hl_binom_S n k')).
Qed.

(* ============================================================ *)
(* section C. Multiplication and division lemmas over Q, field laws with the nonzero premises stated explicitly. *)
(* ============================================================ *)

(* a fraction with positive denominator times its denominator reduces to the numerator over one; the denominators merge without unfolding the Qinv component. *)
Lemma pi_Qden_cancel : forall (u : Z) (p : positive),
  ((u # p) * ((Z.pos p) # 1))%Q == (u # 1)%Q.
Proof.
  intros u p. unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Pos.mul_1_r. ring.
Qed.

Lemma pi_Qneq0_Zpos : forall p : positive, ~ (((Z.pos p) # 1) == 0)%Q.
Proof.
  intros p Hc. unfold Qeq in Hc. vm_compute in Hc. discriminate Hc.
Qed.

Lemma pi_Qneq0_nat : forall m : nat, 1 <= m -> ~ ((Z.of_nat m # 1) == 0)%Q.
Proof.
  intros m Hm Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc. lia.
Qed.

(* right cancellation over Q: from c nonzero and a * c == b * c conclude a == b, through the inverse supplied by Qmult_inv_r. *)
Lemma pi_Qmul_cancel_r_to : forall a b c : Q,
  ~ (c == 0)%Q -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc H.
  assert (Hc1 : (c * (/ c))%Q == 1%Q) by (apply Qmult_inv_r; exact Hc).
  transitivity (((a * c) * (/ c)))%Q.
  - rewrite <- Qmult_assoc, Hc1. symmetry. apply Qmult_1_r.
  - rewrite H. rewrite <- Qmult_assoc, Hc1. apply Qmult_1_r.
Qed.

(* one-sided introduction of a division equation: for y nonzero, x == b * y gives x / y == b. *)
Lemma pi_Qdiv_eq_intro : forall x y b : Q,
  ~ (y == 0)%Q -> x == b * y -> x / y == b.
Proof.
  intros x y b Hy Hxy. unfold Qdiv. rewrite Hxy.
  assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
  rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* cross equivalence for division over Q: for nonzero y, x * (/ y) == z holds exactly when x == z * y. *)
Lemma pi_Qmul_inv_r_eq : forall x y z : Q,
  ~ (y == 0)%Q -> ((x * (/ y)) == z <-> x == z * y).
Proof.
  intros x y z Hy. split; intro H.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    transitivity (((x * (/ y)) * y))%Q.
    + rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ y) y). rewrite Hy1.
      symmetry. apply Qmult_1_r.
    + rewrite H. reflexivity.
  - assert (Hy1 : (y * (/ y))%Q == 1%Q) by (apply Qmult_inv_r; exact Hy).
    rewrite H. rewrite <- Qmult_assoc, Hy1. apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* section D. Divisibility-to-quotient transport and the master bridge integralizing the harmonic sums. *)
(* ============================================================ *)

(* if j divides D, then (D # 1) * (1 / (j # 1)) == (D / j) # 1, with the quotient kept exact by Nat.div_mul. *)
Lemma pi_div_Qeq : forall (D j : nat), 1 <= j -> Nat.divide j D ->
  ((Z.of_nat D # 1) * ((1 # 1) / (Z.of_nat j # 1)))%Q
  == (Z.of_nat (D / j) # 1)%Q.
Proof.
  intros D j Hj Hd. destruct Hd as [c Hc].
  assert (Hj0 : ~ ((Z.of_nat j # 1) == 0)%Q) by (apply pi_Qneq0_nat; exact Hj).
  assert (Hdq : D / j = c).
  { rewrite Hc. apply Nat.div_mul. lia. }
  rewrite Hdq. unfold Qdiv.
  transitivity ((((Z.of_nat D # 1) * (1 # 1)) * (/ (Z.of_nat j # 1))))%Q.
  - ring.
  - apply (proj2 (pi_Qmul_inv_r_eq _ _ _ Hj0)).
    rewrite Qmult_1_r.
    rewrite (qeqT_imp_qeq _ _ (bk_Qmul_nat c j)).
    rewrite Hc. reflexivity.
Qed.

(* the integral harmonic carrier: pi_hsum D k accumulates the quotients D / j for j from 1 to k, at fixed D. *)
Fixpoint pi_hsum (D k : nat) : nat :=
  match k with
  | 0 => 0
  | Datatypes.S m => pi_hsum D m + D / Datatypes.S m
  end.

(* the master harmonic bridge: (D_n # 1) * H_k == (sum of D_n / j for j <= k) # 1, by induction on k, using that every j <= k divides D_n. *)
Lemma pi_hsum_spec : forall (n k : nat), k <= n ->
  ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k. induction k as [| k IH]; intro Hk.
  - cbn [bk_H pi_hsum]. ring.
  - assert (Hle : k <= n) by lia.
    specialize (IH Hle).
    cbn [bk_H pi_hsum].
    rewrite Qmult_plus_distr_r.
    rewrite IH.
    assert (H1 : 1 <= Datatypes.S k) by lia.
    assert (Hd := hl_lcm_divide_all n (Datatypes.S k) H1 Hk).
    assert (Hdv := pi_div_Qeq (hl_lcm_upto n) (Datatypes.S k) H1 Hd).
    rewrite Hdv.
    apply qeqT_imp_qeq. apply bk_Qadd_nat.
Qed.

(* ============================================================ *)
(* section E. Pointwise extensionality and constant extraction for the bk_psQ sums. *)
(* ============================================================ *)

Lemma pi_psQ_ext : forall (N : nat) (f g : nat -> Q) (z : Q),
  (forall k : nat, k < N -> f k == g k) -> bk_psQ f N z == bk_psQ g N z.
Proof.
  induction N as [| N IH]; intros f g z H.
  - reflexivity.
  - cbn [bk_psQ].
    rewrite (IH f g z) by (intros k Hk; apply H; lia).
    rewrite (H N) by lia.
    reflexivity.
Qed.

Lemma pi_psQ_mul : forall (N : nat) (c : Q) (f : nat -> Q) (z : Q),
  bk_psQ (fun k => (c * f k)%Q) N z == (c * bk_psQ f N z)%Q.
Proof.
  induction N as [| N IH]; intros c f z.
  - cbn [bk_psQ]. ring.
  - cbn [bk_psQ]. rewrite IH. ring.
Qed.

(* ============================================================ *)
(* section F. The master integrality statement for p~_n, with coefficient C(n,k)^2 * D_n. *)
(* ============================================================ *)

(* coefficient integrality pointwise: (C(n,k)^2 * D_n # 1) * H_k == (C(n,k)^2 * S_k # 1), where S_k := pi_hsum D_n k. *)
Lemma pi_coeff_Zeq : forall (n k : nat), k <= n ->
  ((Z.of_nat (bkC n k * bkC n k * hl_lcm_upto n) # 1) * bk_H k)%Q
  == (Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1)%Q.
Proof.
  intros n k Hk.
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat (bkC n k * bkC n k) (hl_lcm_upto n))).
  transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                  * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
  - ring.
  - rewrite (pi_hsum_spec n k Hk). apply qeqT_imp_qeq. apply bk_Qmul_nat.
Qed.

(* the carrier of the master statement: p~_n := the sum of C(n,k)^2 * S_k over k <= n, with S_k := pi_hsum D_n k. *)
Definition pi_ptilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k)
         (Datatypes.S n).

(* the Qeq form of bk_Pn_eval, obtained from the Set-level transport qeqT_imp_qeq, for rewriting against == goals. *)
Lemma pi_Pn_eval_eq : forall (n : nat) (z : Q),
  bkQ (bk_Pn_list n) z
  == bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
          (Datatypes.S n) z.
Proof.
  intros n z. exact (qeqT_imp_qeq _ _ (bk_Pn_eval n z)).
Qed.

(* closed value at the half-integer point: (D_n # 1) * (2^n * P_n(1/2)) == (p~_n # 1), with the witness p~_n carried as a nat. *)
Lemma pi_Pn_half : forall n : nat,
  ((Z.of_nat (hl_lcm_upto n) # 1)
     * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q
  == (Z.of_nat (pi_ptilde n) # 1)%Q.
Proof.
  intro n. unfold pi_ptilde.
  rewrite (pi_Pn_eval_eq n (1 # 2)%Q).
  assert (Hmul := pi_psQ_mul (Datatypes.S n)
                    (Z.of_nat (hl_lcm_upto n) # 1)%Q
                    (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
                    (1 # 2)%Q).
  transitivity ((q_pow (2 # 1)%Q n
    * ((Z.of_nat (hl_lcm_upto n) # 1)
         * bk_psQ (fun k : nat => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) (1 # 2)%Q))%Q).
  - ring.
  - rewrite <- Hmul.
    assert (Hpt : forall k : nat, k < Datatypes.S n ->
        (((Z.of_nat (hl_lcm_upto n) # 1)
            * ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k))%Q)
        == ((Z.of_nat (bkC n k * bkC n k * pi_hsum (hl_lcm_upto n) k) # 1))%Q).
    { intro k. intro Hk. assert (Hle : k <= n) by lia.
      transitivity ((Z.of_nat (bkC n k * bkC n k) # 1)
                      * ((Z.of_nat (hl_lcm_upto n) # 1) * bk_H k))%Q.
      - ring.
      - rewrite (pi_hsum_spec n k Hle). apply qeqT_imp_qeq. apply bk_Qmul_nat. }
    rewrite (pi_psQ_ext (Datatypes.S n) _ _ _ Hpt).
    apply qeqT_imp_qeq. apply bk_half_psd.
Qed.

(* the master statement: a sigT witness that p~_n is an integer, carried in Set. *)

Theorem pi_Pn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT (q_pow (2 # 1)%Q n
            * ((Z.of_nat (hl_lcm_upto n) # 1) * bkQ (bk_Pn_list n) (1 # 2)%Q)%Q)
         ((z # 1)%Q)).
Proof.
  intro n. exists (Z.of_nat (pi_ptilde n)). apply qeq_imp_qeqT.
  transitivity ((Z.of_nat (hl_lcm_upto n) # 1)
                  * (q_pow (2 # 1)%Q n * bkQ (bk_Pn_list n) (1 # 2)%Q))%Q.
  - ring.
  - apply pi_Pn_half.
Qed.

(* ============================================================ *)
(* section G. The denominator bound q~_n <= (n+1) * 8^n, carried by QleT' in Set. *)
(* ============================================================ *)

Theorem pi_Qn_le_8pow : forall n : nat,
  QleT' ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
        ((Z.of_nat (Datatypes.S n * 8 ^ n) # 1)%Q).
Proof.
  intro n. apply bk_Qle_nat. apply NatLe_lift.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat, k < Datatypes.S n ->
      bkC n k * bkC n k <= 4 ^ n).
  { intro k. intro Hk.
    assert (Hb := hl_le_t_to_le (hl_binom n k) (2 ^ n)
                    (hl_binom_le_pow2 n k)).
    rewrite <- (pi_bkC_hl n k) in Hb.
    rewrite (pi_pow4b n).
    nia. }
  assert (Hmono := NatLe_drop _ _
                     (bk_psd_mono (Datatypes.S n)
                        (fun k : nat => bkC n k * bkC n k)
                        (fun _ : nat => 4 ^ n)
                        (fun k Hk => NatLe_lift _ _ (Hpt k (NatLe_drop _ _ Hk))))).
  rewrite pi_psd_const in Hmono.
  rewrite Nat.pow_succ_r' in Hmono.
  destruct n as [| n'].
  - cbn [bk_psd bkC Nat.pow] in *. lia.
  - assert (Hs1 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)
                  <= 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n'))
      by (apply Nat.mul_le_mono_l; lia).
    assert (Hs2 : 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')
                  = 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')) by ring.
    assert (Hs3 : 2 * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')
                  <= Datatypes.S (Datatypes.S n') * (4 ^ Datatypes.S n' * 2 ^ Datatypes.S n')).
    { apply Nat.mul_le_mono_r. lia. }
    rewrite (pi_pow8 (Datatypes.S n')).
    apply Nat.le_trans with
      (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n' - 1)).
    + exact Hmono.
    + apply Nat.le_trans with
        (m := 4 ^ Datatypes.S n' * (2 * 2 ^ Datatypes.S n')).
      * exact Hs1.
      * rewrite Hs2. exact Hs3.
Qed.

(* ============================================================ *)
(* section H. Denominator closure for x'_n and the weak positive-denominator sigT form. *)
(* ============================================================ *)

Lemma pi_lcm_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= Nat.lcm a b.
Proof.
  intros a b Ha Hb. unfold Nat.lcm.
  destruct (Nat.gcd a b) as [| g] eqn:Eg.
  - exfalso.
    destruct (Nat.gcd_divide_r a b) as [q Hq].
    rewrite Eg, Nat.mul_0_r in Hq. lia.
  - assert (Hbg : 0 < b / Datatypes.S g).
    { apply Nat.div_str_pos.
      destruct (Nat.gcd_divide_r a b) as [q Hq]. rewrite Eg in Hq.
      destruct q as [| q'].
      - lia.
      - split.
        + lia.
        + assert (Hg1 : Datatypes.S g * 1 <= Datatypes.S g * Datatypes.S q')
            by (apply Nat.mul_le_mono_l; lia).
          rewrite Nat.mul_1_r in Hg1.
          rewrite Hq, Nat.mul_comm. exact Hg1. }
    nia.
Qed.

Lemma pi_lcm_upto_pos : forall n : nat, 1 <= hl_lcm_upto n.
Proof.
  induction n as [| n IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto]. apply pi_lcm_pos.
    + exact IH.
    + lia.
Qed.

Lemma pi_qtilde_pos : forall n : nat, 1 <= bk_Qn_qtilde n.
Proof.
  intro n. pose proof (NatLe_drop (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)).
  pose proof (pi_pow3_ge1 n). lia.
Qed.

(* twice the denominator polynomial is nonzero at the point 1/2, since q~_n >= 3^n > 0. *)
Lemma pi_Qn_nz : forall n : nat,
  ~ (((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q) == 0)%Q.
Proof.
  intro n. intro H0.
  assert (HQ : bkQ (bk_Qn_list n) (1 # 2)%Q == 0%Q).
  { apply (pi_Qmul_cancel_r_to (bkQ (bk_Qn_list n) (1 # 2)%Q) 0%Q (2 # 1)%Q).
    - apply pi_Qneq0_Zpos.
    - rewrite (Qmult_comm (bkQ (bk_Qn_list n) (1 # 2)%Q) (2 # 1)%Q).
      rewrite Qmult_0_l. exact H0. }
  assert (Hh := qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite HQ in Hh. rewrite Qmult_0_r in Hh.
  pose proof (NatLe_drop (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)).
  unfold Qeq in Hh. cbn [Qnum Qden] in Hh.
  rewrite !Z.mul_1_r in Hh.
  replace 0%Z with (Z.of_nat 0) in Hh by reflexivity.
  apply Znat.Nat2Z.inj in Hh.
  pose proof (pi_pow3_ge1 n).
  lia.
Qed.

(* the cross identity: P_n(1/2) * (2 * D_n * q~_n) == p~_n * (2 * Q_n(1/2)), pure ring reasoning over Q. *)
Lemma pi_x_cross : forall n : nat,
  (bkQ (bk_Pn_list n) (1 # 2)%Q
     * (Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n) # 1))%Q
  == ((Z.of_nat (pi_ptilde n) # 1)
        * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
Proof.
  intro n.
  replace (2 # 1)%Q with ((Z.of_nat 2 # 1)%Q) by reflexivity.
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat (2 * hl_lcm_upto n) (bk_Qn_qtilde n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qmul_nat 2 (hl_lcm_upto n))).
  rewrite <- (qeqT_imp_qeq _ _ (bk_Qn_half_closed n)).
  rewrite <- (pi_Pn_half n).
  ring.
Qed.

(* the master denominator closure: x'_n == p~_n / (2 * D_n * q~_n), with the
   denominator constructed explicitly.  The positive denominator is
   Pos.of_succ_nat (Nat.pred M), whose value is exactly M by the defining
   conversions. *)
Theorem pi_x_n_frac : forall n : nat,
  QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
          / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
       ((Z.of_nat (pi_ptilde n)
           # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))%Q).
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hm1 : 1 <= 2 * hl_lcm_upto n * bk_Qn_qtilde n)
    by (pose proof (pi_lcm_upto_pos n); pose proof (pi_qtilde_pos n); lia).
  assert (Hpm : Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
              = Z.of_nat (2 * hl_lcm_upto n * bk_Qn_qtilde n)).
  { assert (Hs : Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))
               = 2 * hl_lcm_upto n * bk_Qn_qtilde n) by lia.
    transitivity (Z.of_nat (Datatypes.S (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
    - reflexivity.
    - rewrite Hs. reflexivity. }
  apply pi_Qdiv_eq_intro.
  - apply pi_Qn_nz.
  - apply (pi_Qmul_cancel_r_to (bkQ (bk_Pn_list n) (1 # 2)%Q)
             (((Z.of_nat (pi_ptilde n)
                  # Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))
                 * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q)
             ((Z.pos (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))) # 1)%Q)).
    + apply pi_Qneq0_Zpos.
    + rewrite Hpm.
      transitivity ((Z.of_nat (pi_ptilde n) # 1)
                      * ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q.
      * exact (pi_x_cross n).
      * rewrite <- (pi_Qden_cancel (Z.of_nat (pi_ptilde n))
                          (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n)))).
        rewrite Hpm.
        ring.
Qed.

(* the weak form: for some positive denominator p, x'_n == p~_n / p, recorded as an informative sigT witness. *)
Theorem pi_den_divide : forall n : nat,
  sigT (fun p : positive =>
    QeqT (bkQ (bk_Pn_list n) (1 # 2)%Q
            / ((2 # 1)%Q * bkQ (bk_Qn_list n) (1 # 2)%Q))%Q
         ((Z.of_nat (pi_ptilde n) # p)%Q)).
Proof.
  intro n.
  exists (Pos.of_succ_nat (Nat.pred (2 * hl_lcm_upto n * bk_Qn_qtilde n))).
  apply pi_x_n_frac.
Qed.

(* ============================================================ *)
(* assumption audit: Print Assumptions at the main exit points. *)
(* ============================================================ *)

Print Assumptions pi_bkC_hl.
Print Assumptions pi_div_Qeq.
Print Assumptions pi_hsum_spec.
Print Assumptions pi_psQ_ext.
Print Assumptions pi_Pn_int.
Print Assumptions pi_Qn_le_8pow.
Print Assumptions pi_x_n_frac.
Print Assumptions pi_den_divide.
