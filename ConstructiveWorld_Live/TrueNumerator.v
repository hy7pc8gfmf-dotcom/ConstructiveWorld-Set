(* ============================================================ *)
(* TrueNumerator.v                                                                               *)
(* Mission. Closed form and identity of the Beukers true-numerator family: P*_n(1/2) = r_n/2^{2n} *)
(* with r_n == 2^{n+1}*p_n (p_n the Laurent closed form of bv_p), i.e. P*_n(1/2) == p_n*2^{1-n} == *)
(* tn_Ps_half n; the general identity tn_x_eq_bv_x: x'_n == tn_x n == p_n/q~_n == bv_x n. Main   *)
(* surface: definitions tn_r/tn_Ps_half/tn_x/tn_Qhalf; the family list tn_Pn_list with its       *)
(* length/nth evaluation surface; the identity bridge tn_x_eq_bv_x (pure Set statement); Q-layer *)
(* support lemmas tn_qpow2_ne/tn_qpow2_inv/tn_Qinv_cong/tn_sh_one/tn_core_eq.                    *)
(* Dependencies. Stdlib QArith/QArith Lists/List Arith/Arith ZArith/ZArith Lia; S01_BaseRing     *)
(* S02_CauchyComplete S03_QExp S07_RealSetoidExpLog; BeukersLists BeukersVariant (transitively   *)
(* PolyIntegral PadeErrorIntegral PintMono).                                                     *)
(* References. Numerical anchors (n = 0..5): p = 0, 2, 9, 131/3, 445/2, 34997/30; q~ = 1, 3, 13, *)
(* 63, 321, 1683; x' = 0, 2/3, 9/13, 131/189, 445/642, 34997/50490; r = 0, 8, 72, 2096/3, 7120,  *)
(* 1119904/15; P*_n(1/2) = 0, 2, 9/2, 131/12, 445/16, 34997/480. Sanity notes: the self-consistent *)
(* shape of P*_n(1/2) is r_n/2^{2n} (8/4 = 2, 72/16 = 9/2); integrality: r_0, r_1, r_2, r_4 are  *)
(* integers while r_3 = 2096/3 and r_5 = 1119904/15 are not (odd prime factors in the denominator), *)
(* so the true-numerator family is essentially rational from n = 3 on -- no power-of-2           *)
(* normalization recovers it. Negative control: the three harmonic-type candidates (sum C(n,k)^2 *)
(* (H_k + H_{n-k}) (1/2)^k, sum C(n,k)^2 (H_{n+k} - H_k) (1/2)^k, sum C(n,k)^2 H_k (1/2)^k) all  *)
(* mismatch from n = 1 on (witnesses tn_harm1_anchor, tn_harm2_anchor); root cause: the true     *)
(* numerator carries a power-of-2 tail term (Laurent 2^{j-n} - 1 structure), not a purely harmonic *)
(* sum.                                                                                          *)
(* Constructivity. All proofs end in Qed with no proof holes on the statement surface; the main  *)
(* item and the anchor group are zero-premise QeqT (pure Set); the nth evaluation surface carries *)
(* the nat premise k <= N; the support lemmas serve reasoning only; extractable; a Print         *)
(* Assumptions audit at end of file re-checks closure.                                           *)
(* Build. Rocq 9.1: rocq c -native-compiler no -q -Q . "" TrueNumerator.v (flat vo-tree namespace); *)
(* trust cache primed first; tiered execution under the temperature-guard wrapper.               *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import BeukersLists BeukersVariant.

Open Scope nat_scope.

(* ============================================================ *)
(* Sec.A True-numerator family definition surface (r_n == 2^{n+1} * p_n conversion) *)
(* ============================================================ *)

(* Q_n(1/2) (library surface: Horner evaluation of the BeukersLists coefficient list) *)
Definition tn_Qhalf (n : nat) : Q := bkQ (bk_Qn_list n) (1 # 2)%Q.

(* tn_r: the r family, r_n == 2^{n+1} * p_n (cross-variant conversion) *)
Definition tn_r (n : nat) : Q := (q_pow (2 # 1)%Q (Datatypes.S n) * bv_p n)%Q.

(* The true numerator evaluated at 1/2: P*_n(1/2) = r_n/2^{2n} = p_n * 2^{1-n},
   written as * (1/2)^{n+n} to avoid Qinv; the definition surface is purely multiplicative *)
Definition tn_Ps_half (n : nat) : Q := (tn_r n * q_pow (1 # 2)%Q (n + n))%Q.

(* tn_x: the constrained shape x'_n = P*_n(1/2) / (2 * Q_n(1/2)) *)
Definition tn_x (n : nat) : Q := (tn_Ps_half n / (2 * tn_Qhalf n))%Q.

(* True-numerator family list: [P*_0(1/2); ...; P*_N(1/2)] (list Fixpoint) *)
Fixpoint tn_Pn_list (N : nat) : list Q :=
  match N with
  | 0 => (tn_Ps_half 0)%Q :: nil
  | Datatypes.S m => tn_Pn_list m ++ ((tn_Ps_half (Datatypes.S m))%Q :: nil)
  end.

(* ============================================================ *)
(* Sec.B Q-layer support lemmas (Prop surface, serving reasoning only) *)
(* ============================================================ *)

(* The nat power of 2 is nonzero (the nonzero premise for Qmult_inv_r) *)
Lemma tn_qpow2_ne : forall k : nat, Not (QeqT (q_pow (2 # 1)%Q k) 0%Q).
Proof.
  induction k as [| k IH]; intro H.
  - unfold QeqT in H. destruct (Qcompare (q_pow (2 # 1)%Q 0) 0%Q) eqn:E.
    + apply (False_rect Empty_set).
      assert (Heq : q_pow (2 # 1)%Q 0 == 0%Q)
        by (apply (proj2 (Qeq_alt _ _)); exact E).
      unfold Qeq in Heq. cbn [q_pow Qnum Qden Qmult] in Heq. lia.
    + inversion H.
    + inversion H.
  - pose proof (qeqT_imp_qeq _ _ H) as H'.
    cbn [q_pow] in H'.
    assert (Hc : False).
    { destruct (Qmult_integral _ _ H') as [H1 | H1].
      - unfold Qeq in H1. cbn [Qnum Qden Qmult] in H1. lia.
      - destruct (IH (qeq_imp_qeqT _ _ H1)). }
    exact (False_rect Empty_set Hc).
Qed.

(* tn_sh_one: q_pow 2 k * q_pow (1/2) k == 1 (2 and 1/2 are mutual inverses) *)
Lemma tn_sh_one : forall k : nat, QeqT (q_pow (2 # 1)%Q k * q_pow (1 # 2)%Q k) 1%Q.
Proof.
  intro k. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (bk_q_pow_mul (2 # 1)%Q (1 # 2)%Q k)).
  assert (H21 : ((2 # 1) * (1 # 2))%Q == (1 # 1)%Q) by reflexivity.
  rewrite H21. apply qeqT_imp_qeq. apply bk_q_pow_one.
Qed.

(* tn_qpow2_inv: /2^k == (1/2)^k (zero premises, via Qinv_mult_distr) *)
Lemma tn_qpow2_inv : forall k : nat, QeqT (Qinv (q_pow (2 # 1)%Q k)) (q_pow (1 # 2)%Q k).
Proof.
  intro k. apply qeq_imp_qeqT.
  assert (HA := tn_sh_one k).
  rewrite <- (Qmult_1_r (Qinv (q_pow (2 # 1)%Q k))).
  rewrite <- (qeqT_imp_qeq _ _ HA).
  rewrite Qmult_assoc.
  rewrite (Qmult_comm (Qinv (q_pow (2 # 1)%Q k)) (q_pow (2 # 1)%Q k)).
  rewrite (Qmult_inv_r (q_pow (2 # 1)%Q k)
             (fun He => match tn_qpow2_ne k (qeq_imp_qeqT _ _ He) with end)).
  apply Qmult_1_l.
Qed.

(* tn_half_inv: /2 == 1/2 *)
Lemma tn_half_inv : QeqT (Qinv (2 # 1)%Q) (1 # 2)%Q.
Proof. exact (qeq_imp_qeqT _ _ (Qeq_refl (1 # 2)%Q)). Qed.

(* Qeq setoid preservation: x == y implies /y == /x (Qeq pointwise equality, zero premises;
   direction taken as y==x in, x==y out, matching the original direction of bk_Qn_half_closed) *)
Lemma tn_Qinv_cong : forall x y : Q, QeqT x y -> QeqT (Qinv y) (Qinv x).
Proof. intros x y H. apply qeq_imp_qeqT. rewrite <- (qeqT_imp_qeq _ _ H). reflexivity. Qed.

(* tn_core_eq: given s * h == 1, (2*s*p*h*h) * ((1/2) * /E) == p * (h * /E)
   -- the residual algebra of tn_x_eq_bv_x (ring rearrangement + two rewrite steps) *)
Lemma tn_core_eq : forall p E s h : Q,
  QeqT (s * h) 1%Q ->
  QeqT ((2 * s * p * (h * h)) * ((1 # 2)%Q * Qinv E))%Q (p * (h * Qinv E)).
Proof.
  intros p E s h Hsh. apply qeq_imp_qeqT.
  (* s*h^2 -> (s*h)*h : pure rearrangement *)
  transitivity ((2 * (s * h) * p * h) * ((1 # 2)%Q * Qinv E))%Q.
  - ring.
  - rewrite (qeqT_imp_qeq _ _ Hsh).
    (* first fuse 2 * (1/2) == 1 *)
    transitivity (2 * (1 # 2)%Q * p * h * Qinv E)%Q.
    + ring.
    + assert (H21 : ((2 # 1) * (1 # 2))%Q == (1 # 1)%Q) by reflexivity.
      rewrite H21. ring.
Qed.

(* ============================================================ *)
(* Sec.C General identity bridge: tn_x_eq_bv_x (pure Set statement, zero premises) *)
(*   tn_x n == bv_x n, i.e. x'_n = P*_n(1/2) / (2 * Q_n(1/2)) == p_n/q~_n *)
(* ============================================================ *)

Theorem tn_x_eq_bv_x : forall n : nat, QeqT (tn_x n) (bv_x n).
Proof.
  intro n. apply qeq_imp_qeqT.
  unfold tn_x, tn_Ps_half, tn_r, tn_Qhalf, bv_x. unfold Qdiv.
  (* exponent normalization: 2^{S n} -> 2 * 2^n; (1/2)^{n+n} -> (1/2)^n * (1/2)^n *)
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q n)).
  rewrite (qeqT_imp_qeq _ _ (q_pow_add (1 # 2)%Q n n)).
  (* Qinv distributive splitting (stdlib zero-premise distributivity Qinv_mult_distr + tn reshaping) *)
  rewrite (Qinv_mult_distr (2 # 1)%Q (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  rewrite (qeqT_imp_qeq _ _ tn_half_inv).
  rewrite (qeqT_imp_qeq _ _
             (tn_Qinv_cong ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q)
                ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q)
                (bk_Qn_half_closed n))).
  rewrite (Qinv_mult_distr (q_pow (2 # 1)%Q n) (bkQ (bk_Qn_list n) (1 # 2)%Q)).
  rewrite (qeqT_imp_qeq _ _ (tn_qpow2_inv n)).
  apply qeqT_imp_qeq.
  apply (tn_core_eq (bv_p n) (bkQ (bk_Qn_list n) (1 # 2)%Q)
                    (q_pow (2 # 1)%Q n) (q_pow (1 # 2)%Q n) (tn_sh_one n)).
Qed.

(* ============================================================ *)
(* Sec.D tn_Pn_list evaluation surface: length and nth *)
(* ============================================================ *)

Lemma tn_Pn_list_length : forall N : nat, Id (length (tn_Pn_list N)) (Datatypes.S N).
Proof.
  induction N as [| N IH]; apply RealSetoid.eq_Id.
  - reflexivity.
  - cbn [tn_Pn_list]. rewrite app_length. rewrite (RealSetoid.Id_eq _ _ IH).
    cbn [length]. lia.
Qed.

Lemma tn_Pn_list_nth : forall N k : nat, NatLe k N ->
  QeqT (nth k (tn_Pn_list N) 0%Q) (tn_Ps_half k).
Proof.
  induction N as [| N IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as Hk0'.
    assert (Hk0 : k = 0) by lia. subst k. cbn [tn_Pn_list nth].
    apply qeq_imp_qeqT. reflexivity.
  - destruct (Nat.eq_dec k (Datatypes.S N)) as [Heq | Hne].
    + subst k. cbn [tn_Pn_list]. apply qeq_imp_qeqT.
      rewrite app_nth2 by (rewrite (RealSetoid.Id_eq _ _ (tn_Pn_list_length N)); lia).
      rewrite (RealSetoid.Id_eq _ _ (tn_Pn_list_length N)).
      replace (Datatypes.S N - Datatypes.S N) with 0 by lia.
      cbn [nth]. reflexivity.
    + pose proof (NatLe_drop _ _ Hk) as Hk'.
      assert (HkN : k <= N) by lia.
      cbn [tn_Pn_list]. apply qeq_imp_qeqT.
      rewrite app_nth1 by (rewrite (RealSetoid.Id_eq _ _ (tn_Pn_list_length N)); lia).
      apply qeqT_imp_qeq. apply IH. exact (NatLe_lift _ _ HkN).
Qed.

(* ============================================================ *)
(* Sec.E Numerical anchor group for the x' sequence (n = 0..5); each anchor decided exactly by vm_compute *)
(* ============================================================ *)

Theorem tn_x0_anchor : QeqT (tn_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x1_anchor : QeqT (tn_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x2_anchor : QeqT (tn_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x3_anchor : QeqT (tn_x 3) (131 # 189)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x4_anchor : QeqT (tn_x 4) (445 # 642)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x5_anchor : QeqT (tn_x 5) (34997 # 50490)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Cross-variant control anchors: numerical verification of tn_x n == bv_x n (n = 3..5) *)
Theorem tn_x3_bv_anchor : QeqT (tn_x 3) (bv_x 3).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x4_bv_anchor : QeqT (tn_x 4) (bv_x 4).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_x5_bv_anchor : QeqT (tn_x 5) (bv_x 5).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* r-family numerical anchors: r_0 = 0, r_1 = 8, r_2 = 72; integrality-breaking witnesses r_3, r_5; r_4 = 7120 is an integer *)
Theorem tn_r0_anchor : QeqT (tn_r 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r1_anchor : QeqT (tn_r 1) (8 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r2_anchor : QeqT (tn_r 2) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r3_anchor : QeqT (tn_r 3) (2096 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r4_anchor : QeqT (tn_r 4) (7120 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_r5_anchor : QeqT (tn_r 5) (1119904 # 15)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* P*_n(1/2) numerical anchors (numerical verification that P*_2(1/2) = 9/2 is not an integer) *)
Theorem tn_Ps1_anchor : QeqT (tn_Ps_half 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_Ps2_anchor : QeqT (tn_Ps_half 2) (9 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_Ps3_anchor : QeqT (tn_Ps_half 3) (131 # 12)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* Harmonic mismatch control anchors: the library bk_Pn_list harmonic numerators evaluated at 1/2
   (true values tn_Ps_half 1 == 2, tn_Ps_half 2 == 9/2; both mismatch) *)
Theorem tn_harm1_anchor : QeqT (bkQ (bk_Pn_list 1) (1 # 2)%Q) (1 # 2)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem tn_harm2_anchor : QeqT (bkQ (bk_Pn_list 2) (1 # 2)%Q) (19 # 8)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* Assumption audit: the Print Assumptions output below should report zero dependencies (closure recheck) *)
(* ============================================================ *)

Print Assumptions tn_x_eq_bv_x.
Print Assumptions tn_x5_anchor.
Print Assumptions tn_r5_anchor.
Print Assumptions tn_Pn_list_nth.
Print Assumptions tn_harm2_anchor.
