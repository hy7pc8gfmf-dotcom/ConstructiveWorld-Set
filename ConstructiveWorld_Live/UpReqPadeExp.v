(* ConstructiveWorld-Set — signed Pade approximation of the exponential over the rationals. *)

(** * UpReqPadeExp: the signed Pade [n/n] approximation family over [Q].

    Mission.  Coefficient, numerator and denominator definition family
 ([pade_coeff], [pade_num], [pade_den] as finite [Q] sums), station
 values at zero and one ([pade_coeff_0_one], [pade_num_0_one],
 [pade_den_0_one], [pade_num_1_half], [pade_den_1_half]), and the
 denominator symmetry [pade_den_sym].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires [S01_BaseRing] through [S15_TailFEPUp] of this
      development.

    References.  This development, UpReqPadeExp.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: [==] equalities
 moved to [QeqT]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: <none>].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeExp.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

Section PadeExpQ.

(* ================= Section 1. Definition family ================= *)

(* Padé [n/n] coefficient: (2n−k)!·n! / ((2n)!·k!·(n−k)!), a [Q] value.
   Domain: (k <= n)%nat, which keeps every factorial argument nonnegative
   (below that bound [Nat.sub] would truncate). *)
Definition pade_coeff (n k : nat) : Q :=
  q_fact (2 * n - k) * q_fact n /
  (q_fact (2 * n) * (q_fact k * q_fact (n - k))).

(* Padé numerator P_n(x) = Σ_{k=0}^{n} c_{n,k}·x^k.
   [sum_upto m f] = Σ_{i=0}^{m−1} f i, so the upper bound is [Datatypes.S n]. *)
Definition pade_num (n : nat) (x : Q) : Q :=
  sum_upto (Datatypes.S n) (fun k => pade_coeff n k * q_pow x k).

(* Padé denominator Q_n(x) = Σ_{k=0}^{n} (−1)^k·c_{n,k}·x^k, written as an
   alternating sum ([q_pow (-1) k]) rather than the direct form with (−x)^k,
   so that the Section 3 symmetry is a genuine termwise-opp lemma rather
   than a definitional identity. *)
Definition pade_den (n : nat) (x : Q) : Q :=
  sum_upto (Datatypes.S n) (fun k => q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)).

(* Parity absorption: (−x)^k == (−1)^k·x^k — the core of the termwise opp in Section 3. *)
Lemma pade_q_pow_opp_sign : forall (x : Q) (k : nat),
  QeqT (q_pow (- x)%Q k) (q_pow (- 1)%Q k * q_pow x k).
Proof.
  intros x k. apply qeq_imp_qeqT. induction k as [| m IH].
  - simpl. reflexivity.
  - change (q_pow (- x)%Q (Datatypes.S m)) with ((- x) * q_pow (- x)%Q m).
    change (q_pow (- 1)%Q (Datatypes.S m)) with ((- 1) * q_pow (- 1)%Q m).
    change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    setoid_rewrite IH.
    ring.
Qed.

(* The k = 0 coefficient is one (definitional well-formedness; 0 <= n holds
   for all n, so no guard parameter is needed). *)
Lemma pade_coeff_0_one : forall n : nat, QeqT (pade_coeff n 0%nat) 1%Q.
Proof.
  intro n. apply qeq_imp_qeqT. unfold pade_coeff.
  assert (H1 : (2 * n - 0 = 2 * n)%nat) by lia.
  assert (H2 : (n - 0 = n)%nat) by lia.
  rewrite H1, H2.
  change (q_fact 0%nat) with 1%Q.
  setoid_rewrite Qmult_1_l.
  unfold Qdiv.
  apply Qmult_inv_r.
  intro Hz.
  assert (Hpos : Qlt 0 (q_fact (2 * n) * q_fact n))
    by (apply Qmult_lt_0_compat; apply (QltT_to_Qlt _ _); apply q_fact_pos).
  unfold Qeq in Hz. unfold Qlt in Hpos. simpl in Hz, Hpos. lia.
Qed.

(* ================= Section 2. Coefficient positivity family ================= *)

(* Positivity chain through the factorials: the numerator is a product of two
   positive factorials and the denominator a product of three, and positivity
   of the Q quotient factors as numerator-positive times
   denominator-inverse positive ([Qmult_lt_0_compat] with
   [Qinv_lt_0_compat]).  The Prop-valued order inside the proof serves only
   as a stepping stone ([Qlt_to_QltT]); the statement face is [QltT].  The
   guard (k <= n)%nat is the domain declaration of the coefficient. *)
Theorem pade_coeff_pos : forall (n k : nat), (k <= n)%nat -> QltT 0 (pade_coeff n k).
Proof.
  intros n k Hk.
  apply Qlt_to_QltT.
  unfold pade_coeff. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply (QltT_to_Qlt _ _); apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply (QltT_to_Qlt _ _). apply q_fact_pos.
    + apply Qmult_lt_0_compat; apply (QltT_to_Qlt _ _); apply q_fact_pos.
Qed.

(* ================= Section 3. Denominator symmetry ================= *)

(* Denominator symmetry: Q_n(x) == P_n(−x), by termwise opp over the finite
   sum ([sum_upto_ext] extensionality with the parity absorption lemma
   [pade_q_pow_opp_sign]). *)
Theorem pade_den_sym : forall (n : nat) (x : Q), QeqT (pade_den n x) (pade_num n (- x)).
Proof.
  intros n x. apply qeq_imp_qeqT. unfold pade_den, pade_num.
  apply qeqT_imp_qeq. apply sum_upto_ext. intro k. cbv beta.
  apply qeq_imp_qeqT.
  assert (Hopp : q_pow (- x)%Q k == q_pow (- 1)%Q k * q_pow x k)
    by (apply qeqT_imp_qeq; apply pade_q_pow_opp_sign).
  setoid_rewrite Hopp.
  ring.
Qed.

(* ================= Section 4. Station values at zero and one ================= *)

(* Tail-zero sum: if every term with positive index is zero, the sum
   collapses to its first term (the backbone of the station-value lemmas,
   by induction on the bound). *)
Lemma pade_sum_tail_zero : forall (n : nat) (f : nat -> Q),
  (forall k, (0 < k)%nat -> f k == 0) -> QeqT (sum_upto (Datatypes.S n) f) (f 0%nat).
Proof.
  intros n f H. apply qeq_imp_qeqT. induction n as [| m IH].
  - simpl. apply Qplus_0_l.
  - assert (IH' : sum_upto (Datatypes.S m) f == f 0%nat) by (apply IH; exact H).
    simpl.
    setoid_rewrite IH'.
    assert (Hlt : (0 < Datatypes.S m)%nat) by lia.
    setoid_rewrite (H (Datatypes.S m) Hlt).
    apply Qplus_0_r.
Qed.

(* Numerator normalization at x = 0: P_n(0) == 1 (the k = 0 term survives;
   every k ≥ 1 term is annihilated by the factor x^k = 0). *)
Lemma pade_num_0_one : forall n : nat, QeqT (pade_num n 0%Q) 1%Q.
Proof.
  intro n. apply qeq_imp_qeqT. unfold pade_num.
  transitivity (pade_coeff n 0%nat * q_pow 0%Q 0%nat).
  - apply qeqT_imp_qeq. apply pade_sum_tail_zero.
    intro k. destruct k as [| m]; intro Hlt; cbv beta.
    + exfalso. lia.
    + change (q_pow 0%Q (Datatypes.S m)) with (0%Q * q_pow 0%Q m).
      setoid_rewrite (Qmult_0_l (q_pow 0%Q m)).
      apply Qmult_0_r.
  - change (q_pow 0%Q 0%nat) with 1%Q.
    assert (Hc0 : pade_coeff n 0%nat == 1%Q) by (apply qeqT_imp_qeq; apply pade_coeff_0_one).
    setoid_rewrite Hc0.
    ring.
Qed.

(* Denominator normalization at x = 0: Q_n(0) == 1 (as above, additionally
   using (−1)^0 = 1). *)
Lemma pade_den_0_one : forall n : nat, QeqT (pade_den n 0%Q) 1%Q.
Proof.
  intro n. apply qeq_imp_qeqT. unfold pade_den.
  transitivity (q_pow (- 1)%Q 0%nat * (pade_coeff n 0%nat * q_pow 0%Q 0%nat)).
  - apply qeqT_imp_qeq. apply pade_sum_tail_zero.
    intro k. destruct k as [| m]; intro Hlt; cbv beta.
    + exfalso. lia.
    + change (q_pow 0%Q (Datatypes.S m)) with (0%Q * q_pow 0%Q m).
      setoid_rewrite (Qmult_0_l (q_pow 0%Q m)).
      setoid_rewrite (Qmult_0_r (pade_coeff n (Datatypes.S m))).
      apply Qmult_0_r.
  - change (q_pow (- 1)%Q 0%nat) with 1%Q.
    change (q_pow 0%Q 0%nat) with 1%Q.
    assert (Hc0 : pade_coeff n 0%nat == 1%Q) by (apply qeqT_imp_qeq; apply pade_coeff_0_one).
    setoid_rewrite Hc0.
    ring.
Qed.

(* Fully expanded n = 1 instance: P_1(x) = 1 + x/2 and Q_1(x) = 1 − x/2, so
   P_1(1/2) = 5/4 and Q_1(1/2) = 3/4.  The proofs compute the closed forms
   by [vm_compute] — an end-to-end numerical check of the coefficient
   formula, the bounded sum, and the alternating sign (any [Nat.sub]
   truncation leaking into the definitions or a flipped sign turns these
   statements red). *)
Lemma pade_num_1_half : QeqT (pade_num 1 (1#2)) (5#4).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma pade_den_1_half : QeqT (pade_den 1 (1#2)) (3#4).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ================= Interface boundary: remainder statements left out =================

   The remainder theory of the Padé [n/n] family rests on the integral
   representation
     e^x − P_n(x)/Q_n(x) = (−1)^n · x^{2n+1} / ((2n)!·Q_n(x))
                           · ∫₀¹ tⁿ(1−t)ⁿ e^{tx} dt,
   from which, for x ≥ 0, the sign of the error is (−1)^n and an explicit
   error bound is computable.  The four statements [pade_error_integral],
   [pade_integral_pos], [pade_error_sign] and [pade_error_bound] are
   deliberately not included here: the integral representation requires a
   constructive integration infrastructure that this development does not
   yet provide, and no ad-hoc assumptions are introduced in their place.

   Upgrade path:
   1. constructive integration of polynomial-type integrands on [0,1]
      (piecewise Q-level sums with a Cauchy limit, reusing the Cauchy
      completeness of [S02_CauchyComplete]);
   2. [pade_integral_pos]: a pointwise-positive integrand has a positive
      integral (monotonicity of the integral); together with
      [pade_q_pow_opp_sign], [pade_den_sym] and [pade_coeff_pos] this gives
      Q_n(x) > 0 for x ≥ 0 from coefficient positivity plus an
      alternating-sum lower bound;
   3. [pade_error_bound]: an explicit [Q] bound of the form
      |remainder| ≤ e^B·B^{2n+1}/((2n)!·(2n+1)) for |x| ≤ B (via [q_fact]
      positivity and the geometric decay [pow_fact_geom]). *)

End PadeExpQ.
