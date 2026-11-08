(* ConstructiveWorld-Set -- the rational-layer factorial growth lower bound with the 10/3 domination corollaries. *)
(** * LW0FactGrowth: the factorial's rational-layer growth lower bound and
    the domination of the rational constant 10/3 by the factorial.

    Mission.  For every natural number n, n! is at least the half-base
      power (n/2)^(n/2) (halving by [Nat.div2]); and (10/3)^n <= n! for all
      n = 22+2k and n = 23+2k (k natural; jointly covering all n >= 22).
      With the repository's rational upper bound 10/3 for pi
      (real_pi_leibniz_lt_ten_thirds of S10_KVQuantTrig, pi < 10/3), this
      module is the rational-constant-side engine for "the power growth of
      pi is dominated by n!"; real-layer power transport is out of scope.

    Dependencies.  [S02_CauchyComplete] (the QleT' decision and its
      two-directional bridges), [S03_QExp] ([q_fact], [q_pow]); Stdlib
      [QArith], [Arith], [ZArith], [Lia].

    References.  n! >= (n/2)^(n/2) is the standard elementary estimate (the
      factors from n/2 on are each at least n/2); no Stdlib rational-layer
      counterpart; in-repository precedent BetaLower (isomorphic QleT'
      statement form and extraction check); same-name ConstructiveWorld-Main
      baseline.

    Constructivity.  All statements Set-carried (global QleT' throughout;
      zero Prop premises, zero existential arguments); axiom-free; no
      classical logic; genuinely constructed Fixpoint factor-table
      decomposition; main statements support Separate Extraction with zero
      Obj.magic.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" LW0FactGrowth.v] (direct call, cpu_guard wrapped). *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ================= §1 order-preserving support lemmas over the rational layer ================= *)

(* The rational image of a natural number (same shape as the q_fact step
   coefficient, convenient for definitional reduction). *)
Definition lw0_q_of_nat (n : nat) : Q := (Z.of_nat n # 1)%Q.

(* The rational image of a natural number is nonnegative. *)
Lemma lw0_q_of_nat_nonneg : forall n : nat, QleT' 0 (lw0_q_of_nat n).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* The rational image of a successor is at least 1. *)
Lemma lw0_q_of_nat_ge_one : forall n : nat, QleT' 1 (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* Monotonicity of the rational image under successor. *)
Lemma lw0_q_of_nat_le_succ : forall n : nat,
  QleT' (lw0_q_of_nat n) (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* Monotonicity of the rational image under addition: the image of a does
   not exceed the image of a+b. *)
Lemma lw0_q_of_nat_le_add : forall a b : nat,
  QleT' (lw0_q_of_nat a) (lw0_q_of_nat (a + b)%nat).
Proof.
  intros a b. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* Monotonicity of powers in the base: 0 ≤ x ≤ y implies x^n ≤ y^n. *)
Lemma lw0_q_pow_mono_base : forall (x y : Q) (n : nat),
  QleT' 0 x -> QleT' x y -> QleT' (q_pow x n) (q_pow y n).
Proof.
  intros x y n H0 Hxy. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - cbn [q_pow].
    apply (Qle_trans _ (x * q_pow y n)%Q).
    + rewrite (Qmult_comm x (q_pow x n)), (Qmult_comm x (q_pow y n)).
      apply Qmult_le_compat_r.
      * exact IH.
      * exact (QleT'_to_Qle _ _ H0).
    + apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hxy).
      * apply QleT'_to_Qle. apply q_pow_nonneg. apply (qleT'_trans 0 x y H0 Hxy).
Qed.

(* Successor enlargement of powers: x ≥ 1 implies x^n ≤ x^(n+1). *)
Lemma lw0_q_pow_le_succ_pow : forall (x : Q) (n : nat),
  QleT' 1 x -> QleT' (q_pow x n) (q_pow x (Datatypes.S n)).
Proof.
  intros x n Hx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ x n)).
  apply (Qle_trans _ (1 * q_pow x n)%Q).
  - rewrite (Qmult_comm 1 (q_pow x n)), Qmult_1_r. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hx).
    + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. apply (Qle_trans 0%Q 1%Q x).
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact (QleT'_to_Qle _ _ Hx).
Qed.

(* ================= §2 the factor-table decomposition of the factorial and the half-base-power lower bound ================= *)

(* The step equation of the factorial: q_fact (n+1) == (n+1)·q_fact n (the
   coefficient is definitionally lw0_q_of_nat). *)
Lemma lw0_q_fact_step : forall k : nat,
  QeqT (q_fact (Datatypes.S k)) (lw0_q_of_nat (Datatypes.S k) * q_fact k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

(* The factorial is at least 1. *)
Lemma lw0_q_fact_ge_one : forall k : nat, QleT' 1 (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [| k IH].
  - apply Qle_refl.
  - rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step k)).
    apply Qmult_le_1_compat.
    + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)).
    + exact IH.
Qed.

(* The two-step equation of the factorial:
   q_fact (n+2) == (n+2)·(n+1)·q_fact n. *)
Lemma lw0_q_fact_step2 : forall k : nat,
  QeqT (q_fact (Datatypes.S (Datatypes.S k)))
  (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) * lw0_q_of_nat (Datatypes.S k) * q_fact k).
Proof.
  intro k. apply qeq_imp_qeqT.
  transitivity (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) *
                (lw0_q_of_nat (Datatypes.S k) * q_fact k))%Q.
  - reflexivity.
  - ring.
Qed.

(* The tail segment of the factor table: (a+1)·(a+2)···(a+k), a genuinely
   constructed inductive structure. *)
Fixpoint lw0_fact_range (a k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S j => lw0_q_of_nat (a + Datatypes.S j) * lw0_fact_range a j
  end.

(* The factor-table decomposition:
   q_fact (a+k) == q_fact a·(a+1)···(a+k). *)
Lemma lw0_q_fact_split : forall a k : nat,
  QeqT (q_fact (a + k)%nat) (q_fact a * lw0_fact_range a k).
Proof.
  intros a k. apply qeq_imp_qeqT. induction k as [| k IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - cbn [lw0_fact_range].
    replace (a + Datatypes.S k)%nat with (Datatypes.S (a + k))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step (a + k)%nat)), IH. ring.
Qed.

(* Power lower bound for the tail segment:
   (a+1)^k ≤ (a+1)·(a+2)···(a+k), factor-by-factor comparison. *)
Lemma lw0_fact_range_ge_pow : forall a k : nat,
  QleT' (q_pow (lw0_q_of_nat (Datatypes.S a)) k) (lw0_fact_range a k).
Proof.
  intros a k. induction k as [| k IH].
  - apply qleT'_refl.
  - apply Qle_to_QleT'.
    cbn [lw0_fact_range q_pow].
    apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S a) * lw0_fact_range a k)%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S a))
                          (q_pow (lw0_q_of_nat (Datatypes.S a)) k)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S a)) (lw0_fact_range a k)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ IH).
      * apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
    + apply Qmult_le_compat_r.
      * unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
      * apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S a)) k)
                           (lw0_fact_range a k)).
        -- apply QleT'_to_Qle. apply q_pow_nonneg. apply lw0_q_of_nat_nonneg.
        -- exact (QleT'_to_Qle _ _ IH).
Qed.

(** The doubled lower bound for the half-base power: for every natural
    number m, m^m ≤ (2m)!.  Mathematical meaning: the tail segment
    (m+1)···(2m) of the factor table 1·2···(2m) has m factors, each at
    least m+1 ≥ m.
    Proof strategy: decompose the factor table to the tail segment, compare
    the tail segment factor-by-factor with (m+1)^m, then multiply back the
    head segment. *)
Lemma lw0_pow_half_le_fact_double : forall m : nat,
  QleT' (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m)%nat).
Proof.
  intro m.
  apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_pow (lw0_q_of_nat (Datatypes.S m)) m)).
  - exact (lw0_q_pow_mono_base (lw0_q_of_nat m) (lw0_q_of_nat (Datatypes.S m)) m
      (lw0_q_of_nat_nonneg m) (lw0_q_of_nat_le_succ m)).
  - apply (qleT'_trans (q_pow (lw0_q_of_nat (Datatypes.S m)) m) (lw0_fact_range m m)).
    + exact (lw0_fact_range_ge_pow m m).
    + replace (2 * m)%nat with (m + m)%nat by lia.
      apply Qle_to_QleT'.
      rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_split m m)).
      apply (Qle_trans _ (1 * lw0_fact_range m m)%Q).
      * rewrite (Qmult_comm 1 (lw0_fact_range m m)), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one m)).
        -- apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S m)) m)
                             (lw0_fact_range m m)).
           ++ apply QleT'_to_Qle. apply q_pow_nonneg. apply lw0_q_of_nat_nonneg.
           ++ exact (QleT'_to_Qle _ _ (lw0_fact_range_ge_pow m m)).
Qed.

(** The half-base-power lower bound for the factorial: for every natural
    number n, (n/2)^(n/2) ≤ n!, where halving is [Nat.div2].  Mathematical
    meaning: the factors of the factor table of n from n/2 on are each at
    least n/2.
    Proof strategy: case on the Boolean value of [Nat.odd] through the
    parity equation [Nat.div2_odd]; the even case reduces to the doubled
    lower bound; the odd case multiplies in the last factor. *)
Theorem lw0_fact_lower_growth : forall n : nat,
  QleT' (q_pow (lw0_q_of_nat (Nat.div2 n)) (Nat.div2 n)) (q_fact n).
Proof.
  intro n.
  pose proof (Nat.div2_odd n) as Hd.
  destruct (Nat.odd n) eqn:Hodd.
  - (* Case n odd: n = 2·(n/2)+1. *)
    cbn [Nat.b2n] in Hd |- *.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m))).
    + exact (lw0_pow_half_le_fact_double m).
    + replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
      apply Qle_to_QleT'.
      rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step (2 * m)%nat)).
      apply (Qle_trans _ (1 * q_fact (2 * m))%Q).
      * rewrite (Qmult_comm 1 (q_fact (2 * m))), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one (2 * m))).
        -- apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply q_fact_pos.
  - (* Case n even: n = 2·(n/2). *)
    cbn [Nat.b2n] in Hd |- *. rewrite Nat.add_0_r in Hd.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    exact (lw0_pow_half_le_fact_double m).
Qed.

(* ================= §3 the powers of the rational upper bound of pi are dominated by the factorial ================= *)

(* Two-step advancement lemma: if 1 ≤ c ≤ the rational image of n+1 and
   c^n ≤ n!, then c^(n+2) ≤ (n+2)!.
   From c^(n+2) = c·(c·c^n) and (n+2)! = (n+2)·(n+1)·n!, the inequality is
   scaled factor by factor. *)
Lemma lw0_q_pow_fact_step2 : forall (c : Q) (n : nat),
  QleT' 1 c ->
  QleT' c (lw0_q_of_nat (Datatypes.S n)) ->
  QleT' (q_pow c n) (q_fact n) ->
  QleT' (q_pow c (Datatypes.S (Datatypes.S n)))
        (q_fact (Datatypes.S (Datatypes.S n))).
Proof.
  intros c n H1c Hcn IH. apply Qle_to_QleT'.
  pose proof (fun (x : Q) (m : nat) => qeqT_imp_qeq _ _ (q_pow_succ x m)) as Hqs.
  rewrite (qeqT_imp_qeq _ _ (lw0_q_fact_step2 n)), !Hqs.
  rewrite <- (Qmult_assoc (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                          (lw0_q_of_nat (Datatypes.S n)) (q_fact n))%Q.
  assert (H0c : Qle 0 c).
  { apply (Qle_trans 0%Q 1%Q c).
    - unfold Qle. cbn [Qnum Qden]. lia.
    - exact (QleT'_to_Qle _ _ H1c). }
  assert (H0P : Qle 0 (q_pow c n))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; apply Qle_to_QleT'; exact H0c).
  assert (HcP : Qle (c * q_pow c n)
                    (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * q_pow c n)).
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hcn).
      + exact H0P.
    - rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_fact n)).
      apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ IH).
      + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))). }
  assert (H0cP : Qle 0 (c * q_pow c n))
    by (apply Qmult_le_0_compat; assumption).
  assert (H0BF : Qle 0 (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply Qmult_le_0_compat.
    - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    - apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply q_fact_pos. }
  assert (HBA : Qle (lw0_q_of_nat (Datatypes.S n))
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
  { replace (Datatypes.S (Datatypes.S n))%nat with (Datatypes.S n + 1)%nat by lia.
    exact (QleT'_to_Qle _ _ (lw0_q_of_nat_le_add (Datatypes.S n) 1)). }
  apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * (c * q_pow c n))%Q).
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hcn).
    + exact H0cP.
  - apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) *
                        (lw0_q_of_nat (Datatypes.S n) * q_fact n))%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (c * q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n))
                          (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
      apply Qmult_le_compat_r.
      * exact HcP.
      * exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    + apply Qmult_le_compat_r.
      * exact HBA.
      * exact H0BF.
Qed.

(** Factorial domination of the powers of the rational upper bound of pi
    (even family): for every natural number k, (10/3)^(22+2k) ≤ (22+2k)!.
    Mathematical meaning: combined with the in-repository estimate pi < 10/3
    (real_pi_leibniz_lt_ten_thirds of S10_KVQuantTrig), for every even
    n ≥ 22 the n-th power of pi's upper bound 10/3 does not exceed n!.
    Proof strategy: the base case closes by numerical decision; the
    induction step is completed by the two-step advancement lemma. *)
Theorem lw0_pi_bound_dominated_even : forall k : nat,
  QleT' (q_pow (10 # 3) (22 + 2 * k)%nat) (q_fact (22 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* Base case k = 0, i.e. n = 22: numerical decision. *)
    vm_compute. reflexivity.
  - (* Induction step: from k to S k, i.e. from n to n+2. *)
    replace (22 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (22 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (22 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (22 + 2 * k)) with (23 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 23)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(** Factorial domination of the powers of the rational upper bound of pi
    (odd family): for every natural number k, (10/3)^(23+2k) ≤ (23+2k)!.
    Conjoined with the even family, this covers all n ≥ 22.
    The proof strategy is the same as the even family: numerical decision
    at the base case, two-step advancement at the induction step. *)
Theorem lw0_pi_bound_dominated_odd : forall k : nat,
  QleT' (q_pow (10 # 3) (23 + 2 * k)%nat) (q_fact (23 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* Base case k = 0, i.e. n = 23: numerical decision. *)
    vm_compute. reflexivity.
  - (* Induction step: from k to S k, i.e. from n to n+2. *)
    replace (23 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (23 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (23 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (23 + 2 * k)) with (24 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 24)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(* Extraction check and axiom-face self-audit: the extraction products
   contain zero Obj.magic, and every statement is Closed. *)

From Stdlib Require Import Extraction.
Separate Extraction lw0_fact_lower_growth lw0_pi_bound_dominated_even lw0_pi_bound_dominated_odd.

Print Assumptions lw0_fact_lower_growth.
Print Assumptions lw0_pi_bound_dominated_even.
Print Assumptions lw0_pi_bound_dominated_odd.
