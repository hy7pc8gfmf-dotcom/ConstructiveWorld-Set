(* ========================================================================= *)
(*  ExpNegPos - positivity bounds for partial sums of the exponential series *)
(* ========================================================================= *)

(** * ExpNegPos: positivity bounds for exponential partial sums.

    Mission. [enp_exp_partial_ge], [enp_exp_partial_nonneg] and
    [enp_exp_partial_pos] bound the partial sums [exp_partial n (- x)] of the
    exponential series from below: for [0 <= x <= 1] every partial sum is at
    least [1 - x] and nonnegative, and for [x < 1] it is strictly positive.
    Supporting lemmas cover the monotone factorial, the paired two-step
    expansion along odd indices, and closed numerical witnesses.

    Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp, plus the
    standard-library rationals (QArith, QArith.Qabs, Arith, Lia).

    References. ConstructiveWorld-Main ConstructiveWorld_Live/ExpNegPos.v
    (statement names carried over verbatim).

    Constructivity. All statements are carried by Set-level predicates
    (QleT'/QeqT/QltT); proofs are Qed-closed with no axioms, and
    [Print Assumptions] on the three main statements reports a closed global
    context.

    Build. Rocq 9.1: [coqc -native-compiler no -Q . "" ExpNegPos.v].
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* ===== Section 0. Arithmetic helpers ===== *)
(* ============================================================ *)

(* 1 <= (S k)#1: unit lower bound of the successor rational. *)
Lemma enp_one_le_succ : forall k : nat,
  QleT' 1 ((Z.of_nat (Datatypes.S k)) # 1).
Proof.
  intros k. apply Qle_to_QleT'. unfold Qle. change (1%Q) with (1 # 1). simpl.
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1)%Z by lia.
  lia.
Qed.

(* Term decrease (division form): 0 <= x <= 1 implies x^{S k}/(S k)! <= x^k/k!,
   via the cross form of pow_fact_mono_int and q_le_div_le (both from S03). *)
Lemma enp_decr : forall (x : Q) (k : nat),
  Qle 0 x -> Qle x 1 ->
  QleT' (q_pow x (Datatypes.S k) / q_fact (Datatypes.S k))
      (q_pow x k / q_fact k).
Proof.
  intros x k H0 H1.
  assert (Hb : Qle x ((Z.of_nat (Datatypes.S k)) # 1)).
  { apply (Qle_trans x 1 ((Z.of_nat (Datatypes.S k)) # 1)).
    - exact H1.
    - apply QleT'_to_Qle. apply enp_one_le_succ. }
  apply (q_le_div_le (q_pow x (Datatypes.S k)) (q_fact (Datatypes.S k))
                     (q_pow x k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat (k + 1))%Z in Hb by lia.
    exact (pow_fact_mono_int x k (Qle_to_QleT' _ _ H0)
                        (Qle_to_QleT' _ _ Hb)).
Qed.

(* Nonnegativity: 0 <= x implies 0 <= x^k/k! (same-denominator bridge). *)
Lemma enp_term_nonneg : forall (x : Q) (k : nat),
  Qle 0 x -> QleT' 0 (q_pow x k / q_fact k).
Proof.
  intros x k H0. apply Qle_to_QleT'.
  apply (Qle_trans 0 (0 / q_fact k) (q_pow x k / q_fact k)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    assert (Hz3 : 0 == 0 / q_fact k) by (unfold Qdiv; ring).
    exact Hz3.
  - apply QleT'_to_Qle. apply (Qle_div_same_denom 0 (q_pow x k) (q_fact k)).
    + apply q_fact_pos.
    + apply q_pow_nonneg. apply Qle_to_QleT'. exact H0.
Qed.

(* ============================================================ *)
(* ===== Section 1. Two-step expansion and odd pairing ===== *)
(* ============================================================ *)

(* Two-step expansion of exp_partial (definitional replace-by-refl). *)
Lemma enp_expSS : forall (x : Q) (n : nat),
  QeqT (exp_partial (Datatypes.S (Datatypes.S n)) (Qopp x))
    (exp_partial n (Qopp x)
     + q_pow (Qopp x) (Datatypes.S n) / q_fact (Datatypes.S n)
     + q_pow (Qopp x) (Datatypes.S (Datatypes.S n))
       / q_fact (Datatypes.S (Datatypes.S n))).
Proof.
  intros x n. apply qeq_imp_qeqT.
  replace (exp_partial (Datatypes.S (Datatypes.S n)) (Qopp x))
    with (exp_partial (Datatypes.S n) (Qopp x)
          + q_pow (Qopp x) (Datatypes.S (Datatypes.S n))
            / q_fact (Datatypes.S (Datatypes.S n))) by reflexivity.
  replace (exp_partial (Datatypes.S n) (Qopp x))
    with (exp_partial n (Qopp x)
          + q_pow (Qopp x) (Datatypes.S n) / q_fact (Datatypes.S n))
    by reflexivity.
  ring.
Qed.

(* Odd two-step pairing: S_{2m+3} == S_{2m+1} + t_{2m+2} - t_{2m+3}. *)
Lemma enp_two_step_odd : forall (x : Q) (m : nat),
  QeqT (exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x))
    (exp_partial (2 * m + 1) (Qopp x)
     + q_pow x (2 * m + 2) / q_fact (2 * m + 2)
     + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))).
Proof.
  intros x m. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (enp_expSS x (2 * m + 1))).
  (* Index normalization: S(2m+1)=2m+2 (even), S(S(2m+1))=S(2m+2) (odd). *)
  replace (Datatypes.S (2 * m + 1))%nat with (2 * m + 2)%nat by lia.
  replace (2 * m + 2)%nat with (2 * Datatypes.S m)%nat by lia.
  (* 2m+2 is even so the sign drops; S(2m+2)=2m+3 is odd so it negates. *)
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg_even x (Datatypes.S m))).
  rewrite (qeqT_imp_qeq _ _ (q_pow_neg_odd x (Datatypes.S m))).
  (* nat index normalization S(2*S m) == 2m+3; ring does not normalize nat atoms. *)
  replace (Datatypes.S (2 * Datatypes.S m))%nat with (2 * m + 3)%nat by lia.
  (* Qopp through Qdiv: ring does not distribute over division; normalize via a Qeq bridge. *)
  assert (Hod : Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))
                == Qopp (q_pow x (2 * m + 3)) / q_fact (2 * m + 3))
    by (unfold Qdiv; ring).
  rewrite Hod.
  ring.
Qed.

(* Odd sums increase stepwise: S_{2m+3} >= S_{2m+1} (paired terms: t_{2m+3} <= t_{2m+2}). *)
Lemma enp_odd_step : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 ->
  QleT' (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x)).
Proof.
  intros x m H0 H1. apply Qle_to_QleT'.
  assert (Hstep := qeqT_imp_qeq _ _ (enp_two_step_odd x m)).
  assert (Hd := QleT'_to_Qle _ _ (enp_decr x (2 * m + 2) H0 H1)).
  pose proof (Qopp_le_compat _ _ Hd) as Hopp.
  (* nat index normalization S(2m+2)==2m+3 inside Hopp. *)
  replace (Datatypes.S (2 * m + 2))%nat with (2 * m + 3)%nat in Hopp by lia.
  (* Hopp : -t_{2m+3} <= -t_{2m+2}. *)
  assert (HAB : Qle 0 (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
                       + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3)))).
  { apply (Qle_trans 0
      (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
       + Qopp (q_pow x (2 * m + 2) / q_fact (2 * m + 2)))).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply Qplus_le_compat.
      + apply Qle_refl.
      + exact Hopp. }
  apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
    (exp_partial (2 * m + 1) (Qopp x)
     + (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
        + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))))
    (exp_partial (Datatypes.S (Datatypes.S (2 * m + 1))) (Qopp x))).
  - (* The atomic LHS does not unify with the x+z pattern of Qplus_le_compat; route through A+0. *)
    apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 1) (Qopp x) + 0)
      (exp_partial (2 * m + 1) (Qopp x)
       + (q_pow x (2 * m + 2) / q_fact (2 * m + 2)
          + Qopp (q_pow x (2 * m + 3) / q_fact (2 * m + 3))))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact HAB.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hstep. ring.
Qed.

(* ============================================================ *)
(* ===== Section 2. Lower bounds along all indices ===== *)
(* ============================================================ *)

(* Odd sums: S_{2m+1} >= 1-x (induction on odd partial sums). *)
Lemma enp_odd_ge : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 -> QleT' (1 - x) (exp_partial (2 * m + 1) (Qopp x)).
Proof.
  intros x m H0 H1. apply Qle_to_QleT'. induction m as [| m IH].
  - assert (Hv : exp_partial 1 (Qopp x) == 1 - x).
    { simpl. unfold Qdiv.
      replace (Qinv (1 * 1)) with 1 by reflexivity.
      ring. } (* Qdiv = Qmult x (Qinv y); Qinv(1*1) is not a ring atom, so reduce by a reflexivity replace first. *)
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    exact (Qeq_sym _ _ Hv).
  - assert (Hstep := QleT'_to_Qle _ _ (enp_odd_step x m H0 H1)).
    replace (Datatypes.S (Datatypes.S (2 * m + 1)))
      with (2 * Datatypes.S m + 1)%nat in Hstep by lia.
    apply (Qle_trans (1 - x)
      (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * Datatypes.S m + 1) (Qopp x))).
    + exact IH.
    + exact Hstep.
Qed.

(* Even sums carry odd sums: S_{2m+2} >= S_{2m+1} (adding a nonnegative term). *)
Lemma enp_even_ge_odd : forall (x : Q) (m : nat),
  Qle 0 x -> Qle x 1 ->
  QleT' (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 2) (Qopp x)).
Proof.
  intros x m H0 H1. apply Qle_to_QleT'.
  assert (Hu : exp_partial (Datatypes.S (2 * m + 1)) (Qopp x)
               == exp_partial (2 * m + 1) (Qopp x)
                  + q_pow (Qopp x) (Datatypes.S (2 * m + 1))
                    / q_fact (Datatypes.S (2 * m + 1))) by reflexivity.
  assert (Ht : q_pow (Qopp x) (Datatypes.S (2 * m + 1))
               == q_pow x (Datatypes.S (2 * m + 1))).
  { replace (Datatypes.S (2 * m + 1)) with (2 * Datatypes.S m)%nat by lia.
    exact (qeqT_imp_qeq _ _ (q_pow_neg_even x (Datatypes.S m))). }
  assert (Hn : Qle 0 (q_pow x (Datatypes.S (2 * m + 1))
                           / q_fact (Datatypes.S (2 * m + 1)))).
  { apply QleT'_to_Qle. apply enp_term_nonneg. exact H0. }
  apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
    (exp_partial (2 * m + 1) (Qopp x)
     + q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1)))
    (exp_partial (2 * m + 2) (Qopp x))).
  - (* Same A+0 routing as above for the atomic LHS. *)
    apply (Qle_trans (exp_partial (2 * m + 1) (Qopp x))
      (exp_partial (2 * m + 1) (Qopp x) + 0)
      (exp_partial (2 * m + 1) (Qopp x)
       + q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1)))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact Hn.
  - (* nat index normalization 2m+2==S(2m+1) for the rewrite site of Hu. *)
    replace (2 * m + 2)%nat with (Datatypes.S (2 * m + 1))%nat by lia.
    apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Hu. rewrite <- Ht. ring.
Qed.

(* Bound for all n (Qle-lined): 1-x <= S_n. *)
Lemma enp_ge_all : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 ->
  QleT' (1 - x) (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1. apply Qle_to_QleT'.
  destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - subst n. destruct m as [| m'].
    + (* n = 0: S_0 = 1 >= 1-x follows from x >= 0. *)
      apply (Qle_trans (1 - x) (1 + Qopp x) 1).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans (1 + Qopp x) (1 + 0) 1).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ (* Route the atomic 0 on the right through Qopp 0. *)
              apply (Qle_trans (Qopp x) (Qopp 0) 0).
              ** apply Qopp_le_compat. exact H0.
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + replace (2 * Datatypes.S m')%nat
        with (Datatypes.S (2 * m' + 1))%nat by lia.
      apply (Qle_trans (1 - x)
        (exp_partial (2 * m' + 1) (Qopp x))
        (exp_partial (Datatypes.S (2 * m' + 1)) (Qopp x))).
      * apply QleT'_to_Qle. apply enp_odd_ge; assumption.
      * (* nat index normalization S(2m'+1)==2m'+2 to match the use site of enp_even_ge_odd. *)
        replace (Datatypes.S (2 * m' + 1))%nat with (2 * m' + 2)%nat by lia.
        apply QleT'_to_Qle. apply enp_even_ge_odd; assumption.
  - subst n. apply QleT'_to_Qle. apply enp_odd_ge; assumption.
Qed.

(* ============================================================ *)
(* ===== Section 3. Set-level main statements ===== *)
(* ============================================================ *)

(* Main A (lower bound): 0 <= x <= 1 implies 1-x <= exp_partial n (-x) for all n. *)
Theorem enp_exp_partial_ge : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' (1 - x) (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1.
  apply enp_ge_all.
  - apply QleT'_to_Qle. exact H0.
  - apply QleT'_to_Qle. exact H1.
Qed.

(* Main B (nonnegativity): 0 <= x <= 1 implies 0 <= exp_partial n (-x) for all n. *)
Theorem enp_exp_partial_nonneg : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 ->
  QleT' 0 (exp_partial n (Qopp x)).
Proof.
  intros x n H0 H1.
  (* Bridge to the Qle layer first, then chain Qle_trans (mirrors Main A). *)
  apply Qle_to_QleT'.
  apply (Qle_trans 0 (1 - x) (exp_partial n (Qopp x))).
  - (* Build 0 <= 1-x natively in Q (lia rejects Q). *)
    assert (H1le : Qle x 1) by (apply QleT'_to_Qle; exact H1).
    apply (Qle_trans 0 (1 + Qopp 1) (1 - x)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans (1 + Qopp 1) (1 + Qopp x) (1 - x)).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qopp_le_compat x 1 H1le).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QleT'_to_Qle. apply enp_ge_all.
    + apply QleT'_to_Qle. exact H0.
    + apply QleT'_to_Qle. exact H1.
Qed.

(* Main C (strict positivity): 0 <= x < 1 implies 0 < exp_partial n (-x) for all n. *)
Theorem enp_exp_partial_pos : forall (x : Q) (n : nat),
  QleT' 0 x -> QltT x 1 ->
  QltT 0 (exp_partial n (Qopp x)).
Proof.
  intros x n H0 Hx1.
  assert (Hx1p : Qlt x 1) by (apply (QltT_to_Qlt x 1); exact Hx1).
  assert (H1 : QleT' x 1) by (apply (qltT_leT' x 1); exact Hx1).
  assert (Hge := enp_exp_partial_ge x n H0 H1).
  assert (Hlow : Qle (1 - x) (exp_partial n (Qopp x)))
    by (apply QleT'_to_Qle; exact Hge).
  (* lia rejects Q; build 0 < 1-x natively: x < 1 gives -1 < -x, hence 1+(-1) < 1+(-x). *)
  assert (Hlt0 : Qlt 0 (1 - x)).
  { assert (Ho : Qlt (Qopp 1) (Qopp x)) by (apply Qopp_lt_compat; exact Hx1p).
    apply (Qle_lt_trans 0 (1 + Qopp 1) (1 - x)).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    - apply (proj2 (Qplus_lt_r (Qopp 1) (Qopp x) 1)). exact Ho. }
  (* Qlt_le_trans yields the Prop-level Qlt; lift the exit to QltT via the S02 bridge. *)
  exact (Qlt_to_QltT 0 (exp_partial n (Qopp x))
    (Qlt_le_trans 0 (1 - x) (exp_partial n (Qopp x)) Hlt0 Hlow)).
Qed.

(* ============================================================ *)
(* ===== Section 4. Numerical witnesses ===== *)
(* ============================================================ *)

(* S_4(-1) = 1 - 1 + 1/2 - 1/6 + 1/24 = 3/8 (nonnegative branch at x = 1). *)
Lemma enp_eval_example1 : QeqT (exp_partial 4 (Qopp 1%Q)) (3 # 8).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* S_3(-1/2) = 1 - 1/2 + 1/8 - 1/48 = 29/48 (strict branch at x < 1; 48-24+6-1 = 29). *)
Lemma enp_eval_example2 : QeqT (exp_partial 3 (Qopp (1 # 2))) (29 # 48).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Print Assumptions enp_exp_partial_ge.
Print Assumptions enp_exp_partial_nonneg.
Print Assumptions enp_exp_partial_pos.
