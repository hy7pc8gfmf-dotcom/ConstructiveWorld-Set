(* ============================================================
   piu1888_growth_quant_lemma
   Mission.
     Quantitative core of the pi-separation nucleus scale T0 = (2n)!/n!:
     the step identity qfact(2(S n)) * qfact n == (2 as Q) * qN(S(2n)) *
     qfact(2n) * qfact(S n), the doubling limb 2*T0 n <= T0(S n) in
     product form, the positivity companions, and the division-transfer
     lemma piu1888_div_le.
   Dependencies.
     Stdlib QArith (transparent Q layer); Stdlib Lia for nat-side linear
     bookkeeping inside proofs; S02_CauchyComplete from the Set tree,
     selectively imported (nine names) for the Set-carried comparison
     faces QltT / QleT' / QeqT and their registered converters.
   References.
     LW0LeibSeparation.v K = BF*C1 + BFd*C2 + 1/8 (:5469); closed-form
     coordinates f^(d)(q) = (-1)^n b^n q^(2n-d) d!/((d-n)!(2n-d)!).
   Constructivity.
     Statement faces are Set-carried boolean Id forms (QltT/QleT'/QeqT);
     premise positions keep the Qle/Qlt Prop kernels lawfully; proof
     bodies bridge through the in-register S02 converters.  Definitions
     transparent; every proof ends in Qed; Qinv is consumed only through
     the piu1888_div_le gate; closed numeric steps close by vm_compute.
   Build.
     rocq c -native-compiler no -q -Q . "" piu1888_growth_quant_lemma.v
     (Rocq 9.1 toolchain, thermal-guard wrapped; world = S01_BaseRing.vo
     and S02_CauchyComplete.vo in this directory).
   ============================================================ *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
Require Import S02_CauchyComplete
  (QltT, QleT', QeqT, Qlt_to_QltT, QltT_to_Qlt,
   Qle_to_QleT', QleT'_to_Qle, qeq_imp_qeqT, qeqT_imp_qeq).

Fixpoint piu1888_qN (n : nat) : Q :=
  match n with
  | O => 0#1
  | S k => (1#1) + piu1888_qN k
  end.

Fixpoint piu1888_qfact (n : nat) : Q :=
  match n with
  | O => 1#1
  | S k => piu1888_qN (S k) * piu1888_qfact k
  end.

Fixpoint piu1888_qpow (q : Q) (m : nat) : Q :=
  match m with
  | O => 1#1
  | S k => q * piu1888_qpow q k
  end.

Lemma piu1888_qN_step : forall k, QeqT (piu1888_qN (S k)) ((1#1) + piu1888_qN k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma piu1888_qfact_step : forall k, QeqT (piu1888_qfact (S k)) (piu1888_qN (S k) * piu1888_qfact k).
Proof. intro k. apply qeq_imp_qeqT. reflexivity. Qed.

Lemma piu1888_mul_ge0 : forall a b : Q, (0#1) <= a -> (0#1) <= b -> QleT' (0#1) (a * b).
Proof. intros a b Ha Hb. apply Qle_to_QleT'. apply Qmult_le_0_compat; assumption. Qed.

Lemma piu1888_qN_double : forall n, QeqT (piu1888_qN (2 * n)) ((2#1) * piu1888_qN n).
Proof.
  intro n. apply qeq_imp_qeqT.
  induction n as [|n IH].
  - vm_compute. reflexivity.
  - assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
    rewrite H2n.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step (S (2 * n)))),
            (qeqT_imp_qeq _ _ (piu1888_qN_step (2 * n))),
            IH.
    rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step n)).
    rewrite (Qmult_plus_distr_r (2#1) (1#1) (piu1888_qN n)).
    rewrite Qmult_1_r.
    rewrite Qplus_assoc.
    reflexivity.
Qed.

Lemma piu1888_qN_ge0 : forall k, QleT' (0#1) (piu1888_qN k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [|k IHk].
  - vm_compute. discriminate.
  - rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step k)).
    apply (Qplus_le_compat (0#1) (1#1) (0#1) (piu1888_qN k)).
    + vm_compute. discriminate.
    + exact IHk.
Qed.

Lemma piu1888_qN_ge1 : forall k, QleT' (1#1) (piu1888_qN (S k)).
Proof.
  intros k. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step k)).
  apply (Qle_trans ((1#1)) ((1#1) + (0#1)) ((1#1) + piu1888_qN k)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN k)).
    + apply Qle_refl.
    + exact (QleT'_to_Qle _ _ (piu1888_qN_ge0 k)).
Qed.

Lemma piu1888_qN_pos : forall k, QltT (0#1) (piu1888_qN (S k)).
Proof.
  intros k. apply Qlt_to_QltT.
  apply (Qlt_le_trans (0#1) (1#1) (piu1888_qN (S k))).
  - vm_compute. reflexivity.
  - exact (QleT'_to_Qle _ _ (piu1888_qN_ge1 k)).
Qed.

Lemma piu1888_qfact_ge1 : forall n, QleT' (1#1) (piu1888_qfact n).
Proof.
  intro n. apply Qle_to_QleT'.
  induction n as [|n IH].
  - vm_compute. discriminate.
  - rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step n)).
    apply (Qle_trans ((1#1)) (piu1888_qfact n) (piu1888_qN (S n) * piu1888_qfact n)).
    + exact IH.
    + apply (Qle_trans (piu1888_qfact n) ((1#1) * piu1888_qfact n)
               (piu1888_qN (S n) * piu1888_qfact n)).
      * rewrite Qmult_1_l. apply Qle_refl.
      * apply (Qmult_le_compat_r (1#1) (piu1888_qN (S n)) (piu1888_qfact n)).
        -- exact (QleT'_to_Qle _ _ (piu1888_qN_ge1 n)).
        -- apply (Qle_trans (0#1) (1#1) (piu1888_qfact n)).
           ++ vm_compute. discriminate.
           ++ exact IH.
Qed.

Lemma piu1888_qfact_pos : forall n, QltT (0#1) (piu1888_qfact n).
Proof.
  intros n. apply Qlt_to_QltT.
  apply (Qlt_le_trans (0#1) (1#1) (piu1888_qfact n)).
  - vm_compute. reflexivity.
  - exact (QleT'_to_Qle _ _ (piu1888_qfact_ge1 n)).
Qed.

Lemma piu1888_qpow_pos : forall q m, (0#1) < q -> QltT (0#1) (piu1888_qpow q m).
Proof.
  intros q m Hq. apply Qlt_to_QltT.
  induction m as [|m IH]; [vm_compute; reflexivity|].
  simpl. apply Qmult_lt_0_compat; assumption.
Qed.

Lemma piu1888_Qmul_cancel : forall a b c : Q, ~ (c == 0) -> a * c == b * c -> QeqT a b.
Proof.
  intros a b c Hc Heq.
  assert (H1 : a * c * / c == b * c * / c) by (rewrite Heq; reflexivity).
  rewrite <- (Qmult_assoc a c (/ c)) in H1.
  rewrite <- (Qmult_assoc b c (/ c)) in H1.
  rewrite (Qmult_inv_r c Hc) in H1.
  rewrite Qmult_1_r in H1.
  rewrite Qmult_1_r in H1.
  apply qeq_imp_qeqT. exact H1.
Qed.

Lemma piu1888_prod_shuffle : forall a b c d : Q,
  QeqT (a * b * (c * d)) (a * c * (b * d)).
Proof.
  intros a b c d. apply qeq_imp_qeqT.
  rewrite <- (Qmult_assoc a b (c * d)).
  rewrite <- (Qmult_assoc a c (b * d)).
  rewrite (Qmult_comm b (c * d)).
  rewrite <- (Qmult_assoc c d b).
  rewrite (Qmult_comm d b).
  reflexivity.
Qed.

Lemma piu1888_le_mul_r : forall w v : Q, (0#1) <= w -> (1#1) <= v -> QleT' w (w * v).
Proof.
  intros w v Hw Hv. apply Qle_to_QleT'.
  apply (Qle_trans ((w)) ((v * w)) ((w * v))).
  - apply (Qle_trans ((w)) ((1#1) * w) ((v * w))).
    + rewrite Qmult_1_l. apply Qle_refl.
    + apply (Qmult_le_compat_r (1#1) v w).
      * exact Hv.
      * exact Hw.
  - rewrite (Qmult_comm v w). apply Qle_refl.
Qed.

(* T0 = (2n)!/n! *)
Definition piu1888_T0 (n : nat) : Q := piu1888_qfact (2 * n) * / piu1888_qfact n.

Lemma piu1888_T0_pos : forall n, QltT (0#1) (piu1888_T0 n).
Proof.
  intros n. apply Qlt_to_QltT. unfold piu1888_T0. apply Qmult_lt_0_compat.
  - apply QltT_to_Qlt. apply piu1888_qfact_pos.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply piu1888_qfact_pos.
Qed.

(* Step identity (product form): (2(S n))! * n! == 2*(2n+1 as Q) * (2n)! * (S n)! *)
Lemma piu1888_T0_prod_step : forall n,
  QeqT (piu1888_qfact (2 * S n) * piu1888_qfact n)
  ((2#1) * piu1888_qN (S (2 * n)) * piu1888_qfact (2 * n) * piu1888_qfact (S n)).
Proof.
  intros n. apply qeq_imp_qeqT.
  assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
  rewrite H2n.
  rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (S (2 * n)))),
          (qeqT_imp_qeq _ _ (piu1888_qfact_step (2 * n))).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step (S (2 * n)))),
          (qeqT_imp_qeq _ _ (piu1888_qN_step (2 * n))),
          (qeqT_imp_qeq _ _ (piu1888_qN_double n)).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step n)),
          (qeqT_imp_qeq _ _ (piu1888_qN_step n)).
  assert (Hc : (1#1) + ((1#1) + (2#1) * piu1888_qN n) == (2#1) * ((1#1) + piu1888_qN n)).
  { rewrite (Qmult_plus_distr_r (2#1) (1#1) (piu1888_qN n)).
    rewrite Qmult_1_r.
    rewrite Qplus_assoc.
    reflexivity. }
  rewrite Hc.
  rewrite (Qmult_assoc ((2#1) * ((1#1) + piu1888_qN n))
                       ((1#1) + (2#1) * piu1888_qN n) (piu1888_qfact (2 * n))).
  rewrite <- (Qmult_assoc (2#1) ((1#1) + piu1888_qN n)
                       ((1#1) + (2#1) * piu1888_qN n)).
  rewrite (Qmult_comm ((1#1) + piu1888_qN n) ((1#1) + (2#1) * piu1888_qN n)).
  rewrite (Qmult_assoc (2#1) ((1#1) + (2#1) * piu1888_qN n)
                       ((1#1) + piu1888_qN n)).
  rewrite <- (Qmult_assoc ((2#1) * ((1#1) + (2#1) * piu1888_qN n) *
                       ((1#1) + piu1888_qN n)) (piu1888_qfact (2 * n))
                       (piu1888_qfact n)).
  rewrite (qeqT_imp_qeq _ _ (piu1888_prod_shuffle ((2#1) * ((1#1) + (2#1) * piu1888_qN n))
            ((1#1) + piu1888_qN n) (piu1888_qfact (2 * n)) (piu1888_qfact n))).
  reflexivity.
Qed.

(* Doubling limb (product form): 2*(2n)!*n! <= (2(S n))!*(S n)! *)
Lemma piu1888_T0_mono_prod : forall n,
  QleT' ((2#1) * (piu1888_qfact (2 * n) * piu1888_qfact n))
  (piu1888_qfact (2 * S n) * piu1888_qfact (S n)).
Proof.
  intros n. apply Qle_to_QleT'.
  assert (Hx0 : (0#1) <= piu1888_qN n) by exact (QleT'_to_Qle _ _ (piu1888_qN_ge0 n)).
  assert (HQ1 : (1#1) <= (1#1) + (2#1) * piu1888_qN n).
  { apply (Qle_trans ((1#1)) ((1#1) + (0#1)) ((1#1) + (2#1) * piu1888_qN n)).
    - rewrite Qplus_0_r. apply Qle_refl.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) ((2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + apply QleT'_to_Qle. apply piu1888_mul_ge0.
        * vm_compute. discriminate.
        * exact Hx0. }
  assert (HQ0 : (0#1) <= (1#1) + (2#1) * piu1888_qN n).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + (2#1) * piu1888_qN n)).
    - vm_compute. discriminate.
    - exact HQ1. }
  assert (HP0 : (0#1) <= (1#1) + ((1#1) + (2#1) * piu1888_qN n)).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + ((1#1) + (2#1) * piu1888_qN n))).
    - vm_compute. discriminate.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) ((1#1) + (2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + exact HQ0. }
  assert (HP1 : (2#1) <= (1#1) + ((1#1) + (2#1) * piu1888_qN n)).
  { apply (Qle_trans ((1#1) + (1#1)) ((1#1) + (1#1))
             ((1#1) + ((1#1) + (2#1) * piu1888_qN n))).
    - apply Qle_refl.
    - apply (Qplus_le_compat (1#1) (1#1) (1#1) ((1#1) + (2#1) * piu1888_qN n)).
      + apply Qle_refl.
      + exact HQ1. }
  assert (H1x : (0#1) <= (1#1) + piu1888_qN n).
  { apply (Qle_trans (0#1) (1#1) ((1#1) + piu1888_qN n)).
    - vm_compute. discriminate.
    - apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN n)).
      + apply Qle_refl.
      + exact Hx0. }
  assert (H2n : (2 * S n)%nat = S (S (2 * n))) by lia.
  rewrite H2n.
  rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (S (2 * n)))).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step n)).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step (S (2 * n)))),
          (qeqT_imp_qeq _ _ (piu1888_qN_step (2 * n))),
          (qeqT_imp_qeq _ _ (piu1888_qN_double n)),
          (qeqT_imp_qeq _ _ (piu1888_qN_step n)).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qfact_step (2 * n))).
  rewrite (qeqT_imp_qeq _ _ (piu1888_qN_step (2 * n))),
          (qeqT_imp_qeq _ _ (piu1888_qN_double n)).
  rewrite (qeqT_imp_qeq _ _ (piu1888_prod_shuffle _ _ _ _)).
  rewrite <- (Qmult_assoc ((1#1) + (2#1) * piu1888_qN n)
             (piu1888_qfact (2 * n)) (piu1888_qfact n)).
  rewrite (Qmult_assoc (((1#1) + ((1#1) + (2#1) * piu1888_qN n))
             * ((1#1) + piu1888_qN n)) ((1#1) + (2#1) * piu1888_qN n)
             (piu1888_qfact (2 * n) * piu1888_qfact n)).
  apply (Qmult_le_compat_r (2#1)
           (((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n)
              * ((1#1) + (2#1) * piu1888_qN n))
           (piu1888_qfact (2 * n) * piu1888_qfact n)).
  - apply (Qle_trans (2#1) ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
             ((((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
                * ((1#1) + (2#1) * piu1888_qN n))).
    + exact HP1.
    + apply (Qle_trans ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
               (((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
               ((((1#1) + ((1#1) + (2#1) * piu1888_qN n)) * ((1#1) + piu1888_qN n))
                  * ((1#1) + (2#1) * piu1888_qN n))).
      * apply QleT'_to_Qle.
        apply (piu1888_le_mul_r ((1#1) + ((1#1) + (2#1) * piu1888_qN n))
                 ((1#1) + piu1888_qN n)).
        -- exact HP0.
        -- apply (Qle_trans (1#1) ((1#1) + (0#1)) ((1#1) + piu1888_qN n)).
           ++ rewrite Qplus_0_r. apply Qle_refl.
           ++ apply (Qplus_le_compat (1#1) (1#1) (0#1) (piu1888_qN n)).
              ** apply Qle_refl.
              ** exact Hx0.
      * apply QleT'_to_Qle.
        apply (piu1888_le_mul_r (((1#1) + ((1#1) + (2#1) * piu1888_qN n))
                     * ((1#1) + piu1888_qN n))
                 ((1#1) + (2#1) * piu1888_qN n)).
        -- apply QleT'_to_Qle. apply piu1888_mul_ge0.
           ++ exact HP0.
           ++ exact H1x.
        -- exact HQ1.
  - apply QleT'_to_Qle. apply piu1888_mul_ge0; apply Qlt_le_weak;
      exact (QltT_to_Qlt _ _ (piu1888_qfact_pos _)).
Qed.

(* Division transfer (Qinv single-point gate) *)
Lemma piu1888_inv_mul_swap : forall s t : Q,
  (0#1) < s -> (0#1) < t -> QeqT (t * / (s * t)) (/ s).
Proof.
  intros s t Hs Ht.
  assert (Hst : ~ (s * t == 0)).
  { intros Hc. exact (Qlt_not_eq (0#1) (s * t) (Qmult_lt_0_compat s t Hs Ht)
                       (Qeq_sym (s * t) (0#1) Hc)). }
  assert (Hs0 : ~ (s == 0)).
  { intros Hc. exact (Qlt_not_eq (0#1) s Hs (Qeq_sym s (0#1) Hc)). }
  assert (H1 : s * (t * / (s * t)) == s * / s).
  { rewrite (Qmult_assoc s t (/(s * t))).
    rewrite (Qmult_inv_r (s * t) Hst).
    rewrite (Qmult_inv_r s Hs0).
    reflexivity. }
  rewrite (Qmult_comm s (t * / (s * t))) in H1.
  rewrite (Qmult_comm s (/ s)) in H1.
  exact (piu1888_Qmul_cancel (t * / (s * t)) (/ s) s Hs0 H1).
Qed.

Lemma piu1888_div_le : forall u v s t : Q,
  (0#1) < s -> (0#1) < t -> u * t <= v * s -> QleT' (u * / s) (v * / t).
Proof.
  intros u v s t Hs Ht H.
  assert (H1 : u * t * / (s * t) <= v * s * / (s * t)).
  { apply (Qmult_le_compat_r (u * t) (v * s) (/(s * t))).
    - exact H.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; assumption. }
  rewrite <- (Qmult_assoc u t (/(s * t))) in H1.
  rewrite <- (Qmult_assoc v s (/(s * t))) in H1.
  rewrite (qeqT_imp_qeq _ _ (piu1888_inv_mul_swap s t Hs Ht)) in H1.
  rewrite (Qmult_comm s t) in H1.
  rewrite (qeqT_imp_qeq _ _ (piu1888_inv_mul_swap t s Ht Hs)) in H1.
  apply Qle_to_QleT'. exact H1.
Qed.

Lemma piu1888_T0_le : forall n, QleT' ((2#1) * piu1888_T0 n) (piu1888_T0 (S n)).
Proof.
  intros n. apply Qle_to_QleT'. unfold piu1888_T0.
  rewrite (Qmult_assoc (2#1) (piu1888_qfact (2 * n)) (/ (piu1888_qfact n))).
  apply QleT'_to_Qle.
  apply (piu1888_div_le ((2#1) * piu1888_qfact (2 * n)) (piu1888_qfact (2 * S n))
                        (piu1888_qfact n) (piu1888_qfact (S n))).
  - apply QltT_to_Qlt. apply piu1888_qfact_pos.
  - apply QltT_to_Qlt. apply piu1888_qfact_pos.
  - rewrite (qeqT_imp_qeq _ _ (piu1888_T0_prod_step n)).
    apply (Qmult_le_compat_r ((2#1) * piu1888_qfact (2 * n))
             ((2#1) * piu1888_qN (S (2 * n)) * piu1888_qfact (2 * n))
             (piu1888_qfact (S n))).
    + apply (Qmult_le_compat_r (2#1) ((2#1) * piu1888_qN (S (2 * n)))
                                (piu1888_qfact (2 * n))).
      * apply (Qle_trans ((2#1)) ((1#1) * (2#1))
                 ((2#1) * piu1888_qN (S (2 * n)))).
        -- rewrite Qmult_1_l. apply Qle_refl.
        -- rewrite (Qmult_comm (2#1) (piu1888_qN (S (2 * n)))).
           apply (Qmult_le_compat_r (1#1) (piu1888_qN (S (2 * n))) (2#1)).
           ++ exact (QleT'_to_Qle _ _ (piu1888_qN_ge1 (2 * n))).
           ++ vm_compute. discriminate.
      * apply (Qle_trans (0#1) (1#1) (piu1888_qfact (2 * n))).
        -- vm_compute. discriminate.
        -- exact (QleT'_to_Qle _ _ (piu1888_qfact_ge1 (2 * n))).
    + apply Qlt_le_weak; exact (QltT_to_Qlt _ _ (piu1888_qfact_pos _)).
Qed.
