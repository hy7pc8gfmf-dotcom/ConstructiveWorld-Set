(* ConstructiveWorld-Set — positivity of general-order Pade denominator polynomials. *)

(** * UpReqPadeDenPos: Pade denominator positivity for arbitrary order.

    Mission.  For every order [n] and rational [x] in the unit interval,
      [pdp_den_pos : QleT 0 x -> QleT x 1 -> QleT' 0 (pade_den n x)]
      where the denominator is the finite alternating sum with
      [c_k = pade_coeff n k]; the proof assembles termwise decay
      [t (S k) <= t k] from the coefficient ratio and feeds the
      alternating-sum engine [altsum_nonneg_leT].  Supporting laws:
      [pdp_sign_term], [pdp_coeff_pos_any], [pdp_acc_sum], the parity
      closed forms of [q_pow (-1) k], and the [vm_compute]-checked
      instances [pdp_den2_*], [pdp_den3_*].

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].
      Requires [S01_BaseRing]-[S15_TailFEPUp] and the companions
      [UpReqPadeExp], [UpReqAltSumPos], [UpReqPadeQLeg].

    References.  This development, [UpReqPadeDenPos] in
      ConstructiveWorld-Main, the baseline module whose statement
      names are carried over here verbatim (statement-face
      Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]
      (decidable Q-carriers [QltT]/[QleT]/[QleT']/[QeqT], [Id]);
      scope: the unit interval; statements extract with
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPadeDenPos.v]
      compiles cleanly; artifact magic [436f7121 00015ff4]. *)

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
Require Import UpReqPadeExp UpReqAltSumPos.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeDenPosQ.

(* ============ Part 0. Multiplication monotonicity on the statement face ============ *)

Lemma pdp_qmult_le_0 : forall a b : Q,
  QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb.
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat; apply QleT'_to_Qle; assumption.
Qed.

Lemma pdp_qmult_le_compat_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc.
  apply Qle_to_QleT'.
  apply Qmult_le_compat_r; apply QleT'_to_Qle; assumption.
Qed.

Lemma pdp_qmult_le_compat_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc.
  assert (Hr : QleT' (a * c) (b * c))
    by (apply pdp_qmult_le_compat_r; assumption).
  apply Qle_to_QleT'.
  apply (Qle_trans (c * a) (a * c)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_comm.
  - apply (Qle_trans (a * c) (b * c)).
    + apply QleT'_to_Qle. exact Hr.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ============ Part 1. Closed forms of [q_pow (-1) k] by parity ============ *)

Lemma pdp_qpow_neg1_even : forall m : nat, QeqT (q_pow (- 1)%Q (2 * m)%nat) (1%Q).
Proof.
  induction m as [| m IH].
  - reflexivity.
  - apply qeq_imp_qeqT.
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    change (q_pow (- 1)%Q (Datatypes.S (Datatypes.S (2 * m))))
      with ((- 1)%Q * q_pow (- 1)%Q (Datatypes.S (2 * m))).
    change (q_pow (- 1)%Q (Datatypes.S (2 * m)))
      with ((- 1)%Q * q_pow (- 1)%Q (2 * m)).
    rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma pdp_qpow_neg1_odd : forall m : nat, QeqT (q_pow (- 1)%Q (2 * m + 1)%nat) ((- 1)%Q).
Proof.
  intro m. apply qeq_imp_qeqT.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * m + 1)))%nat by lia.
    change (q_pow (- 1)%Q (Datatypes.S (Datatypes.S (2 * m + 1))))
      with ((- 1)%Q * q_pow (- 1)%Q (Datatypes.S (2 * m + 1))).
    change (q_pow (- 1)%Q (Datatypes.S (2 * m + 1)))
      with ((- 1)%Q * q_pow (- 1)%Q (2 * m + 1)).
    rewrite IH. ring.
Qed.

Lemma pdp_sgp_succ_T : forall k : nat,
  altsum_sgp k = true -> @Id bool (altsum_sgp (Datatypes.S k)) false.
Proof.
  intros k H.
  destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (Id_eq _ _ (altsum_peven_eq k Ep)).
    replace (Datatypes.S k)%nat with (2 * altsum_phalf k + 1)%nat by lia.
    exact (match Id_eq _ _ (altsum_sgp_2k1 (altsum_phalf k))
           in (_ = y) return @Id bool (altsum_sgp (2 * altsum_phalf k + 1)) y
           with eq_refl => id_refl end).
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (Id_eq _ _ (altsum_podd_eq k Ep)).
    rewrite Hk in H. rewrite (Id_eq _ _ (altsum_sgp_2k1 (altsum_phalf k))) in H. discriminate H.
Qed.

Lemma pdp_sgp_succ_F : forall k : nat,
  altsum_sgp k = false -> @Id bool (altsum_sgp (Datatypes.S k)) true.
Proof.
  intros k H.
  destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (Id_eq _ _ (altsum_peven_eq k Ep)).
    rewrite Hk in H. rewrite (Id_eq _ _ (altsum_sgp_2k (altsum_phalf k))) in H. discriminate H.
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (Id_eq _ _ (altsum_podd_eq k Ep)).
    replace (Datatypes.S k)%nat
      with (2 * Datatypes.S (altsum_phalf k))%nat by lia.
    exact (match Id_eq _ _ (altsum_sgp_2k (Datatypes.S (altsum_phalf k)))
           in (_ = y) return @Id bool (altsum_sgp (2 * Datatypes.S (altsum_phalf k))) y
           with eq_refl => id_refl end).
Qed.

Lemma pdp_qpow_neg1_sgp : forall k : nat,  
 QeqT (q_pow (- 1)%Q k) (if altsum_sgp k then 1%Q else (- 1)%Q).
Proof.
  intro k. destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (Id_eq _ _ (altsum_peven_eq k Ep)).
    rewrite Hk. rewrite (Id_eq _ _ (altsum_sgp_2k (altsum_phalf k))). apply pdp_qpow_neg1_even.
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (Id_eq _ _ (altsum_podd_eq k Ep)).
    rewrite Hk. rewrite (Id_eq _ _ (altsum_sgp_2k1 (altsum_phalf k))). apply pdp_qpow_neg1_odd.
Qed.

(* Termwise sign absorption: [q_pow (-1) k * g k] equals [g k] on even
   indices and the negation [- g k] on odd ones. *)
Lemma pdp_sign_term : forall (g : nat -> Q) (k : nat),  
 QeqT (q_pow (- 1)%Q k * g k)
 (if altsum_sgp k then g k else Qopp (g k)).
Proof.
  intros g k. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (pdp_qpow_neg1_sgp k)).
  destruct (altsum_sgp k); cbv iota; ring.
Qed.

(* ============ Part 2. Coefficient positivity, unbounded in the index ============ *)

Lemma pdp_coeff_pos_any : forall n k : nat, QltT 0 (pade_coeff n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold pade_coeff. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply q_fact_pos.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
Qed.

(* ============ Part 3. Sum-form lemmas: head folding, range shifting,
   accumulator alignment ============ *)

Lemma pdp_sum_head : forall (f : nat -> Q) (m : nat),  
 QeqT (sum_upto (Datatypes.S m) f)
 (f 0%nat + sum_upto m (fun j : nat => f (Datatypes.S j)%nat)).
Proof.
  intros f m. apply qeq_imp_qeqT. induction m as [| m IH].
  - change (sum_upto (Datatypes.S 0%nat) f) with (0%Q + f 0%nat).
    change (sum_upto 0%nat (fun j : nat => f (Datatypes.S j)%nat)) with 0%Q.
    ring.
  - change (sum_upto (Datatypes.S (Datatypes.S m)) f)
      with (sum_upto (Datatypes.S m) f + f (Datatypes.S m)%nat).
    rewrite IH.
    change (sum_upto (Datatypes.S m) (fun j : nat => f (Datatypes.S j)%nat))
      with (sum_upto m (fun j : nat => f (Datatypes.S j)%nat)
            + f (Datatypes.S m)%nat).
    ring.
Qed.

Lemma pdp_sum_upto_ext_range : forall (m : nat) (f g : nat -> Q),  
 (forall k : nat, (k < m)%nat -> f k == g k) ->   QeqT
 (sum_upto m f) (sum_upto m g).
Proof.
  intros m f g H. induction m as [| m IH].
  - apply qeq_imp_qeqT. reflexivity.
  - assert (IH' : sum_upto m f == sum_upto m g).
    { apply qeqT_imp_qeq. apply IH. intros k Hk. apply H. lia. }
    change (sum_upto (Datatypes.S m) f)
      with (sum_upto m f + f m%nat).
    change (sum_upto (Datatypes.S m) g)
      with (sum_upto m g + g m%nat).
    apply (altsum_qplus_eq_compat _ _ _ _ IH').
    + apply H. lia.
Qed.

(* Alignment between the sign-accumulator recursion [altsum_acc] and
   [sum_upto]: with start index [k] and first sign [sg = altsum_sgp k],
   the two sums agree termwise. *)
Lemma pdp_acc_sum : forall (g : nat -> Q) (n k : nat) (sg : bool),  
 sg = altsum_sgp k ->  
 QeqT (altsum_acc sg g k n)

 (sum_upto n (fun j : nat =>     (if altsum_sgp (k + j)%nat then g (k + j)%nat else Qopp (g (k + j)%nat)))).
Proof.
  intros g n. induction n as [| m IH]; intros k sg Esg.
  - apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (altsum_acc_0_eq sg g k)). reflexivity.
  - destruct sg.
    + assert (Esk : altsum_sgp (Datatypes.S k) = false).
      { assert (Esk' : @Id bool (altsum_sgp (Datatypes.S k)) false)
          by (apply pdp_sgp_succ_T; symmetry; exact Esg).
        exact (match Esk' in (@Id _ _ y)
               return (altsum_sgp (Datatypes.S k) = y)
               with id_refl => eq_refl end). }
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (altsum_acc_T g k m)).
      rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) false (eq_sym Esk))).
      rewrite (qeqT_imp_qeq _ _ (pdp_sum_head _ _)). cbv beta.
      assert (E0 : (if altsum_sgp (k + 0)%nat
                    then g (k + 0)%nat
                    else Qopp (g (k + 0)%nat)) == g k).
      { replace (k + 0)%nat with k%nat by lia.
        rewrite <- Esg. reflexivity. }
      rewrite E0.
      apply (Qeq_trans (g k
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (Datatypes.S k + j)%nat
             then g (Datatypes.S k + j)%nat
             else Qopp (g (Datatypes.S k + j)%nat))))
        (g k
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (k + Datatypes.S j)%nat
             then g (k + Datatypes.S j)%nat
             else Qopp (g (k + Datatypes.S j)%nat))))).
      * apply qeqT_imp_qeq. apply altsum_qplus_eq_compat.
        -- reflexivity.
        -- apply qeqT_imp_qeq. apply sum_upto_ext. intro j. apply qeq_imp_qeqT. cbv beta.
           replace (Datatypes.S k + j)%nat
             with (k + Datatypes.S j)%nat by lia.
           reflexivity.
      * reflexivity.
    + assert (Esk : altsum_sgp (Datatypes.S k) = true).
      { assert (Esk' : @Id bool (altsum_sgp (Datatypes.S k)) true)
          by (apply pdp_sgp_succ_F; symmetry; exact Esg).
        exact (match Esk' in (@Id _ _ y)
               return (altsum_sgp (Datatypes.S k) = y)
               with id_refl => eq_refl end). }
      apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (altsum_acc_F g k m)).
      rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) true (eq_sym Esk))).
      rewrite (qeqT_imp_qeq _ _ (pdp_sum_head _ _)). cbv beta.
      assert (E0 : (if altsum_sgp (k + 0)%nat
                    then g (k + 0)%nat
                    else Qopp (g (k + 0)%nat)) == Qopp (g k)).
      { replace (k + 0)%nat with k%nat by lia.
        rewrite <- Esg. reflexivity. }
      rewrite E0.
      apply (Qeq_trans (Qopp (g k)
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (Datatypes.S k + j)%nat
             then g (Datatypes.S k + j)%nat
             else Qopp (g (Datatypes.S k + j)%nat))))
        (Qopp (g k)
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (k + Datatypes.S j)%nat
             then g (k + Datatypes.S j)%nat
             else Qopp (g (k + Datatypes.S j)%nat))))).
      * apply qeqT_imp_qeq. apply altsum_qplus_eq_compat.
        -- reflexivity.
        -- apply qeqT_imp_qeq. apply sum_upto_ext. intro j. apply qeq_imp_qeqT. cbv beta.
           replace (Datatypes.S k + j)%nat
             with (k + Datatypes.S j)%nat by lia.
           reflexivity.
      * reflexivity.
Qed.

Lemma pdp_altsum_sum : forall (g : nat -> Q) (n : nat),  
 QeqT (altsum g (Datatypes.S n))

 (sum_upto (Datatypes.S n)     (fun j : nat => (if altsum_sgp j then g j else Qopp (g j)))).
Proof.
  intros g n. unfold altsum. apply qeq_imp_qeqT.
  assert (E0 : true = altsum_sgp 0%nat) by reflexivity.
  rewrite (qeqT_imp_qeq _ _ (pdp_acc_sum g (Datatypes.S n) 0%nat true E0)).
  apply qeqT_imp_qeq. apply sum_upto_ext. intro j. apply qeq_imp_qeqT. cbv beta.
  replace (0 + j)%nat with j%nat by lia. reflexivity.
Qed.

(* ============ Part 4. The index-wrapped summand [pdp_g] ============ *)

Definition pdp_g (n : nat) (x : Q) (k : nat) : Q :=
  (if (k <=? n)%nat then pade_coeff n k else 0%Q) * q_pow x k.

Lemma pdp_g_nonneg : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x -> QleT' 0 (pdp_g n x k).
Proof.
  intros n x k Hx. unfold pdp_g.
  destruct (k <=? n)%nat eqn:E.
  - apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    + apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx.
  - apply Qle_to_QleT'.
    apply (Qle_trans 0%Q 0%Q).
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qeq_sym. apply Qmult_0_l.
Qed.

Lemma pdp_g_decay_hi : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x -> (n < Datatypes.S k)%nat ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n x k Hx Hhi. unfold pdp_g.
  assert (E : (Datatypes.S k <=? n)%nat = false)
    by (apply Nat.leb_gt; lia).
  rewrite E.
  apply Qle_to_QleT'.
  apply (Qle_trans (0%Q * q_pow x (Datatypes.S k)) 0%Q).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_0_l.
  - apply QleT'_to_Qle. apply pdp_g_nonneg. exact Hx.
Qed.

(* ============ Part 5. Coefficient ratio and adjacent decay ============

   Core algebra: [c k / c (S k) = (2n-k)(k+1)/(n-k) >= 1] for [k < n];
   at the integer level this is [(n-k) <= (2n-k)(k+1)], i.e. the lemma
   [pql_nat_ratio_mono].  The ratio identity is discharged by [field]. *)

Definition pdp_R (n k : nat) : Q :=
  (Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
  (Z.of_nat (Datatypes.S k) # 1) *
  Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q.

Lemma pdp_ZS1_nz : forall j : nat,
  Not (QeqT (Z.of_nat (Datatypes.S j) # 1) 0%Q).
Proof.
  intros j Heq.
  assert (Hlt : (0 < Z.of_nat (Datatypes.S j) # 1)%Q)
    by (unfold Qlt; simpl; lia).
  apply (False_rect Empty_set).
  apply (Qlt_not_eq 0%Q ((Z.of_nat (Datatypes.S j)) # 1)%Q Hlt).
  apply Qeq_sym. exact (qeqT_imp_qeq _ _ Heq).
Qed.

Lemma pdp_R_ge_1 : forall n k : nat, (k < n)%nat -> QleT' 1 (pdp_R n k).
Proof.
  intros n k Hk.
  assert (Hlit : QleT' ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q)
    (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
      (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul].
    pose proof (ZLeT_drop _ _ (pql_nat_ratio_mono n k Hk)). lia. }
  assert (Hinvpos : QleT' 0
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Ez : Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
               (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) == 1%Q).
  { apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))
      ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      1%Q).
    - ring.
    - apply Qmult_inv_r.
      apply not_eq_sym. apply (Qlt_not_eq 0%Q (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)).
      unfold Qlt. simpl. lia. }
  apply (qleT'_trans 1%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
    (pdp_R n k)).
  - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. exact Ez.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. apply qeq_imp_qeqT. unfold pdp_R. ring.
Qed.

Lemma pdp_coeff_ratio : forall n k : nat, (k < n)%nat ->  
 QeqT (pade_coeff n k) (pade_coeff n (Datatypes.S k) * pdp_R n k).
Proof.
  intros n k Hk.
  unfold pade_coeff, Qdiv, pdp_R. apply qeq_imp_qeqT.
  replace (2 * n - k)%nat
    with (Datatypes.S (2 * n - Datatypes.S k))%nat by lia.
  replace (n - k)%nat
    with (Datatypes.S (n - Datatypes.S k))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ (2 * n - Datatypes.S k)%nat)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ k%nat)).
  rewrite (qeqT_imp_qeq _ _ (q_fact_succ (n - Datatypes.S k)%nat)).
  field.
  all: repeat split.
  all: try solve [apply not_eq_sym; apply (Qlt_not_eq 0%Q _); apply QltT_to_Qlt; apply q_fact_pos
                 | apply not_eq_sym; apply (Qlt_not_eq 0%Q _); unfold Qlt; simpl; lia].
Qed.

Lemma pdp_coeff_decay : forall n k : nat, (k < n)%nat ->
  QleT' (pade_coeff n (Datatypes.S k)) (pade_coeff n k).
Proof.
  intros n k Hk.
  assert (Hpos : QleT' 0 (pade_coeff n (Datatypes.S k))).
  { apply qltT_leT'. apply pdp_coeff_pos_any. }
  apply (qleT'_trans (pade_coeff n (Datatypes.S k))
    (pade_coeff n (Datatypes.S k) * pdp_R n k)
    (pade_coeff n k)).
  - apply (qleT'_trans (pade_coeff n (Datatypes.S k))
      (pade_coeff n (Datatypes.S k) * 1%Q)
      (pade_coeff n (Datatypes.S k) * pdp_R n k)).
    + apply qeq_leT'. apply qeq_imp_qeqT. ring.
    + apply pdp_qmult_le_compat_l.
      * apply pdp_R_ge_1. exact Hk.
      * exact Hpos.
  - exact (qeq_leT' _ _ (qeq_imp_qeqT _ _
             (Qeq_sym _ _ (qeqT_imp_qeq _ _ (pdp_coeff_ratio n k Hk))))).
Qed.

Lemma pdp_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QleT' x 1 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx1.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  apply Qle_to_QleT'.
  assert (Hq : Qle 0 (q_pow x k))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Hx).
  assert (Hc0 : Qle 0 (pade_coeff n k)).
  { apply Qlt_le_weak. apply QltT_to_Qlt. apply pdp_coeff_pos_any. }
  assert (Hin : Qle (x * q_pow x k) (1%Q * q_pow x k)).
  { apply Qmult_le_compat_r.
    - apply QleT'_to_Qle. exact Hx1.
    - exact Hq. }
  assert (Hsc : Qle ((x * q_pow x k) * pade_coeff n k)
                    ((1%Q * q_pow x k) * pade_coeff n k))
    by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                   (pade_coeff n k * (x * q_pow x k))
                   (pade_coeff n k * q_pow x k)).
  - apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                     (pade_coeff n k * q_pow x (Datatypes.S k))
                     (pade_coeff n k * (x * q_pow x k))).
    + apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. apply pdp_coeff_decay. exact Hk.
      * apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
  - apply (Qle_trans (pade_coeff n k * (x * q_pow x k))
                     ((x * q_pow x k) * pade_coeff n k)
                     (pade_coeff n k * q_pow x k)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_comm.
    + apply (Qle_trans ((x * q_pow x k) * pade_coeff n k)
                       ((1%Q * q_pow x k) * pade_coeff n k)
                       (pade_coeff n k * q_pow x k)).
      * exact Hsc.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* ============ Part 6. Denominator expansion and the main theorem ============ *)

Lemma pdp_den_altsum : forall (n : nat) (x : Q),  
 QeqT (pade_den n x) (altsum (pdp_g n x) (Datatypes.S n)).
Proof.
  intros n x. unfold pade_den. apply qeq_imp_qeqT.
  apply (Qeq_trans
    (sum_upto (Datatypes.S n)
       (fun k : nat => q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)))
    (sum_upto (Datatypes.S n)
       (fun k : nat => q_pow (- 1)%Q k * pdp_g n x k))
    (altsum (pdp_g n x) (Datatypes.S n))).
  - apply qeqT_imp_qeq. apply pdp_sum_upto_ext_range. intros k Hk. cbv beta. unfold pdp_g.
    destruct (k <=? n)%nat eqn:E.
    + reflexivity.
    + apply Nat.leb_gt in E. exfalso. lia.
  - apply (Qeq_trans
      (sum_upto (Datatypes.S n)
         (fun k : nat => q_pow (- 1)%Q k * pdp_g n x k))
      (sum_upto (Datatypes.S n)
         (fun k : nat =>
            (if altsum_sgp k then pdp_g n x k else Qopp (pdp_g n x k))))
      (altsum (pdp_g n x) (Datatypes.S n))).
    + apply qeqT_imp_qeq. apply sum_upto_ext. intro k. cbv beta.
      apply pdp_sign_term.
    + apply Qeq_sym. apply qeqT_imp_qeq. apply pdp_altsum_sum.
Qed.

(* Main theorem: [0 <= x <= 1] implies [0 <= pade_den n x] for every
   order [n]; the cases [n = 0] and [n = 1] are covered uniformly. *)
Theorem pdp_den_pos : forall (n : nat) (x : Q),
  QleT 0 x -> QleT x 1 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx1.
  assert (Hxa : QleT' 0 x) by (apply altsum_QleT_to_QleT'; exact Hx0).
  assert (Hxb : QleT' x 1) by (apply altsum_QleT_to_QleT'; exact Hx1).
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by (apply qeqT_imp_qeq; apply pdp_den_altsum).
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdp_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hxa.
        -- exact Hxb.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hxa.
        -- apply Nat.leb_gt in E. lia.
  - exact (qeq_leT' _ _ (qeq_imp_qeqT _ _ (Qeq_sym _ _ Hb))).
Qed.

Corollary pdp_den_pos_lt : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 1 -> QleT' 0 (pade_den n x).
Proof.
  intros n x H0 H1. apply pdp_den_pos.
  - exact H0.
  - left. exact H1.
Qed.

(* ============ Instances: end-to-end checks for [n = 2, 3] by [vm_compute] ============ *)
(* den_2(x) = 1 - x/2 + x^2/12; den_3(x) = 1 - x/2 + x^2/10 - x^3/120 *)

Lemma pdp_den2_three_fifths : QltT 0 (pade_den 2 (3#5)).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den2_one : QleT' 0 (pade_den 2 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den3_one : QleT' 0 (pade_den 3 1%Q).
Proof. vm_compute. reflexivity. Qed.

End PadeDenPosQ.
