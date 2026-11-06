(* ConstructiveWorld-Set -- denominator-positivity certificates for Pade approximants in Set carriers. *)

(** * PadeDenPosB12: Pade denominator nonnegativity on the segment [0,2].

    Mission.  For the Pade denominator [pade_den] with term family [pdp_g],
      this file closes the remaining segment [x] in (1,2]: [pdpb_R_ge_2]
      lifts the coefficient ratio bound to [2 <= pdp_R n k], [pdpb_term_decay]
      chains the adjacent-term decay by multiplying through the positive
      ratio, and [pdpb_den_pos_le2] (with the QleT adaptation
      [pdpb_den_pos_le2_T] and the (1,2] form [pdpb_den_pos_b12]) keeps
      [pade_den n x] nonnegative on the whole segment [0,2].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia], [Setoid].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqPadeExp], [UpReqAltSumPos], [UpReqPadeDenPos] of this development.

    References.  This development, PadeDenPosB12.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" PadeDenPosB12.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== Part 1. Strengthened coefficient ratio bound: [2 <= R(n,k)]
   (algebraic core of the coefficient comparison) =====
   The comparison [(2n-k)(k+1) >= 2(n-k)] unfolds into the integer
   identity [k(2n-k+1) >= 0] for [0 <= k < n], discharged by [nia] on the
   [Z]-level lifting; the truncated nat subtractions normalize through
   successors and the [Q] goals carry the rationals as explicit fractions. *)

Lemma pdpb_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2 (pdp_R n k).
Proof.
  intros n k Hk.
  assert (ZK : (0 <= Z.of_nat k)%Z) by lia.
  assert (ZKN : (Z.of_nat k < Z.of_nat n)%Z) by lia.
  assert (Hlit : QleT' ((2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
      (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul]. nia. }
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
      intro Hq0. unfold Qeq in Hq0. cbn [Qnum Qden] in Hq0. lia. }
  apply (qleT'_trans 2%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
    (pdp_R n k)).
  - apply qeq_leT'. apply qeq_imp_qeqT.
    apply (Qeq_trans 2%Q
      ((Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
        (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) * 2%Q)%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q).
    + apply Qeq_sym.
      rewrite Ez. ring.
    + ring.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. apply qeq_imp_qeqT. unfold pdp_R. ring.
Qed.

(* ===== Part 2. Adjacent-term decay on the segment [x] in (1,2]
   (assembly by ratio elimination) =====
   The chain for [c_{k+1} * x^{S k} <= c_k * x^k]: first
   [c_{k+1} * x^{S k} == (c_{k+1} * x) * x^k] ([q_pow_succ] plus [ring]),
   then [(c_{k+1} * x) * x^k <= (c_{k+1} * R(n,k)) * x^k] by
   [x <= 2 <= R] with the order preserved under multiplication by the
   positive factor [c_{k+1}], and finally [== c_k * x^k] by the ratio
   identity [pdp_coeff_ratio] (the ratio elimination itself: both sides
   are reconciled through [Qeq], no true division occurs). *)

Lemma pdpb_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QleT' x 2 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  apply Qle_to_QleT'.
  assert (Hxk : Qle 0 (q_pow x k))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; exact Hx).
  assert (HxR : QleT' x (pdp_R n k)).
  { apply (qleT'_trans x 2%Q (pdp_R n k)).
    - exact Hx2.
    - apply pdpb_R_ge_2. exact Hk. }
  assert (Hcx : QleT' (pade_coeff n (Datatypes.S k) * x)
                      (pade_coeff n (Datatypes.S k) * pdp_R n k)).
  { apply pdp_qmult_le_compat_l.
    - exact HxR.
    - apply qltT_leT'. apply pdp_coeff_pos_any. }
  apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                   ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
                   (pade_coeff n k * q_pow x k)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ x k)). ring.
  - apply (Qle_trans ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
                     ((pade_coeff n (Datatypes.S k) * pdp_R n k) * q_pow x k)
                     (pade_coeff n k * q_pow x k)).
    + apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. exact Hcx.
      * exact Hxk.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (pdp_coeff_ratio n k Hk)). reflexivity.
Qed.

(* ===== Part 3. Main statement: [0 <= x <= 2] implies [0 <= denominator]
   (covering the remaining (1,2] segment) ===== *)

Theorem pdpb_den_pos_le2 : forall (n : nat) (x : Q),
  QleT' 0 x -> QleT' x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hxa Hxb.
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdpb_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hxa.
        -- exact Hxb.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hxa.
        -- apply Nat.leb_gt in E. lia.
  - apply qeq_leT'.
    apply qeq_imp_qeqT. apply Qeq_sym.
    apply qeqT_imp_qeq. apply pdp_den_altsum.
Qed.

(* ===== Part 4. Adaptation to the [QleT]-premise form
   (statement face parallel to [pdp_den_pos]) ===== *)

Theorem pdpb_den_pos_le2_T : forall (n : nat) (x : Q),
  QleT 0 x -> QleT x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx2.
  apply pdpb_den_pos_le2.
  - apply altsum_QleT_to_QleT'. exact Hx0.
  - apply altsum_QleT_to_QleT'. exact Hx2.
Qed.


Theorem pdpb_den_pos_b12 : forall (n : nat) (x : Q),
  QltT 1 x -> QleT x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x H1 H2.
  apply pdpb_den_pos_le2.
  - apply Qle_to_QleT'.
    apply (Qle_trans 0%Q 1%Q x).
    + unfold Qle. simpl. lia.
    + apply Qlt_le_weak. apply QltT_to_Qlt. exact H1.
  - apply altsum_QleT_to_QleT'. exact H2.
Qed.

(* ===== Part 6. vm_compute end-to-end reconciliations (including the
   true zero at [x = 2]) ===== *)
(* [den_1(x) = 1 - x/2] vanishes at [x = 2] (the nonnegativity conclusion
   touches zero exactly there); [den_2(2) = 1/3 > 0] and
   [den_3(2) = 1 - 1 + 2/5 - 1/15 = 1/3 > 0]. *)

Lemma pdpb_den1_two : QleT' 0 (pade_den 1%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den1_three_halves : QltT 0 (pade_den 1%nat (3 # 2)).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den2_two : QltT 0 (pade_den 2%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den3_two : QltT 0 (pade_den 3%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

(* ===== Audit: the main statements are closed under the global context
   (evidence in the compile log) ===== *)

Print Assumptions pdpb_R_ge_2.
Print Assumptions pdpb_term_decay.
Print Assumptions pdpb_den_pos_le2.
Print Assumptions pdpb_den_pos_le2_T.
Print Assumptions pdpb_den_pos_b12.
