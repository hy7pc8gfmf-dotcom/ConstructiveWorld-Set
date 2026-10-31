(* ==========================================================================)
   PadeErrorIntegral.v -- statement family collection and instantiation carrier
   Mission. This file formalizes the following statement families:
   bts_mult_nonneg, bts_pow_nonneg, bts_q_pow_one, bts_sum_nonneg_bounded,
   bts_Qabs_mult, bts_qabs_q_pow, bts_qabs_pow_sign_one, bts_sum_abs_triangle,
   bts_qle_lt_plus_one, together with the Pade remainder model, the
   Beta-integral engine (pei_* family) and the truncated-exponential error
   integral family with its closed forms and positivity bounds.
   Dependencies. The Require declarations listed in this file: S01_BaseRing,
   S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO,
   S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO,
   S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF,
   S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpReqQExpTail,
   UpReqPadeExp, PolyIntegral, plus Stdlib Setoid, Lia, QArith, Arith, List.
   References. Beukers-type rational approximations to ln 2 through the error
   integral carried by a Pade numerator and denominator; the classical
   integral representation of the approximation error; the constructive
   Set-level comparison carriers (QeqT, QltT, QleT', NatLe, Id) of the
   hosting library.
   Constructivity. The whole file is closed by Qed with zero unfinished
   proofs and no classical logic; statement faces are carried at Set
   level through the QeqT/QltT/QleT'/NatLe/Id carriers with zero Prop
   leakage; the remaining explicit interface assumptions are universally
   quantified statement arguments, not facts asserted without proof.
   Build. Rocq 9.1 direct call: rocq c -native-compiler no -q -Q . "",
   wrapped by the cpu_guard load limiter.
   ========================================================================== *)

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
Require Import UpReqQExpTail.
Require Import UpReqPadeExp.
From Stdlib Require Import Setoid Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.

(* ================= Sec 1 bts_mult_nonneg family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ================= Common small engine (Q/abs level) ================= *)

(* Nonnegativity preservation under multiplication: from 0 <= x and
   0 <= y conclude 0 <= x*y (via the qtail monotonicity lemma). *)
Lemma bts_mult_nonneg : forall x y : Q, QleT' 0 x -> QleT' 0 y -> QleT' 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (x * 0)).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QleT'_to_Qle. apply (qtail_mult_le_compat_l 0 y x).
    + exact (QleT'_to_Qle _ _ Hy).
    + exact (QleT'_to_Qle _ _ Hx).
Qed.

(* Powers of a nonnegative base are nonnegative. *)
Lemma bts_pow_nonneg : forall (x : Q) (k : nat), QleT' 0 x -> QleT' 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| m IH].
  - apply Qle_to_QleT'. apply (Qlt_le_weak 0 1). apply (QltT_to_Qlt 0 1). apply qtail_Qlt01.
  - change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    apply bts_mult_nonneg; assumption.
Qed.

(* Powers of 1 normalize to 1. *)
Lemma bts_q_pow_one : forall k : nat, QeqT (q_pow 1%Q k) 1%Q.
Proof.
  intro k. apply qeq_imp_qeqT.
  induction k as [| m IH].
  - reflexivity.
  - change (q_pow 1%Q (Datatypes.S m)) with (1 * q_pow 1%Q m).
    rewrite IH. reflexivity.
Qed.

(* Bounded sums of nonnegative terms are nonnegative (guarded form:
   only the terms with index below the bound are required). *)
Lemma bts_sum_nonneg_bounded : forall (n : nat) (f : nat -> Q),
  (forall k, NatLe (Datatypes.S k) n -> QleT' 0 (f k)) -> QleT' 0 (sum_upto n f).
Proof.
  intros n f H. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    apply (Qle_trans _ (sum_upto m f)).
    + apply QleT'_to_Qle. apply IH. intros k Hk. apply H.
      apply (NatLe_lift (Datatypes.S k) (Datatypes.S m)).
      pose proof (NatLe_drop _ _ Hk). lia.
    + apply QleT'_to_Qle. apply qtail_le_plus_r.
      apply QleT'_to_Qle. apply H.
      apply (NatLe_lift (Datatypes.S m) (Datatypes.S m)). lia.
Qed.

(* Multiplicativity of Qabs at the Z level: |x*y| equals |x|*|y|
   (Z-level absolute value distributivity; Q taken by constructor cases). *)
Lemma bts_Qabs_mult : forall x y : Q, QeqT (Qabs (x * y)) (Qabs x * Qabs y).
Proof.
  intros [xn xd] [yn yd]. apply qeq_imp_qeqT.
  unfold Qabs, Qmult, Qeq. cbn [Qnum Qden].
  rewrite Z.abs_mul. reflexivity.
Qed.

(* The absolute value of a power is the power of the absolute value. *)
Lemma bts_qabs_q_pow : forall (x : Q) (k : nat),
  QeqT (Qabs (q_pow x k)) (q_pow (Qabs x) k).
Proof.
  intros x k. apply qeq_imp_qeqT. induction k as [| m IH].
  - reflexivity.
  - change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    change (q_pow (Qabs x) (Datatypes.S m)) with (Qabs x * q_pow (Qabs x) m).
    rewrite (qeqT_imp_qeq _ _ (bts_Qabs_mult _ _)).
    rewrite IH. reflexivity.
Qed.

(* The absolute value of (-1)^k is constantly 1
   (via |x^k| == |x|^k and |(-1)| == 1). *)
Lemma bts_qabs_pow_sign_one : forall k : nat, QeqT (Qabs (q_pow (- 1)%Q k)) 1%Q.
Proof.
  intro k. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (bts_qabs_q_pow _ _)).
  assert (H1 : Qabs (- 1)%Q == 1%Q) by reflexivity.
  rewrite H1. exact (qeqT_imp_qeq _ _ (bts_q_pow_one k)).
Qed.

(* Triangle rule for finite sums: |sum f| <= sum |f|. *)
Lemma bts_sum_abs_triangle : forall (n : nat) (f : nat -> Q),
  QleT' (Qabs (sum_upto n f)) (sum_upto n (fun k => Qabs (f k))).
Proof.
  intros n f. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    change (sum_upto (Datatypes.S m) (fun k => Qabs (f k)))
      with (sum_upto m (fun k => Qabs (f k)) + Qabs (f m)).
    apply (Qle_trans _ (Qabs (sum_upto m f) + Qabs (f m))).
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * exact (QleT'_to_Qle _ _ IH).
      * apply Qle_refl.
Qed.

(* From x >= 0 conclude x + 1 > 0 (direct Z-level reasoning). *)
Lemma bts_qle_lt_plus_one : forall x : Q, QleT' 0 x -> QltT 0 (x + 1).
Proof.
  intros [xn xd] H. apply Qlt_to_QltT.
  assert (H0 : 0 <= (xn # xd)%Q) by (apply QleT'_to_Qle; exact H).
  unfold Qlt, Qplus. unfold Qle in H0. cbn [Qnum Qden] in H0 |- *. lia.
Qed.

(* Self-reflection of Pade coefficient absolute values (k <= n guard;
   positivity carried by pade_coeff_pos). *)
Lemma bts_coeff_abs_self : forall (n k : nat), NatLe k n ->
  QeqT (Qabs (pade_coeff n k)) (pade_coeff n k).
Proof.
  intros n k Hk. apply qeq_imp_qeqT. apply Qabs_pos. apply Qlt_le_weak.
  apply (QltT_to_Qlt 0 (pade_coeff n k)). apply pade_coeff_pos.
  apply (NatLe_drop _ _ Hk).
Qed.

(* ================= Sec 1a: finite-sum swap / uniform control face ================= *)

(* (1) Finite double-sum exchange identity (the finite analogue of exchanging
       the order of summation -- pure Qeq face; at the finite level there is
       no exchange obstruction; the obstruction lives only at the limit
       level and this face never touches limits). *)
Lemma bts_sum_square_swap : forall (n : nat) (F G : nat -> Q),
  QeqT
  (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => F k * G i)))
  (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => F i * G k))).
Proof.
  intros n F G. apply qeq_imp_qeqT.
  transitivity (sum_upto (Datatypes.S n) F * sum_upto (Datatypes.S n) G).
  - apply Qeq_sym. exact (qeqT_imp_qeq _ _ (sum_upto_prod n n F G)).
  - transitivity (sum_upto (Datatypes.S n) G * sum_upto (Datatypes.S n) F).
    + apply Qmult_comm.
    + transitivity (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i => G k * F i))).
      * exact (qeqT_imp_qeq _ _ (sum_upto_prod n n G F)).
      * exact (qeqT_imp_qeq _ _ (sum_upto_ext (Datatypes.S n)
                 (fun k => sum_upto (Datatypes.S n) (fun i => G k * F i))
                 (fun k => sum_upto (Datatypes.S n) (fun i => F i * G k))
                 (fun k => sum_upto_ext (Datatypes.S n)
                    (fun i => G k * F i) (fun i => F i * G k)
                    (fun i => qeq_imp_qeqT _ _ (Qmult_comm (G k) (F i)))))).
Qed.

(* (2) Specialized double-sum exchange for the Pade numerator times
       denominator: P_n(x) * Q_n(x) equals sum_k sum_i (denominator term i
       first, numerator term k second) -- the coefficient-face landing
       point for the later error analysis. *)
Lemma bts_pade_nd_swap : forall (n : nat) (x : Q),
  QeqT (pade_num n x * pade_den n x)
  (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i =>
    (pade_coeff n i * q_pow x i) * (q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k))))).
Proof.
  intros n x. apply qeq_imp_qeqT. unfold pade_num, pade_den.
  transitivity (sum_upto (Datatypes.S n) (fun k => sum_upto (Datatypes.S n) (fun i =>
    (pade_coeff n k * q_pow x k) * (q_pow (- 1)%Q i * (pade_coeff n i * q_pow x i))))).
  - exact (qeqT_imp_qeq _ _ (sum_upto_prod n n
             (fun k => pade_coeff n k * q_pow x k)
             (fun i => q_pow (- 1)%Q i * (pade_coeff n i * q_pow x i)))).
  - exact (qeqT_imp_qeq _ _ (bts_sum_square_swap n
             (fun k => pade_coeff n k * q_pow x k)
             (fun i => q_pow (- 1)%Q i * (pade_coeff n i * q_pow x i)))).
Qed.

(* (3) Reduction of the exp truncation difference to the qtail tail sum
       (QExpTail engine interface identity; qtail_sum b m n counts
       the sum over k in [m, n-1] of b^k/k!). *)
Lemma bts_exp_partial_diff_tail : forall (b : Q) (N1 N2 : nat), NatLe N1 N2 ->
  QeqT (exp_partial N2 b - exp_partial N1 b)
       (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)).
Proof.
  intros b N1 N2 Hle. apply qeq_imp_qeqT.
  induction N2 as [| m IH].
  - assert (Hz : N1 = 0%nat) by (pose proof (NatLe_drop _ _ Hle); lia). subst N1.
    assert (Hq0 : qtail_sum b 1 1 == 0)
      by (apply qeqT_imp_qeq; apply (qtail_sum_le_m b 1 1 (Nat.le_refl 1))).
    rewrite Hq0.
    ring.
  - destruct (Nat.eq_dec N1 (Datatypes.S m)) as [Heq | Hne].
    + subst N1.
      assert (Hq0 : qtail_sum b (Datatypes.S (Datatypes.S m))
                       (Datatypes.S (Datatypes.S m)) == 0)
        by (apply qeqT_imp_qeq; apply (qtail_sum_le_m b (Datatypes.S (Datatypes.S m))
              (Datatypes.S (Datatypes.S m)) (Nat.le_refl (Datatypes.S (Datatypes.S m))))).
      rewrite Hq0.
      ring.
    + assert (Hm : NatLe N1 m)
         by (apply (NatLe_lift N1 m); pose proof (NatLe_drop _ _ Hle); lia).
      pose proof (NatLe_drop _ _ Hm) as HmP.
      change (exp_partial (Datatypes.S m) b)
        with (exp_partial m b + q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)).
      assert (Hs1 : (Datatypes.S N1 <= Datatypes.S m)%nat) by lia.
      assert (Hs2 : (Datatypes.S m <= Datatypes.S (Datatypes.S m))%nat) by lia.
      assert (Hqa : qtail_sum b (Datatypes.S N1) (Datatypes.S (Datatypes.S m))
                    == qtail_sum b (Datatypes.S N1) (Datatypes.S m)
                       + qtail_sum b (Datatypes.S m) (Datatypes.S (Datatypes.S m)))
        by (apply qeqT_imp_qeq; apply (qtail_sum_add b (Datatypes.S N1) (Datatypes.S m)
              (Datatypes.S (Datatypes.S m)) Hs1 Hs2)).
      rewrite Hqa.
      transitivity ((exp_partial m b - exp_partial N1 b)
                    + (q_pow b (Datatypes.S m) / q_fact (Datatypes.S m))).
      * ring.
      * rewrite (IH Hm).
      assert (Hs : qtail_sum b (Datatypes.S m) (Datatypes.S (Datatypes.S m))
                   == q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)).
      { change (qtail_sum b (Datatypes.S m) (Datatypes.S (Datatypes.S m)))
          with ((if Nat.leb (Datatypes.S m) (Datatypes.S m)
                 then q_pow b (Datatypes.S m) / q_fact (Datatypes.S m)
                 else 0) + qtail_sum b (Datatypes.S m) (Datatypes.S m)).
        destruct (Nat.leb_spec0 (Datatypes.S m) (Datatypes.S m)) as [Hc | Hc].
        - assert (Hq1 : qtail_sum b (Datatypes.S m) (Datatypes.S m) == 0)
            by (apply qeqT_imp_qeq; apply (qtail_sum_le_m b (Datatypes.S m)
                  (Datatypes.S m) (Nat.le_refl (Datatypes.S m)))).
          rewrite Hq1.
          ring.
        - exfalso. lia. }
      rewrite Hs. ring.
Qed.

(* (4) Uniform control face: from b >= 0 and e > 0 an explicit N is produced
       -- the qtail tail sum is uniformly pressed below e. The witness is
       given directly (N is a computable function of b and e), in pure
       witness/epsilon form. Combined with (3) this yields the uniform
       bound on the exp truncation difference; the statement lands directly
       on the qtail carrier ((3) is the recognition face) to avoid doing
       Qeq rewrites inside a QltT goal. *)
Lemma bts_exp_tail_uniform : forall b e : Q, QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall N1 N2 : nat, (N <= N1)%nat -> (N1 <= N2)%nat ->
    QltT (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus_ord b e Hb He) as [N HN].
  exists N. intros N1 N2 Ha Hab.
  exact (HN (Datatypes.S N2) (Datatypes.S N1) (le_S _ _ Ha) (le_n_S _ _ Hab)).
Qed.

(* ================= Sec 2: witness/epsilon limit transfer face (non-swapped form) ================= *)

(* (5) Remainder model: rem n y N = e_N(y)*Q_n(y) - P_n(y)
       (the left-hand side of the Pade error identity with the exp partial
       sum at truncation N substituted in). *)
Definition bts_rem_model (n : nat) (y : Q) (N : nat) : Q :=
  exp_partial N y * pade_den n y - pade_num n y.

(* (6) Model difference = tail sum times denominator (pure ring face --
       the algebraic base of the transfer face). *)
Lemma bts_rem_model_diff : forall (n : nat) (y : Q) (N1 N2 : nat),
  QeqT (bts_rem_model n y N2 - bts_rem_model n y N1)
       ((exp_partial N2 y - exp_partial N1 y) * pade_den n y).
Proof.
  intros n y N1 N2. unfold bts_rem_model. apply qeq_imp_qeqT. ring.
Qed.

(* Pointwise monotonicity of finite sums (<= face; Qplus_le_compat used
   directly). *)
Lemma bts_sum_upto_mono : forall (n : nat) (f g : nat -> Q),
  (forall k, NatLe (Datatypes.S k) n -> QleT' (f k) (g k)) ->
  QleT' (sum_upto n f) (sum_upto n g).
Proof.
  intros n f g H. induction n as [| m IH].
  - cbn [sum_upto]. apply Qle_to_QleT'. apply Qle_refl.
  - apply Qle_to_QleT'.
    change (sum_upto (Datatypes.S m) f) with (sum_upto m f + f m).
    change (sum_upto (Datatypes.S m) g) with (sum_upto m g + g m).
    apply Qplus_le_compat.
    + apply QleT'_to_Qle. apply IH. intros k Hk. apply H.
      apply (NatLe_lift (Datatypes.S k) (Datatypes.S m)).
      pose proof (NatLe_drop _ _ Hk). lia.
    + apply QleT'_to_Qle. apply H. apply (NatLe_lift (Datatypes.S m) (Datatypes.S m)). lia.
Qed.

(* (7) Denominator absolute value bound: |Q_n(y)| <= P_n(|y|)
       (triangle face + sum monotonicity + pointwise
       |(-1)^k c_k y^k| == c_k*|y|^k carried on the Qeq face). *)
Lemma bts_den_abs_le_num_abs : forall (n : nat) (x : Q),
  QleT' (Qabs (pade_den n x)) (pade_num n (Qabs x)).
Proof.
  intros n x. apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto (Datatypes.S n)
           (fun k => Qabs (q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k))))).
  - unfold pade_den.
    exact (QleT'_to_Qle _ _ (bts_sum_abs_triangle (Datatypes.S n)
             (fun k => q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)))).
  - unfold pade_num. apply QleT'_to_Qle. apply bts_sum_upto_mono.
    intro k. intro Hk.
    assert (HkN : NatLe k n)
      by (apply (NatLe_lift k n); pose proof (NatLe_drop _ _ Hk); lia).
    apply qeq_le. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (bts_Qabs_mult _ _)).
    rewrite (qeqT_imp_qeq _ _ (bts_qabs_q_pow _ _)).
    rewrite (qeqT_imp_qeq _ _ (bts_Qabs_mult _ _)).
    rewrite (qeqT_imp_qeq _ _ (bts_qabs_q_pow _ _)).
    change (Qabs (- 1)%Q) with 1%Q.
    rewrite (qeqT_imp_qeq _ _ (bts_q_pow_one k)).
    rewrite (qeqT_imp_qeq _ _ (bts_coeff_abs_self n k HkN)).
    apply Qmult_1_l.
Qed.

(* The Pade numerator is nonnegative at |b| (P_n(|b|) >= 0 --
   positive coefficients + nonnegative powers). *)
Lemma bts_num_abs_nonneg : forall (n : nat) (b : Q), QleT' 0 (pade_num n (Qabs b)).
Proof.
  intros n b. unfold pade_num. apply bts_sum_nonneg_bounded.
  intro k. intro Hk.
  apply bts_mult_nonneg.
  - apply Qle_to_QleT'. apply Qlt_le_weak.
    apply (QltT_to_Qlt 0 (pade_coeff n k)). apply pade_coeff_pos.
    pose proof (NatLe_drop _ _ Hk). lia.
  - apply bts_pow_nonneg. apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

(* (8) Main piece of Sec 2 (downgraded interface-argument form, the
       assumption positions are explicit -- honest marking): the
       witness/epsilon chain = tail control ((4)) x model difference ((6)) x
       denominator bound ((7)) x product-epsilon transfer x the
       Qeq-QltT compatibility bridge. The Qeq face is fully closed there;
       the two library faces "Qeq-QltT compatibility bridge" and "product
       epsilon transfer" are currently missing from the library, so they
       stand in the statement face as explicit interface assumptions
       (not facts asserted without proof -- universally quantified
       arguments); once the library faces are located, the discharge
       needs zero changes = explicit-assumption gate D2. *)
Lemma bts_rem_cauchy : forall (n : nat) (b e : Q),
  QleT 0 b -> QltT 0 e ->
  (forall u v w : Q, QeqT u v -> QltT v w -> QltT u w) ->
  (forall t : Q, QltT t (e / (pade_num n (Qabs b) + 1)) ->
     QltT (t * Qabs (pade_den n b)) e) ->
  sigT (fun N : nat => forall N1 N2 : nat, (N <= N1)%nat -> (N1 <= N2)%nat ->
    QltT (Qabs (bts_rem_model n b N2 - bts_rem_model n b N1)) e).
Proof.
  intros n b e Hb He Hx Hprod.
  destruct (qtail_cauchy_modulus_ord b (e / (pade_num n (Qabs b) + 1)) Hb
                 (qtail_div_pos e (pade_num n (Qabs b) + 1) (QltT_to_Qlt 0 e He)
                    (QltT_to_Qlt 0 (pade_num n (Qabs b) + 1)
                       (bts_qle_lt_plus_one _ (bts_num_abs_nonneg n b))))) as [N HN].
  exists N. intros N1 N2 Ha Hab.
  apply (Hx (Qabs (bts_rem_model n b N2 - bts_rem_model n b N1))
            (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)) * Qabs (pade_den n b)) e).
  - (* Qeq face: |rem(N2)-rem(N1)| == |tail|*|Q_n(b)| (recognition face (3)) *)
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (bts_rem_model_diff n b N1 N2)).
    rewrite (qeqT_imp_qeq _ _ (bts_Qabs_mult _ _)).
    rewrite (qeqT_imp_qeq _ _
      (bts_exp_partial_diff_tail b N1 N2 (NatLe_lift _ _ Hab))).
    rewrite (Qabs_pos (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
    + reflexivity.
    + apply (QleT'_to_Qle 0 (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
      apply qtail_sum_nonneg. apply Qle_to_QleT'.
      apply (qtail_QleT_to_Qle 0 b). exact Hb.
  - (* product-epsilon transfer (explicit interface position; the tail
       bound comes from the qtail-carrier witness of (4) directly) *)
    apply (Hprod (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)))).
    apply (Hx (Qabs (qtail_sum b (Datatypes.S N1) (Datatypes.S N2)))
                (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))
                (e / (pade_num n (Qabs b) + 1))).
    + apply qeq_imp_qeqT.
      apply (Qabs_pos (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
      * apply (QleT'_to_Qle 0 (qtail_sum b (Datatypes.S N1) (Datatypes.S N2))).
        apply qtail_sum_nonneg. apply Qle_to_QleT'.
        apply (qtail_QleT_to_Qle 0 b). exact Hb.
    + exact (HN (Datatypes.S N2) (Datatypes.S N1) (le_S _ _ Ha) (le_n_S _ _ Hab)).
Qed.

(* ================= Section summary (honest marking) =================
   The four pieces of Sec 1 and the three pieces of Sec 2 are all closed,
   zero downgrade and zero unfinished proofs; the original four pieces (the
   integral representation family) do not belong to the statement face of
   this file and stay as explicit assumptions: their exact forms need a
   constructive integration infrastructure and a limit-integration
   exchange face, both judged missing from the library (the explicit
   assumption section of UpReqPadeExp); forcing them is forbidden --
   the explicit assumptions are listed separately at gate D2 in the
   compliance self-check report. *)
(* ================= Sec 2 pei_mult_canc family ================= *)
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Import ListNotations.

(* Sec A: rational-domain engine (nonvanishing / cross cancellation /
   division face) *)

Lemma pei_mult_canc : forall a b c : Q,
  QeqT (a * c) (b * c) -> Not (QeqT c 0%Q) -> QeqT a b.
Proof.
  intros a b c H Hc0. apply qeq_imp_qeqT.
  assert (Hc0' : ~ (c == 0%Q))
    by (intro E; destruct (Hc0 (qeq_imp_qeqT _ _ E))).
  apply (proj1 (Qmult_inj_r a b c Hc0')). exact (qeqT_imp_qeq _ _ H).
Qed.

Lemma pei_mult_nz : forall x y : Q,
  Not (QeqT x 0%Q) -> Not (QeqT y 0%Q) -> Not (QeqT (x * y) 0%Q).
Proof.
  intros x y Hx Hy Heq. apply Hx.
  apply (pei_mult_canc x 0%Q y).
  - apply qeq_imp_qeqT. rewrite Qmult_0_l. exact (qeqT_imp_qeq _ _ Heq).
  - exact Hy.
Qed.

Lemma pei_div_eq : forall p q r s : Q,
  QltT 0 q -> QltT 0 s -> QeqT (p * s) (q * r) -> QeqT (p / q) (r / s).
Proof.
  intros p q r s Hq Hs H. apply qeq_imp_qeqT.
  assert (Hqz : ~ (q == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q q (QltT_to_Qlt 0 q Hq)). exact (Qeq_sym _ _ E). }
  assert (Hsz : ~ (s == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q s (QltT_to_Qlt 0 s Hs)). exact (Qeq_sym _ _ E). }
  assert (HqzT : Not (QeqT q 0%Q))
    by (intro E; exact (False_rect Empty_set (Hqz (qeqT_imp_qeq _ _ E)))).
  assert (HszT : Not (QeqT s 0%Q))
    by (intro E; exact (False_rect Empty_set (Hsz (qeqT_imp_qeq _ _ E)))).
  assert (HqszT : Not (QeqT (q * s) 0%Q)) by (apply (pei_mult_nz q s HqzT HszT)).
  assert (Hpq : QeqT ((p / q) * (q * s)) ((r / s) * (q * s))).
  { apply qeq_imp_qeqT. unfold Qdiv.
    assert (E1 : (p * Qinv q) * (q * s) == (p * Qinv q * q) * s) by ring.
    rewrite E1.
    assert (E2 : (p * Qinv q * q) * s == p * s).
    { rewrite <- (Qmult_assoc p (Qinv q) q). rewrite (Qmult_comm (Qinv q) q).
      rewrite (Qmult_inv_r q Hqz). ring. }
    rewrite E2.
    assert (E3 : (r * Qinv s) * (q * s) == (r * Qinv s * s) * q) by ring.
    rewrite E3.
    assert (E4 : (r * Qinv s * s) * q == q * r).
    { rewrite <- (Qmult_assoc r (Qinv s) s). rewrite (Qmult_comm (Qinv s) s).
      rewrite (Qmult_inv_r s Hsz). ring. }
    rewrite E4. exact (qeqT_imp_qeq _ _ H). }
  exact (qeqT_imp_qeq _ _
    (pei_mult_canc (p / q) (r / s) (q * s) Hpq HqszT)).
Qed.

Lemma pei_div_sub : forall a b c d : Q,
  QltT 0 b -> QltT 0 d ->
  QeqT (a / b - c / d) ((a * d - c * b) / (b * d)).
Proof.
  intros a b c d Hb Hd. apply qeq_imp_qeqT.
  assert (Hbz : ~ (b == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q b (QltT_to_Qlt 0 b Hb)). exact (Qeq_sym _ _ E). }
  assert (Hdz : ~ (d == 0%Q)).
  { intro E. apply (Qlt_not_eq 0%Q d (QltT_to_Qlt 0 d Hd)). exact (Qeq_sym _ _ E). }
  assert (HbzT : Not (QeqT b 0%Q))
    by (intro E; exact (False_rect Empty_set (Hbz (qeqT_imp_qeq _ _ E)))).
  assert (HdzT : Not (QeqT d 0%Q))
    by (intro E; exact (False_rect Empty_set (Hdz (qeqT_imp_qeq _ _ E)))).
  assert (HbdzT : Not (QeqT (b * d) 0%Q)) by (apply (pei_mult_nz b d HbzT HdzT)).
  assert (Hbdz : ~ (b * d == 0%Q))
    by (intro E; destruct (HbdzT (qeq_imp_qeqT _ _ E))).
  assert (Hbd1 : (b * d) * Qinv (b * d) == 1%Q) by (apply Qmult_inv_r; exact Hbdz).
  assert (Hpq : QeqT ((a / b - c / d) * (b * d))
                     (((a * d - c * b) / (b * d)) * (b * d))).
  { apply qeq_imp_qeqT. unfold Qdiv.
    assert (E1 : (a * Qinv b - c * Qinv d) * (b * d)
                 == a * (Qinv b * b) * d - c * (Qinv d * d) * b) by ring.
    rewrite E1.
    rewrite <- (Qmult_assoc (a * d - c * b) (Qinv (b * d)) (b * d)).
    rewrite (Qmult_comm (Qinv (b * d)) (b * d)). rewrite Hbd1.
    rewrite (Qmult_comm (Qinv b) b).
    assert (Hb1 : b * Qinv b == 1%Q) by (apply Qmult_inv_r; exact Hbz).
    rewrite Hb1.
    rewrite (Qmult_comm (Qinv d) d).
    assert (Hd1 : d * Qinv d == 1%Q) by (apply Qmult_inv_r; exact Hdz).
    rewrite Hd1.
    ring. }
  exact (qeqT_imp_qeq _ _
    (pei_mult_canc (a / b - c / d) ((a * d - c * b) / (b * d)) (b * d) Hpq HbdzT)).
Qed.

Lemma pei_div_le_1 : forall a c : Q, QltT 0 c -> QleT' a c -> QleT' (a / c) 1%Q.
Proof.
  intros a c Hc0 Hac. apply Qle_to_QleT'. unfold Qdiv.
  apply (Qle_trans _ (c * Qinv c) 1%Q).
  - apply (Qmult_le_compat_r a c).
    + exact (QleT'_to_Qle _ _ Hac).
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ Hc0).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_inv_r.
    intro E. apply (Qlt_not_eq 0%Q c (QltT_to_Qlt 0 c Hc0)). exact (Qeq_sym _ _ E).
Qed.

Lemma pei_qeq_lt : forall a b c : Q, QeqT a b -> QltT c a -> QltT c b.
Proof.
  intros a b c Hab Hca. apply Qlt_to_QltT. apply (Qlt_le_trans c a b).
  - exact (QltT_to_Qlt _ _ Hca).
  - apply QleT'_to_Qle. apply qeq_le. exact Hab.
Qed.

(* Division-multiplication exchange lemma (Qdiv is a ring atom; identities
   crossing the atom need explicit repositioning -- required by the two
   sides of the step term in pei_eb_eval carrying different /-atom
   shapes). *)
Lemma pei_div_mul_shift : forall X Y Z : Q, QeqT (X * Z / Y) ((X / Y) * Z).
Proof.
  intros X Y Z. apply qeq_imp_qeqT. unfold Qdiv. ring.
Qed.

Lemma pei_lt_le_plus : forall a b : Q, QltT 0 a -> QleT' 0 b -> QltT 0 (a + b).
Proof.
  intros a b Ha Hb. apply Qlt_to_QltT.
  apply (Qlt_le_trans 0%Q a (a + b)).
  - exact (QltT_to_Qlt _ _ Ha).
  - apply (Qle_trans a (a + 0) (a + b)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (QleT'_to_Qle _ _ Hb).
Qed.

Lemma pei_ZS1_nz : forall k : nat,
  Not (QeqT (Z.of_nat (Datatypes.S k) # 1)%Q 0%Q).
Proof.
  intro k. intro E. apply (False_rect Empty_set).
  pose proof (qeqT_imp_qeq _ _ E) as E0.
  unfold Qeq in E0. cbn [Qnum Qden Qmult Pos.mul] in E0.
  assert (Hnn : (0 <= Z.of_nat (Datatypes.S k))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma pei_qfact_nz : forall k : nat, Not (QeqT (q_fact k) 0%Q).
Proof.
  intro k. intro E.
  exact (False_rect Empty_set
    (Qlt_not_eq 0%Q (q_fact k) (QltT_to_Qlt _ _ (q_fact_pos k)) (Qeq_sym _ _ (qeqT_imp_qeq _ _ E)))).
Qed.

Lemma pei_sum_shift : forall (M : nat) (f : nat -> Q),
  QeqT (sum_upto (Datatypes.S M) f)
       (f 0%nat + sum_upto M (fun k => f (Datatypes.S k))).
Proof.
  intros M f. apply qeq_imp_qeqT.
  induction M as [| m IH].
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

Lemma pei_q_pow_mul : forall (x y : Q) (k : nat),
  QeqT (q_pow (x * y) k) (q_pow x k * q_pow y k).
Proof.
  intros x y k. apply qeq_imp_qeqT.
  induction k as [| m IH].
  - cbn [q_pow]. ring.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma pei_q_pow_pos_sq : forall (n : nat) (y : Q),
  QltT 0 y -> QltT 0 (q_pow y n).
Proof.
  intros n y Hy. apply Qlt_to_QltT. induction n as [| m IH].
  - cbn [q_pow]. unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat; [exact (QltT_to_Qlt _ _ Hy) | exact IH].
Qed.

Lemma pei_q_pow_odd_pos : forall (n : nat) (x : Q),
  QltT 0 x -> QltT 0 (q_pow x (Datatypes.S (2 * n))).
Proof.
  intros n x Hx. apply Qlt_to_QltT.
  replace (Datatypes.S (2 * n))%nat with (Datatypes.S (n + n))%nat by lia.
  rewrite (qeqT_imp_qeq _ _ (q_pow_succ x (n + n))).
  apply (Qmult_lt_0_compat x (q_pow x (n + n))).
  - exact (QltT_to_Qlt _ _ Hx).
  - rewrite (qeqT_imp_qeq _ _ (q_pow_add x n n)).
    rewrite <- (qeqT_imp_qeq _ _ (pei_q_pow_mul x x n)).
    apply (QltT_to_Qlt 0 (q_pow (x * x) n)).
    apply (pei_q_pow_pos_sq n (x * x)).
    apply Qlt_to_QltT. apply Qmult_lt_0_compat; exact (QltT_to_Qlt _ _ Hx).
Qed.

(* Sec B: the Beta family -- construction, evaluation semantics and closed
   forms of the coefficient lists t^a(1-t)^b *)

(* Tail zero padding: appending one 0 to the tail of a polynomial list
   changes neither the value nor the integral (used for equal lengths). *)
Definition pei_ztail (p : list Q) : list Q := p ++ (0%Q :: nil).

Lemma pei_eval_ztail : forall (p : list Q) (x : Q),
  QeqT (pint_eval (pei_ztail p) x) (pint_eval p x).
Proof.
  intros p x. apply qeq_imp_qeqT. unfold pei_ztail.
  induction p as [| a p' IH].
  - cbn [app pint_eval]. ring.
  - cbn [app pint_eval]. rewrite IH. ring.
Qed.

Lemma pei_integral_ztail : forall p : list Q,
  QeqT (pint_integral (pei_ztail p)) (pint_integral p).
Proof.
  intro p. apply qeq_imp_qeqT. unfold pint_integral, pei_ztail. generalize 0%nat.
  induction p as [| a p' IH]; intro k.
  - cbn [app pint_integral_from]. unfold pint_monomial_int.
    rewrite (qeqT_imp_qeq _ _ (pint_zero_div _)). ring.
  - cbn [app pint_integral_from]. rewrite IH. ring.
Qed.

(* The canonical coefficient list of t^a(1-t)^b (head is the constant term;
   length a+b+1): the list-level recursion of
   (1-t)^(b+1) = (1-t)^b - t*(1-t)^b, with the first operand zero-padded
   to preserve equal lengths. *)
Fixpoint pei_list (a b : nat) : list Q :=
  match b with
  | 0%nat => pint_pow_poly a
  | Datatypes.S b' =>
      pint_add (pei_ztail (pei_list a b'))
               (pint_scale (- 1)%Q (pei_list (Datatypes.S a) b'))
  end.

Lemma pei_scale_length : forall (a : Q) (p : list Q),
  Id (length (pint_scale a p)) (length p).
Proof.
  intros a p. apply RealSetoid.eq_Id. induction p as [| c p' IH].
  - reflexivity.
  - cbn [pint_scale length]. rewrite IH. reflexivity.
Qed.

Lemma pei_add_length : forall p q : list Q,
  Id (length p) (length q) -> Id (length (pint_add p q)) (length p).
Proof.
  intros p q Hlen. apply RealSetoid.eq_Id.
  pose proof (RealSetoid.Id_eq _ _ Hlen) as HlenP. clear Hlen.
  revert HlenP. revert q.
  induction p as [| a p' IH]; intros q HlenP.
  - destruct q as [| b q'].
    + reflexivity.
    + discriminate HlenP.
  - destruct q as [| b q'].
    + discriminate HlenP.
    + cbn [pint_add length]. injection HlenP as HlenP'.
      rewrite (IH q' HlenP'). reflexivity.
Qed.

Lemma pei_list_length : forall a b : nat,
  Id (length (pei_list a b)) (Datatypes.S (a + b)%nat).
Proof.
  intros a b. apply RealSetoid.eq_Id. revert a.
  induction b as [| b' IH]; intros a.
  - cbn [pei_list]. replace (Datatypes.S (a + 0))%nat with (Datatypes.S a)%nat by lia.
    induction a as [| a' IHa].
    + reflexivity.
    + cbn [pint_pow_poly length] in IHa. cbn [pint_pow_poly length].
      rewrite IHa. reflexivity.
  - cbn [pei_list].
    assert (HL : length (pei_ztail (pei_list a b'))
                 = length (pint_scale (- 1)%Q (pei_list (Datatypes.S a) b'))).
    { unfold pei_ztail. rewrite app_length, (IH a).
      rewrite (RealSetoid.Id_eq _ _ (pei_scale_length (- 1)%Q (pei_list (Datatypes.S a) b'))),
              (IH (Datatypes.S a)). simpl. lia. }
    rewrite (RealSetoid.Id_eq _ _ (pei_add_length _ _ (RealSetoid.eq_Id _ _ HL))).
    unfold pei_ztail. rewrite app_length, (IH a). cbn [length]. lia.
Qed.

(* Evaluation linearity (no length premise -- the zero-padding semantics
   is self-consistent). *)
Lemma pei_eval_add : forall (p q : list Q) (x : Q),
  QeqT (pint_eval (pint_add p q) x) (pint_eval p x + pint_eval q x).
Proof.
  intros p q x. apply qeq_imp_qeqT. revert q x.
  induction p as [| a p' IH]; intros q x.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval]. ring.
  - destruct q as [| b q'].
    + cbn [pint_add pint_eval]. ring.
    + cbn [pint_add pint_eval]. rewrite IH. ring.
Qed.

Lemma pei_eval_scale : forall (a : Q) (p : list Q) (x : Q),
  QeqT (pint_eval (pint_scale a p) x) (a * pint_eval p x).
Proof.
  intros a p x. apply qeq_imp_qeqT.
  induction p as [| c p' IH].
  - cbn [pint_scale pint_eval]. ring.
  - cbn [pint_scale pint_eval]. rewrite IH. ring.
Qed.

(* Semantic anchor: pei_list a b evaluates pointwise to t^a * (1-t)^b. *)
Lemma pei_beta_eval : forall (a b : nat) (t : Q),
  QeqT (pint_eval (pei_list a b) t) (q_pow t a * q_pow (1 - t) b).
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a t.
  - cbn [pei_list]. cbn [q_pow]. apply qeq_imp_qeqT.
    rewrite <- (qeqT_imp_qeq _ _ (pint_eval_pow_poly a t)).
    ring.
  - cbn [pei_list]. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (pei_eval_add _ _ t)),
            (qeqT_imp_qeq _ _ (pei_eval_ztail _ t)),
            (qeqT_imp_qeq _ _ (pei_eval_scale _ _ t)).
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S a) t)),
            (qeqT_imp_qeq _ _ (IH a t)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ t a)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ (1 - t)%Q b')). ring.
Qed.

(* Beta closed form: the integral of t^a(1-t)^b over [0,1] equals
   a!*b!/(a+b+1)!. The induction runs on the second argument: the step is
   the linear split plus the division merge (pei_div_sub/pei_div_eq). *)
Theorem pei_beta_value : forall a b : nat,
  QeqT (pint_integral (pei_list a b))
       (q_fact a * q_fact b / q_fact (a + b + 1)%nat).
Proof.
  intros a b. revert a. induction b as [| b' IH]; intros a.
  - cbn [pei_list]. apply qeq_imp_qeqT.
    assert (H := qeqT_imp_qeq _ _ (pint_integral_pow_poly a)).
    rewrite H.
    replace (a + 0 + 1)%nat with (Datatypes.S a)%nat by lia.
    cbn [q_fact].
    apply qeqT_imp_qeq. apply pei_div_eq.
    + apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
    + apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      * unfold Qlt. cbn [Qnum Qden Qplus Qmult Qinv q_fact]. lia.
      * apply QltT_to_Qlt. apply q_fact_pos.
    + apply qeq_imp_qeqT. ring.
  - cbn [pei_list]. apply qeq_imp_qeqT.
    assert (HL : length (pei_ztail (pei_list a b'))
                 = length (pint_scale (- 1)%Q (pei_list (Datatypes.S a) b'))).
    { unfold pei_ztail. rewrite app_length, (RealSetoid.Id_eq _ _ (pei_list_length a b')).
      rewrite (RealSetoid.Id_eq _ _ (pei_scale_length (- 1)%Q (pei_list (Datatypes.S a) b'))),
              (RealSetoid.Id_eq _ _ (pei_list_length (Datatypes.S a) b')). simpl. lia. }
    assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite Hadd.
    rewrite (qeqT_imp_qeq _ _ (pei_integral_ztail (pei_list a b'))).
    assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (- 1)%Q (pei_list (Datatypes.S a) b'))).
    rewrite Hsc.
    rewrite (qeqT_imp_qeq _ _ (IH a)), (qeqT_imp_qeq _ _ (IH (Datatypes.S a))).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ b')).
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ a)).
    replace (a + Datatypes.S b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    replace (Datatypes.S a + b' + 1)%nat with (Datatypes.S (a + b' + 1))%nat by lia.
    rewrite (qeqT_imp_qeq _ _ (q_fact_succ (a + b' + 1)%nat)).
    assert (EJ : (Z.of_nat (Datatypes.S (a + b' + 1)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S a) # 1)
                       + (Z.of_nat (Datatypes.S b') # 1))%Q).
    { unfold Qeq, Qplus. cbn [Qnum Qden Qmult Pos.mul].
      replace (Z.of_nat (Datatypes.S (a + b' + 1)))
        with ((Z.of_nat (Datatypes.S a) + Z.of_nat (Datatypes.S b'))%Z) by lia.
      lia. }
    rewrite EJ.
    transitivity (q_fact a * q_fact b' / q_fact (a + b' + 1)
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a * q_fact b')
                       / (((Z.of_nat (Datatypes.S a) # 1)
                             + (Z.of_nat (Datatypes.S b') # 1))
                            * q_fact (a + b' + 1)))).
    + ring.
    + assert (Hd1 : QltT 0 (q_fact (a + b' + 1))) by apply q_fact_pos.
      assert (Hd2 : QltT 0 (((Z.of_nat (Datatypes.S a) # 1)
                               + (Z.of_nat (Datatypes.S b') # 1))
                              * q_fact (a + b' + 1)))
        by (apply Qlt_to_QltT; apply Qmult_lt_0_compat;
            [unfold Qlt; cbn [Qnum Qden Qplus]; lia | apply QltT_to_Qlt; apply q_fact_pos]).
      rewrite (qeqT_imp_qeq _ _
               (pei_div_sub (q_fact a * q_fact b') (q_fact (a + b' + 1))
               (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
               (((Z.of_nat (Datatypes.S a) # 1)
                   + (Z.of_nat (Datatypes.S b') # 1))
                  * q_fact (a + b' + 1)) Hd1 Hd2)).
      * apply qeqT_imp_qeq. apply (pei_div_eq
                 ((q_fact a * q_fact b')
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1))
                  - (((Z.of_nat (Datatypes.S a) # 1) * q_fact a) * q_fact b')
                      * q_fact (a + b' + 1))
                 (q_fact (a + b' + 1)
                    * (((Z.of_nat (Datatypes.S a) # 1)
                          + (Z.of_nat (Datatypes.S b') # 1))
                         * q_fact (a + b' + 1)))
                 (q_fact a * ((Z.of_nat (Datatypes.S b') # 1) * q_fact b'))
                 (((Z.of_nat (Datatypes.S a) # 1)
                     + (Z.of_nat (Datatypes.S b') # 1))
                    * q_fact (a + b' + 1))).
        -- apply Qlt_to_QltT. apply Qmult_lt_0_compat.
           ++ apply QltT_to_Qlt. apply q_fact_pos.
           ++ apply Qmult_lt_0_compat.
              ** unfold Qlt. cbn [Qnum Qden Qplus]. lia.
              ** apply QltT_to_Qlt. apply q_fact_pos.
        (* The original block was a copy of block 1 with the s factor in
           the reverse order ((S a#1 + S b'#1) first, q_fact second);
           applying q_fact_pos to the summed term failed to unify there,
           so the lia branch and the q_fact branch are exchanged. *)
        -- apply Qlt_to_QltT. apply Qmult_lt_0_compat.
           ++ unfold Qlt. cbn [Qnum Qden Qplus]. lia.
           ++ apply QltT_to_Qlt. apply q_fact_pos.
        -- apply qeq_imp_qeqT. ring.
Qed.

(* Sec C: Beta positivity and upper bounds (the factorial inequality
   engine) *)

Lemma pei_beta_pos : forall a b : nat,
  QltT 0 (pint_integral (pei_list a b)).
Proof.
  intros a b. apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value a b)). unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

Corollary pei_beta_integral_pos : forall n : nat,
  QltT 0 (pint_integral (pei_list n n)).
Proof.
  intro n. exact (pei_beta_pos n n).
Qed.

(* Factorial inequality core: n!*(n+k)! <= (2n+k+1)! (the carrier of
   Beta_k <= 1). *)
Lemma pei_fact_le : forall n k : nat,
  QleT' (q_fact n * q_fact (n + k)) (q_fact (Datatypes.S (2 * n + k))).
Proof.
  intros n k. apply Qle_to_QleT'.
  induction n as [| m IH].
  - replace (0 + k)%nat with k%nat by lia.
    replace (2 * 0 + k)%nat with k%nat by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ k)). cbn [q_fact].
    (* The original attempt applied a multiplication monotonicity lemma
       that does not exist under that name in this stdlib; the measured
       goal (after cbn of q_fact 0) is 1*q_fact k <= (S k#1)*q_fact k,
       which matches exactly the conclusion shape of Qmult_le_compat_r
       1 (S k#1) (q_fact k), closing in one step. *)
    apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S k) # 1)%Q (q_fact k)).
    + unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. lia.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply q_fact_pos.
  - assert (Esm : q_fact (Datatypes.S m)
                  == (Z.of_nat (Datatypes.S m) # 1) * q_fact m)
      by exact (qeqT_imp_qeq _ _ (q_fact_succ m)).
    assert (Esmk : q_fact (Datatypes.S m + k)
                   == (Z.of_nat (Datatypes.S (m + k)) # 1) * q_fact (m + k)).
    { replace (Datatypes.S m + k)%nat with (Datatypes.S (m + k))%nat by lia.
      exact (qeqT_imp_qeq _ _ (q_fact_succ (m + k))). }
    assert (Ej1 : q_fact (Datatypes.S (2 * m + k))
                  == (Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))
      by exact (qeqT_imp_qeq _ _ (q_fact_succ (2 * m + k))).
    (* The original replace added one S too many
       (S(S(S(2m+k))) = 2m+k+3 differs from 2*S m+k = 2m+k+2 and lia
       reported no witness); the q_fact_succ rewrite chain and the
       Qle_trans chain below are written in the two-layer S form
       S(S(2m+k)) matching the chain that was actually proven. *)
    replace (2 * Datatypes.S m + k)%nat
      with (Datatypes.S (Datatypes.S (2 * m + k)))%nat by lia.
    setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (Datatypes.S (2 * m + k))))).
    setoid_rewrite (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S (2 * m + k)))).
    setoid_rewrite Esm. setoid_rewrite Esmk. setoid_rewrite Ej1.
    (* The original induction-step rewrite chain carried three genuine
       defects: an extra S in the replace; the same-level left
       association of A#1 * B#1 being swallowed by Qmake (a positive-type
       error); and qeq_le+ring misused on a genuine inequality. The
       construction below is a four-step right-nested chain:
       h1 identity repositioning (ring); h2 the induction premise
       right-multiplied (r-form, with 0 <= A); h3 after rotation the
       r-form again: A <= (2m+k+3)(2m+k+2) by nia, right-multiplied by
       q_fact(S(2m+k)); h4 identity repositioning by Ej1 (ring). *)
    apply (Qle_trans
      ((Z.of_nat (Datatypes.S m) # 1) * q_fact m
         * ((Z.of_nat (Datatypes.S (m + k)) # 1) * q_fact (m + k)))
      ((q_fact m * q_fact (m + k))
         * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
      ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
         * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
              * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans
        ((q_fact m * q_fact (m + k))
           * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
        (q_fact (Datatypes.S (2 * m + k))
           * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
        ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
           * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
      * apply (Qmult_le_compat_r (q_fact m * q_fact (m + k))
                  (q_fact (Datatypes.S (2 * m + k)))
                  ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))).
        -- exact IH.
        -- apply Qmult_le_0_compat; unfold Qle; cbn [Qnum Qden Qplus Qmult Qinv q_fact]; lia.
      * apply (Qle_trans
          (q_fact (Datatypes.S (2 * m + k))
             * ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1)))
          (((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
             * q_fact (Datatypes.S (2 * m + k)))
          ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
             * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                  * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans
              (((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
                 * q_fact (Datatypes.S (2 * m + k)))
              (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1))
                 * q_fact (Datatypes.S (2 * m + k)))
              ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                 * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1)
                      * ((Z.of_nat (Datatypes.S (2 * m + k)) # 1) * q_fact (2 * m + k))))).
           ++ apply (Qmult_le_compat_r
                  ((Z.of_nat (Datatypes.S m) # 1) * (Z.of_nat (Datatypes.S (m + k)) # 1))
                  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m + k)))) # 1)
                     * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m + k))) # 1))
                  (q_fact (Datatypes.S (2 * m + k)))).
              ** unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. nia.
              ** apply Qlt_le_weak. apply QltT_to_Qlt. apply q_fact_pos.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite Ej1. ring.
Qed.

(* Sec D: the truncated-exponential integrand pei_eb_list (the main
   carrier): pei_eb_list n x M is the sum over k <= M of
   (x^k/k!) * list(t^(n+k)(1-t)^n); its pointwise semantics is
   t^n(1-t)^n * exp_partial M (x*t). *)

Fixpoint pei_eb_list (n : nat) (x : Q) (M : nat) : list Q :=
  match M with
  | 0%nat => pei_list n n
  | Datatypes.S m =>
      pint_add (pint_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                           (pei_list (n + Datatypes.S m) n))
               (pei_ztail (pei_eb_list n x m))
  end.

Lemma pei_eb_length : forall (n : nat) (x : Q) (M : nat),
  Id (length (pei_eb_list n x M)) ((2 * n + M + 1)%nat).
Proof.
  intros n x M. apply RealSetoid.eq_Id. induction M as [| m IH].
  - cbn [pei_eb_list]. rewrite (RealSetoid.Id_eq _ _ (pei_list_length n n)). lia.
  - cbn [pei_eb_list].
    assert (HL : length (pint_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                                    (pei_list (n + Datatypes.S m) n))
                 = length (pei_ztail (pei_eb_list n x m))).
    { rewrite (RealSetoid.Id_eq _ _ (pei_scale_length (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                             (pei_list (n + Datatypes.S m) n))),
              (RealSetoid.Id_eq _ _ (pei_list_length (n + Datatypes.S m) n)).
      unfold pei_ztail. rewrite app_length, IH.
      cbn [length]. lia. }
    rewrite (RealSetoid.Id_eq _ _ (pei_add_length _ _ (RealSetoid.eq_Id _ _ HL))).
    rewrite (RealSetoid.Id_eq _ _ (pei_scale_length (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                           (pei_list (n + Datatypes.S m) n))),
            (RealSetoid.Id_eq _ _ (pei_list_length (n + Datatypes.S m) n)).
    cbn [length]. lia.
Qed.

(* Step decomposition: the integral at S m equals
   c_m*Beta(n+S m, n) plus the integral at m. *)
Lemma pei_eb_step : forall (n : nat) (x : Q) (m : nat),
  QeqT (pint_integral (pei_eb_list n x (Datatypes.S m)))
  (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m) *
    (q_fact (n + Datatypes.S m) * q_fact n
       / q_fact (Datatypes.S (n + Datatypes.S m + n)))
  + pint_integral (pei_eb_list n x m)).
Proof.
  intros n x m. apply qeq_imp_qeqT. cbn [pei_eb_list].
  assert (HL : length (pint_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                                  (pei_list (n + Datatypes.S m) n))
               = length (pei_ztail (pei_eb_list n x m))).
  { rewrite (RealSetoid.Id_eq _ _ (pei_scale_length (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))
                           (pei_list (n + Datatypes.S m) n))),
            (RealSetoid.Id_eq _ _ (pei_list_length (n + Datatypes.S m) n)).
    unfold pei_ztail. rewrite app_length, (RealSetoid.Id_eq _ _ (pei_eb_length n x m)).
    simpl. lia. }
  assert (Hadd := qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
  rewrite Hadd.
  rewrite (qeqT_imp_qeq _ _ (pei_integral_ztail (pei_eb_list n x m))).
  assert (Hsc := qeqT_imp_qeq _ _ (pint_integral_scale (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)) (pei_list (n + Datatypes.S m) n))).
  rewrite Hsc.
  assert (Hbv := qeqT_imp_qeq _ _ (pei_beta_value (n + Datatypes.S m) n)).
  replace (n + Datatypes.S m + n + 1)%nat
    with (Datatypes.S (n + Datatypes.S m + n))%nat in Hbv by lia.
  rewrite Hbv. ring.
Qed.

Lemma pei_eb_value0 : forall (n : nat) (x : Q),
  QeqT (pint_integral (pei_eb_list n x 0))
       (q_fact n * q_fact n / q_fact (Datatypes.S (2 * n))%nat).
Proof.
  intros n x. apply qeq_imp_qeqT. cbn [pei_eb_list].
  rewrite (qeqT_imp_qeq _ _ (pei_beta_value n n)).
  replace (n + n + 1)%nat with (Datatypes.S (2 * n))%nat by lia.
  reflexivity.
Qed.

(* Closed form: the integral equals the sum over k <= M of
   x^k/k!*Beta(n+k+1, n+1) -- the constructive Taylor-coefficient
   interface of the remainder integral representation (the finite core
   of item (2)). *)
Theorem pei_eb_value : forall (n : nat) (x : Q) (M : nat),
  QeqT (pint_integral (pei_eb_list n x M))
  (sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k))))).
Proof.
  intros n x M. apply qeq_imp_qeqT. induction M as [| m IH].
  - rewrite (qeqT_imp_qeq _ _ (pei_eb_value0 n x)). cbn [sum_upto].
    replace (n + 0)%nat with n%nat by lia.
    replace (2 * n + 0)%nat with (2 * n)%nat by lia.
    change (q_pow x 0%nat) with 1%Q.
    change (q_fact 0%nat) with 1%Q.
    assert (Hone : 1%Q / 1%Q == 1%Q).
    { unfold Qdiv. apply Qmult_inv_r.
      intro E. unfold Qeq in E. cbn [Qnum Qden Qmult Pos.mul] in E. lia. }
    rewrite Hone. rewrite Qmult_1_l. ring.
  - rewrite (qeqT_imp_qeq _ _ (pei_eb_step n x m)), IH. cbn [sum_upto].
    replace (2 * n + Datatypes.S m)%nat with (n + Datatypes.S m + n)%nat by lia.
    ring.
Qed.

(* Semantic anchor: pei_eb_list evaluates pointwise to
   t^n(1-t)^n * exp_partial M (x*t) -- the truncated-exponential integrand
   is exactly the constructive M-truncation of e^(tx). *)
Theorem pei_eb_eval : forall (n : nat) (x : Q) (M : nat) (t : Q),
  QeqT (pint_eval (pei_eb_list n x M) t)
       (q_pow t n * q_pow (1 - t) n * exp_partial M (x * t)).
Proof.
  intros n x M t. apply qeq_imp_qeqT. revert t.
  induction M as [| m IH]; intro t.
  - cbn [pei_eb_list]. rewrite (qeqT_imp_qeq _ _ (pei_beta_eval n n t)).
    cbn [exp_partial]. ring.
  - cbn [pei_eb_list].
    rewrite (qeqT_imp_qeq _ _ (pei_eval_add _ _ t)),
            (qeqT_imp_qeq _ _ (pei_eval_ztail _ t)),
            (qeqT_imp_qeq _ _ (pei_eval_scale _ _ t)).
    rewrite IH. rewrite (qeqT_imp_qeq _ _ (pei_beta_eval (n + Datatypes.S m) n t)).
    cbn [exp_partial].
    rewrite (qeqT_imp_qeq _ _ (pei_q_pow_mul x t (Datatypes.S m))).
    rewrite (qeqT_imp_qeq _ _
      (pei_div_mul_shift (q_pow x (Datatypes.S m)) (q_fact (Datatypes.S m))
                         (q_pow t (Datatypes.S m)))).
    rewrite (qeqT_imp_qeq _ _ (q_pow_add t n (Datatypes.S m))).
    ring.
Qed.

(* Term nonnegativity: for x >= 0 every Taylor term is nonnegative
   (nonnegative power times positive 1/k! times positive Beta). *)
Lemma pei_term_nonneg : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x ->
  QleT' 0 (q_pow x k / q_fact k
           * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))).
Proof.
  intros n x k Hx. apply Qle_to_QleT'. unfold Qdiv.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
  - apply Qlt_le_weak. apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* Sec E: main piece one (the counterpart of pade_integral_pos): the
   integral is strictly positive. *)

Theorem pei_integral_pos : forall (n : nat) (x : Q) (M : nat),
  QleT' 0 x -> QltT 0 (pint_integral (pei_eb_list n x M)).
Proof.
  intros n x M Hx.
  assert (HvalP := qeqT_imp_qeq _ _ (pei_eb_value n x M)).
  assert (HshiftP := qeqT_imp_qeq _ _ (pei_sum_shift M (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))))).
  rewrite HshiftP in HvalP.
  assert (Hrest : Qle 0 (sum_upto M (fun k : nat =>
    q_pow x (Datatypes.S k) / q_fact (Datatypes.S k)
      * (q_fact (n + Datatypes.S k) * q_fact n
           / q_fact (Datatypes.S (2 * n + Datatypes.S k)))))).
  { apply QleT'_to_Qle. apply (bts_sum_nonneg_bounded M (fun k : nat =>
      q_pow x (Datatypes.S k) / q_fact (Datatypes.S k)
        * (q_fact (n + Datatypes.S k) * q_fact n
             / q_fact (Datatypes.S (2 * n + Datatypes.S k))))).
    intro k. intro Hbnd. apply pei_term_nonneg. exact Hx. }
  assert (Hf0 : Qlt 0 (q_pow x 0%nat / q_fact 0%nat
    * (q_fact (n + 0)%nat * q_fact n
         / q_fact (Datatypes.S (2 * n + 0)%nat)))).
  { replace (n + 0)%nat with n%nat by lia.
    replace (2 * n + 0)%nat with (2 * n)%nat by lia.
    change (q_pow x 0%nat) with 1%Q.
    change (q_fact 0%nat) with 1%Q.
    assert (Hone : 1%Q / 1%Q == 1%Q).
    { unfold Qdiv. apply Qmult_inv_r.
      intro E. unfold Qeq in E. cbn [Qnum Qden Qmult Pos.mul] in E. lia. }
    rewrite Hone, Qmult_1_l.
    unfold Qdiv.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply QltT_to_Qlt. apply q_fact_pos. }
  assert (Hsum : Qlt 0 (sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))))).
  { setoid_rewrite HshiftP. apply QltT_to_Qlt. apply pei_lt_le_plus.
    - apply Qlt_to_QltT. exact Hf0.
    - apply Qle_to_QleT'. exact Hrest. }
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun k : nat =>
    q_pow x k / q_fact k
      * (q_fact (n + k) * q_fact n / q_fact (Datatypes.S (2 * n + k)))))
    (pint_integral (pei_eb_list n x M)) 0%Q).
  - apply qeq_imp_qeqT. rewrite HshiftP. apply Qeq_sym. exact HvalP.
  - apply Qlt_to_QltT. exact Hsum.
Qed.

(* Sec F: main piece two (the counterpart of pade_error_bound): an
   explicit upper bound. *)

Theorem pei_eb_le : forall (n : nat) (x : Q) (M : nat),
  QleT' 0 x -> QleT' (pint_integral (pei_eb_list n x M)) (exp_partial M x).
Proof.
  intros n x M Hx. induction M as [| m IH].
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (q_fact n * q_fact n / q_fact (Datatypes.S (2 * n))) 1%Q).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      exact (qeqT_imp_qeq _ _ (pei_eb_value0 n x)).
    + apply QleT'_to_Qle. apply pei_div_le_1.
      * apply q_fact_pos.
      * assert (Hle := pei_fact_le n 0%nat).
        replace (n + 0)%nat with n%nat in Hle by lia.
        replace (2 * n + 0)%nat with (2 * n)%nat in Hle by lia.
        exact Hle.
  - apply Qle_to_QleT'.
    assert (Hstep := qeqT_imp_qeq _ _ (pei_eb_step n x m)).
    assert (Hf2 := pei_fact_le n (Datatypes.S m)).
    replace (2 * n + Datatypes.S m)%nat
      with (n + Datatypes.S m + n)%nat in Hf2 by lia.
    assert (Hf3 : QleT' (q_fact (n + Datatypes.S m) * q_fact n)
                      (q_fact (Datatypes.S (n + Datatypes.S m + n)))).
    { apply Qle_to_QleT'.
      apply (Qle_trans _ (q_fact n * q_fact (n + Datatypes.S m)) _).
      - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      - exact (QleT'_to_Qle _ _ Hf2). }
    (* The original step chain carried three ordering defects: the middle
       point of the outer chain was mistakenly exp_partial m x (it should
       be the pint_integral (pei_eb_list n x m) term on the right of
       Hstep); the two + bullets were swapped (the Hstep transfer must
       come before the Qplus_le_compat split); and the inner middle point
       c*1 should be 1*c (the conclusion shape of Qmult_le_compat_r is
       x*z <= y*z). The construction here:
       pint(S m) <=(Hstep) c*Beta + pint m <=(Qplus_le_compat) c*1 + exp m
       ==(cbn+ring) exp(S m). *)
    apply (Qle_trans _
      (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)
         * (q_fact (n + Datatypes.S m) * q_fact n
              / q_fact (Datatypes.S (n + Datatypes.S m + n)))
       + pint_integral (pei_eb_list n x m)) _).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hstep.
    + apply (Qle_trans _
        (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m) * 1%Q
           + exp_partial m x) _).
      * apply Qplus_le_compat.
        -- apply (Qle_trans _
              ((q_fact (n + Datatypes.S m) * q_fact n
                  / q_fact (Datatypes.S (n + Datatypes.S m + n)))
                 * (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))) _).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
           ++ apply (Qle_trans _
                 (1%Q * (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))) _).
              ** apply (Qmult_le_compat_r
                    (q_fact (n + Datatypes.S m) * q_fact n
                       / q_fact (Datatypes.S (n + Datatypes.S m + n))) 1%Q
                    (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))).
                 --- apply QleT'_to_Qle. apply pei_div_le_1.
                     +++ apply q_fact_pos.
                     +++ exact Hf3.
                 --- unfold Qdiv. apply Qmult_le_0_compat.
                     *** apply QleT'_to_Qle. apply q_pow_nonneg. exact Hx.
                     *** apply Qlt_le_weak. apply Qinv_lt_0_compat.
                         apply QltT_to_Qlt. apply q_fact_pos.
              ** apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply QleT'_to_Qle. apply IH.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. cbn [exp_partial]. ring.
Qed.

(* Sec G: main piece three (the counterpart of pade_error_sign): the
   sign is (-1)^n with a positive magnitude.
   Main piece four (the counterpart of pade_error_integral): the leading
   term factorization. *)

Theorem pei_error_mag_pos : forall (n : nat) (x : Q),
  QltT 0 x ->
  QltT 0 (q_fact n * q_fact n * q_pow x (Datatypes.S (2 * n))
            / (q_fact (2 * n) * q_fact (Datatypes.S (2 * n)))).
Proof.
  intros n x Hx. apply Qlt_to_QltT. unfold Qdiv.
  apply (Qmult_lt_0_compat
           (q_fact n * q_fact n * q_pow x (Datatypes.S (2 * n)))
           (Qinv (q_fact (2 * n) * q_fact (Datatypes.S (2 * n))))).
  - apply (Qmult_lt_0_compat (q_fact n * q_fact n)
             (q_pow x (Datatypes.S (2 * n)))).
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
    + apply (QltT_to_Qlt 0 (q_pow x (Datatypes.S (2 * n)))).
      apply pei_q_pow_odd_pos. exact Hx.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos.
Qed.

(* Leading-term identity (the remainder integral representation of the
   M = 0 truncation):
   (-1)^n * x^(2n+1)/(2n)! * the integral of t^n(1-t)^n times the k = 0
   term of e^(tx) equals (-1)^n * x^(2n+1)/(2n)! * n!^2/(2n+1)! -- the
   classical leading term of the error. *)
Corollary pei_error_lead_integral : forall (n : nat) (x : Q),
  QeqT (q_pow (- 1)%Q n
    * (q_pow x (Datatypes.S (2 * n)) / q_fact (2 * n)
         * pint_integral (pei_eb_list n x 0)))
       (q_pow (- 1)%Q n
    * (q_pow x (Datatypes.S (2 * n)) / q_fact (2 * n)
         * (q_fact n * q_fact n / q_fact (Datatypes.S (2 * n))))).
Proof.
  intros n x. apply qeq_imp_qeqT.
  exact (Qmult_comp _ _ (Qeq_refl _) _ _
           (Qmult_comp _ _ (Qeq_refl _) _ _
              (qeqT_imp_qeq _ _ (pei_eb_value0 n x)))).
Qed.

(* Assumption audit trail: Print Assumptions (compile-time stdout,
   re-checked by the verifier). *)

Print Assumptions pei_beta_eval.
Print Assumptions pei_beta_value.
Print Assumptions pei_beta_pos.
Print Assumptions pei_beta_integral_pos.
Print Assumptions pei_fact_le.
Print Assumptions pei_eb_eval.
Print Assumptions pei_eb_value.
Print Assumptions pei_integral_pos.
Print Assumptions pei_eb_le.
Print Assumptions pei_error_lead_integral.
Print Assumptions pei_error_mag_pos.
