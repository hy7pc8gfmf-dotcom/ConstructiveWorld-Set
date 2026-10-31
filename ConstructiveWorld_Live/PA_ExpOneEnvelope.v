(* ==========================================================================)
   PA_ExpOneEnvelope - PA assembly entry of the ExpOneEnvelope family: the
   QltT' bridge, the factorial and partial-sum monotone positivity family,
   the explicit tail bound |S_n - S_m| <= 2/m!, the rational two-sided
   interval for e = sum 1/k!, and the extractable sigT Cauchy modulus.

   (** * PA_ExpOneEnvelope: PA entry re-assembly of the ExpOneEnvelope family.

    Mission. Carry the registered family forms of ExpOneEnvelope.v Sections
    0-6 into the PA entry: QltT' exit bridge, factorial and partial-sum
    monotonicity, explicit tail bound, two-sided interval, Cauchy modulus.

    Dependencies. S01_BaseRing through S15_TailFEPUp (15 in-tree modules),
    plus stdlib QArith, Qabs, Qround, ZArith, Arith, Bool, List, Setoid,
    Morphisms, Lia, QArith.Qminmax.

    References. ConstructiveWorld_Live/ExpOneEnvelope.v Sections 0-6:
    statement faces, bridge-wrapped proofs and comments carried verbatim
    from the registered family forms (same bridge trio as PiEnvelope.v).

    Constructivity. Statements are Set-carried (QltT'/QltT/QleT'/QeqT/
    NatLe/sigT); proofs are Qed-closed, Print Assumptions reports Closed
    under the global context; premise-position Prop carriers of the three
    mixed stations are kept verbatim per the registered family forms.

    Build. Rocq 9.1: rocq c -native-compiler no -q -Q . "" inside the seat
    world (S01-S15 .vo chain); extraction probe reports Obj.magic = 0.
 *)
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* ===== Section 0. Set-level exit: QltT' (Id-of-bool reflection form) ===== *)
(* ============================================================ *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> QltT x y.
Proof. intros x y H. exact H. Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  exact (Qle_to_QleT' a c (Qle_trans a b c H (QleT'_to_Qle _ _ (qeq_le b c (qeq_imp_qeqT _ _ Hbc))))).
Qed.

(* ============================================================ *)
(* ===== Section 1. Small order/equality bridges: transport, monotonicity, inversion ===== *)
(* ============================================================ *)

(* ---- Qeq transport left: x == y -> y < z -> x < z ---- *)
Lemma eoe_lt_eq_l : forall x y z : Q, x == y -> Qlt y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. apply Qlt_to_QltT.
  exact (Qle_lt_trans x y z (QleT'_to_Qle _ _ (qeq_le x y (qeq_imp_qeqT _ _ Hxy))) Hyz).
Qed.

(* ---- Qeq transport right: x < y -> y == z -> x < z ---- *)
Lemma eoe_lt_eq_r : forall x y z : Q, Qlt x y -> y == z -> QltT x z.
Proof.
  intros x y z Hxy Hyz.
  apply Qlt_to_QltT.
  exact (Qlt_le_trans x y z Hxy (QleT'_to_Qle _ _ (qeq_le y z (qeq_imp_qeqT _ _ Hyz)))).
Qed.

(* ---- Left multiplication monotonicity (term-order bridge: u*v <= u*w) ---- *)
Lemma eoe_mult_le_l : forall u v w : Q, Qle v w -> Qle 0 u -> QleT' (u * v) (u * w).
Proof.
  intros u v w Hvw Hu.
  apply Qle_to_QleT'.
  exact (Qle_trans (u * v) (v * u) (u * w)
           (QleT'_to_Qle _ _ (qeq_le (u * v) (v * u) (qeq_imp_qeqT _ _ (Qmult_comm u v))))
           (Qle_trans (v * u) (w * u) (u * w)
              (Qmult_le_compat_r v w u Hvw Hu)
              (QleT'_to_Qle _ _ (qeq_le (w * u) (u * w) (qeq_imp_qeqT _ _ (Qmult_comm w u)))))).
Qed.

(* ---- Inversion antitone (Qle form): 0 < x -> 0 < y -> y <= x -> /x <= /y ---- *)
Lemma eoe_qinv_le : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qle y x -> QleT' (/ x) (/ y).
Proof.
  intros x y Hx Hy Hyx.
  apply Qle_to_QleT'.
  destruct (Qle_lt_or_eq y x Hyx) as [Hlt | Heq].
  - exact (Qlt_le_weak (/ x) (/ y) (proj1 (Qinv_lt_contravar y x Hy Hx) Hlt)).
  - rewrite Heq. exact (Qle_refl (/ x)).
Qed.

(* ---- Division monotone (Qle form): fixed numerator, positive denominators ---- *)
Lemma eoe_div_le : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qle z y -> QleT' (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  apply Qle_to_QleT'.
  exact (Qle_trans (a / y) (/ y * a) (a / z)
           (QleT'_to_Qle _ _ (qeq_le (a / y) (/ y * a) (qeq_imp_qeqT _ _ (Qmult_comm a (/ y)))))
           (Qle_trans (/ y * a) (/ z * a) (a / z)
              (Qmult_le_compat_r (/ y) (/ z) a (QleT'_to_Qle _ _ (eoe_qinv_le y z Hy Hz Hzy))
                 (Qlt_le_weak 0 a Ha))
              (QleT'_to_Qle _ _ (qeq_le (/ z * a) (a / z) (qeq_imp_qeqT _ _ (Qmult_comm (/ z) a)))))).
Qed.

(* ---- Division monotone (Qlt form): strict version ---- *)
Lemma eoe_div_lt : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qlt z y -> QltT (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  exact (eoe_lt_eq_l (a / y) (/ y * a) (a / z)
           (Qmult_comm a (/ y))
           (QltT_to_Qlt _ _ (eoe_lt_eq_r (/ y * a) (/ z * a) (a / z)
              (Qmult_lt_compat_r (/ y) (/ z) a Ha
                 (proj1 (Qinv_lt_contravar z y Hz Hy) Hzy))
              (Qmult_comm (/ z) a)))).
Qed.

(* ============================================================ *)
(* ===== Section 2. Factorial order structure (monotone, positive, >= max(1,n)) ===== *)
(* ============================================================ *)

Lemma eoe_fact_ge_one : forall k : nat, QleT' (1%Q) (q_fact k).
Proof.
  intro k.
  apply Qle_to_QleT'.
  induction k as [| k IH].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1))).
    + unfold Qle. simpl. lia.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * (1%Q))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
        -- apply QleT'_to_Qle. apply eoe_mult_le_l.
           ++ exact IH.
           ++ unfold Qle. simpl. lia.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma eoe_fact_ge_self : forall k : nat, QleT' (Z.of_nat k # 1) (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'. destruct k as [| j].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * (1%Q))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      * apply QleT'_to_Qle. apply eoe_mult_le_l.
        -- exact (QleT'_to_Qle _ _ (eoe_fact_ge_one j)).
        -- unfold Qle. simpl. lia.
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma eoe_fact_step_ge : forall k : nat, QleT' (q_fact k) (q_fact (Datatypes.S k)).
Proof.
  intro k.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
  - apply (Qle_trans _ (q_fact k * (Z.of_nat (Datatypes.S k) # 1))).
    + apply (Qle_trans _ (q_fact k * 1%Q)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply QleT'_to_Qle. apply eoe_mult_le_l.
        -- unfold Qle. simpl. lia.
        -- apply (Qlt_le_weak 0 (q_fact k)).
           apply (QltT_to_Qlt 0 (q_fact k)). apply q_fact_pos.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma eoe_fact_mono_add : forall d a : nat, QleT' (q_fact a) (q_fact (a + d)).
Proof.
  intros d a. apply Qle_to_QleT'. induction d as [| d IH].
  - replace (a + 0)%nat with a by lia. apply Qle_refl.
  - replace (a + Datatypes.S d)%nat with (Datatypes.S (a + d)) by lia.
    apply (Qle_trans _ (q_fact (a + d))).
    + exact IH.
    + exact (QleT'_to_Qle _ _ (eoe_fact_step_ge (a + d))).
Qed.

Lemma eoe_fact_mono : forall a b : nat, (a <= b)%nat -> QleT' (q_fact a) (q_fact b).
Proof.
  intros a b Hab.
  replace b with (a + (b - a))%nat by lia.
  exact (eoe_fact_mono_add (b - a) a).
Qed.

(* ============================================================ *)
(* ===== Section 3. Partial-sum order structure (positive terms increase; 2/n! > 0) ===== *)
(* ============================================================ *)

Lemma eoe_q_pow_one : forall n : nat, QeqT (q_pow 1 n) 1.
Proof.
  intro n.
  apply qeq_imp_qeqT.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow 1 (Datatypes.S n)) with (1 * q_pow 1 n).
    rewrite IH. apply Qmult_1_l.
Qed.

Lemma eoe_two_fact_pos : forall n : nat, QltT 0 ((1 + 1)%Q / q_fact n).
Proof.
  intro n.
  apply (eoe_lt_eq_l _ (0 * / q_fact n)).
  - rewrite Qmult_0_l. reflexivity.
  - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ q_fact n)).
    + apply Qinv_lt_0_compat.
       apply (QltT_to_Qlt 0 _). apply q_fact_pos.
    + unfold Qlt. simpl. lia.
Qed.

Lemma eoe_term_pos : forall n : nat,
  QltT 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intro n. apply Qlt_to_QltT.
  rewrite (qeqT_imp_qeq _ _ (eoe_q_pow_one (Datatypes.S n))).
  exact (QltT_to_Qlt _ _ (eoe_lt_eq_r 0 (/ q_fact (Datatypes.S n)) (1 / q_fact (Datatypes.S n))
           (Qinv_lt_0_compat (q_fact (Datatypes.S n))
              (QltT_to_Qlt 0 _ (q_fact_pos (Datatypes.S n))))
           (Qeq_sym (1 * / q_fact (Datatypes.S n)) (/ q_fact (Datatypes.S n))
              (Qmult_1_l (/ q_fact (Datatypes.S n)))))).
Qed.

Lemma eoe_step_pos : forall n : nat,
  QltT 0 (exp_partial (Datatypes.S n) 1 - exp_partial n 1).
Proof.
  intro n.
  assert (Hd : exp_partial (Datatypes.S n) 1 - exp_partial n 1 ==
               q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
  { simpl. ring. }
  exact (eoe_lt_eq_r 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n))
           (exp_partial (Datatypes.S n) 1 - exp_partial n 1)
           (QltT_to_Qlt _ _ (eoe_term_pos n)) (Qeq_sym _ _ Hd)).
Qed.

Lemma eoe_mono_add : forall d m : nat, QleT' (exp_partial m 1) (exp_partial (m + d) 1).
Proof.
  intros d m. apply Qle_to_QleT'. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    apply (Qle_trans _ (exp_partial (m + d) 1)).
    + exact IH.
    + apply (proj2 (Qle_minus_iff (exp_partial (m + d) 1)
                                  (exp_partial (Datatypes.S (m + d)) 1))).
      apply (Qlt_le_weak 0 (exp_partial (Datatypes.S (m + d)) 1 -
                            exp_partial (m + d) 1)).
      exact (QltT_to_Qlt _ _ (eoe_step_pos (m + d))).
Qed.

Lemma eoe_mono : forall m n : nat, (m <= n)%nat -> QleT' (exp_partial m 1) (exp_partial n 1).
Proof.
  intros m n Hmn.
  replace n with (m + (n - m))%nat by lia.
  exact (eoe_mono_add (n - m) m).
Qed.

(* ============================================================ *)
(* ===== Section 4. Explicit tail bound: m <= n implies |S_n - S_m| <= 2/m! ===== *)
(*   (engine: exp_partial_diff_bound from S03, with A := Qabs 1) *)
(* ============================================================ *)

Lemma eoe_one_abs : QeqT (Qabs 1) 1.
Proof. apply qeq_imp_qeqT. apply Qabs_pos. unfold Qle. simpl. lia. Qed.

Lemma eoe_q_pow_one_abs : forall n : nat, QeqT (q_pow (Qabs 1) n) 1.
Proof.
  intro n.
  apply qeq_imp_qeqT.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow (Qabs 1) (Datatypes.S n)) with (Qabs 1 * q_pow (Qabs 1) n).
    rewrite (qeqT_imp_qeq _ _ eoe_one_abs). rewrite IH. reflexivity.
Qed.

Lemma eoe_diff_bound : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  QleT' (Qabs (exp_partial n 1 - exp_partial m 1))
        ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q).
Proof.
  intros m n H1m Hmn.
  apply (exp_partial_diff_bound 1 (Qabs 1) m n).
  - apply qeq_imp_qeqT. reflexivity.
  - vm_compute. reflexivity.
  - intros t Hmt. apply NatLe_drop in Hmt.
    apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - exact Hmn.
Qed.

Lemma eoe_tail_explicit : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  QleT' (Qabs (exp_partial n 1 - exp_partial m 1)) ((1 + 1)%Q / q_fact m).
Proof.
  intros m n H1m Hmn.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q)).
  - apply QleT'_to_Qle.
    apply (exp_partial_diff_bound 1 (Qabs 1) m n).
    + apply qeq_imp_qeqT. reflexivity.
    + vm_compute. reflexivity.
    + intros t Hmt. apply NatLe_drop in Hmt.
      apply Qle_to_QleT'. unfold Qle. simpl. lia.
    + exact Hmn.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (eoe_q_pow_one_abs m)). unfold Qdiv. ring.
Qed.

(* ---- Symmetrized exit form: 1 <= n <= m implies |S_m - S_n| <= 2/n! ---- *)
Lemma eoe_abs_Qle : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (eoe_tail_explicit n m H1n Hnm).
Qed.

Theorem eoe_abs_bound : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (eoe_abs_Qle m n H1n Hnm).
Qed.

(* ============================================================ *)
(* ===== Section 5. Explicit rational two-sided interval for e ===== *)
(*   lo := S_n, hi := S_n + 2/n!, hi - lo == 2/n! > 0, and every later partial *)
(*   sum S_m with m >= n stays within [lo, hi]. *)
(* ============================================================ *)

Theorem eoe_two_sided : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      prod (QltT' 0 (hi - lo))
           (forall m : nat, NatLe n m ->
              prod (QleT' lo (exp_partial m 1))
                   (QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) (hi - lo))))).
Proof.
  intros n H1n.
  exists (exp_partial n 1).
  exists (exp_partial n 1 + (1 + 1)%Q / q_fact n).
  split.
  - (* Explicit gap: hi - lo == 2/n! > 0. *)
    apply Qlt_to_QltT'.
    assert (Hgap : (exp_partial n 1 + (1 + 1)%Q / q_fact n) - exp_partial n 1 ==
                   (1 + 1)%Q / q_fact n) by ring.
    rewrite Hgap. exact (QltT_to_Qlt 0 _ (eoe_two_fact_pos n)).
  - intros m Hnm.
    assert (Hnm' : (n <= m)%nat) by (apply NatLe_drop in Hnm; exact Hnm).
    split.
    + (* Lower wing: S_n <= S_m (positive terms increase). *)
      apply eoe_mono. exact Hnm'.
    + (* Upper wing: |S_m - S_n| <= hi - lo == 2/n!. *)
      apply (qleT'_weaken _ ((1 + 1)%Q / q_fact n) _).
      * exact (QleT'_to_Qle _ _ (eoe_abs_Qle m n H1n Hnm')).
      * ring.
Qed.

(* ============================================================ *)
(* ===== Section 6. Computable precision: explicit modulus N := S(ceil(2/eps)) ===== *)
(* ============================================================ *)

Definition eoe_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling ((1 + 1)%Q / eps))).

Lemma eoe_modulus_bound : forall eps : Q, Qlt 0 eps ->
  QltT ((1 + 1)%Q / q_fact (eoe_modulus eps)) eps.
Proof.
  intros eps Hlt.
  apply Qlt_to_QltT.
  unfold eoe_modulus.
  assert (Hinv0 : Qlt 0 (/ eps)) by (apply Qinv_lt_0_compat; exact Hlt).
  assert (H2e : Qlt 0 ((1 + 1)%Q / eps)).
  { apply (QltT_to_Qlt 0 ((1 + 1)%Q / eps)).
    apply (eoe_lt_eq_l _ (0 * / eps)).
    - rewrite Qmult_0_l. reflexivity.
    - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ eps)).
      + exact Hinv0.
      + unfold Qlt. simpl. lia. }
  remember (Qceiling ((1 + 1)%Q / eps)) as c eqn:Hcdef.
  assert (Hle : Qle ((1 + 1)%Q / eps) (c # 1)) by (rewrite Hcdef; apply Qle_ceiling).
  assert (Hc1 : (1 <= c)%Z).
  { assert (Hlt1 : Qlt 0 (c # 1))
      by (apply (Qlt_le_trans 0 ((1 + 1)%Q / eps) (c # 1)); assumption).
    unfold Qlt in Hlt1. simpl in Hlt1. lia. }
  assert (Hk : Z.of_nat (Z.to_nat c) = c) by lia.
  assert (Hceil : Qle ((1 + 1)%Q / eps) ((Z.of_nat (Z.to_nat c)) # 1))
    by (rewrite Hk; exact Hle).
  (* 2/eps <= k#1 <= k! gives 2 <= k!*eps. *)
  assert (H2fact : Qle ((1 + 1)%Q / eps) (q_fact (Z.to_nat c))).
  { apply (Qle_trans _ ((Z.of_nat (Z.to_nat c)) # 1)).
    - exact Hceil.
    - apply QleT'_to_Qle. apply eoe_fact_ge_self. }
  assert (Hmul : Qle ((1 + 1)%Q / eps * eps) (q_fact (Z.to_nat c) * eps)).
  { apply Qmult_le_compat_r.
    - exact H2fact.
    - apply (Qlt_le_weak 0 eps). exact Hlt. }
  assert (Hid : (1 + 1)%Q / eps * eps == (1 + 1)%Q).
  { field. intro Hzz. apply (Qlt_not_eq 0 eps Hlt). exact (Qeq_sym _ _ Hzz). }
  assert (H2 : Qle (1 + 1)%Q (q_fact (Z.to_nat c) * eps)).
  { apply (Qle_trans _ ((1 + 1)%Q / eps * eps)).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. exact Hid.
    - exact Hmul. }
  (* The factorial of N = S k is (k+1)*k! >= 2*k!, pressing strictly below eps. *)
  assert (HN2 : Qle (1 + 1)%Q ((Z.of_nat (Datatypes.S (Z.to_nat c))) # 1)).
  { unfold Qle. simpl. lia. }
  assert (Hden : Qle ((1 + 1)%Q * q_fact (Z.to_nat c))
                     (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Z.to_nat c)) # 1) * q_fact (Z.to_nat c))).
    - apply Qmult_le_compat_r.
      + exact HN2.
      + apply (Qlt_le_weak 0 (q_fact (Z.to_nat c))).
        apply (QltT_to_Qlt 0 _). apply q_fact_pos.
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity. }
  assert (Hstrict : Qlt (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
  { apply (QltT_to_Qlt _ ((1 + 1)%Q * q_fact (Z.to_nat c))).
    apply (eoe_lt_eq_l _ (1 * q_fact (Z.to_nat c))).
    - symmetry. apply Qmult_1_l.
    - apply (Qmult_lt_compat_r 1 (1 + 1)%Q (q_fact (Z.to_nat c))).
      + apply (QltT_to_Qlt 0 (q_fact _)). apply q_fact_pos.
      + unfold Qlt. simpl. lia. }
  assert (HqN : Qlt (q_fact (Z.to_nat c)) (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qlt_le_trans (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
    - exact Hstrict.
    - exact Hden. }
  assert (Hdrop : Qlt ((1 + 1)%Q / q_fact (Datatypes.S (Z.to_nat c)))
                      ((1 + 1)%Q / q_fact (Z.to_nat c))).
  { apply (QltT_to_Qlt _ ((1 + 1)%Q / q_fact (Z.to_nat c))).
    apply (eoe_div_lt (1 + 1)%Q (q_fact (Datatypes.S (Z.to_nat c))) (q_fact (Z.to_nat c))).
    - unfold Qlt. simpl. lia.
    - apply (QltT_to_Qlt 0 _). apply q_fact_pos.
    - apply (QltT_to_Qlt 0 _). apply q_fact_pos.
    - exact HqN. }
  assert (H2inv : Qle ((1 + 1)%Q * / q_fact (Z.to_nat c))
                      ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
  { apply Qmult_le_compat_r.
    - exact H2.
    - apply (Qlt_le_weak 0 (/ q_fact (Z.to_nat c))).
      apply Qinv_lt_0_compat.
      apply (QltT_to_Qlt 0 _). apply q_fact_pos. }
  assert (Hid2 : (q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c) == eps).
  { field. intro Hzz.
    destruct (q_neq_of_lt (q_fact (Z.to_nat c)) (q_fact_pos (Z.to_nat c))
      (qeq_imp_qeqT _ _ Hzz)). }
  assert (Hfinal : Qle ((1 + 1)%Q / q_fact (Z.to_nat c)) eps).
  { apply (Qle_trans _ ((1 + 1)%Q * / q_fact (Z.to_nat c))).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. reflexivity.
    - apply (Qle_trans _ ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
      + exact H2inv.
      + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hid2. }
  apply (Qlt_le_trans _ ((1 + 1)%Q / q_fact (Z.to_nat c))).
  - exact Hdrop.
  - exact Hfinal.
Qed.

(* ---- Exit 2: sigT Cauchy modulus (explicit N = ceil(2/eps)+1, extractable) ---- *)
Theorem eoe_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (exp_partial m 1 - exp_partial n 1)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT_to_Qlt 0 eps Heps)).
  exists (eoe_modulus eps).
  intros m n HNm HNn.
  apply NatLe_drop in HNm.
  apply NatLe_drop in HNn.
  apply Qlt_to_QltT'.
  assert (HN1 : (1 <= eoe_modulus eps)%nat) by (unfold eoe_modulus; lia).
  assert (H1m : (1 <= m)%nat) by lia.
  assert (H1n : (1 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:E.
  - (* m <= n: |S_n - S_m| <= 2/m! <= 2/N! < eps. *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact m)).
      * rewrite Qabs_Qminus. apply QleT'_to_Qle. apply (eoe_tail_explicit m n); assumption.
      * apply QleT'_to_Qle.
        apply (eoe_div_le (1 + 1)%Q (q_fact m) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply (QltT_to_Qlt 0 _). apply q_fact_pos.
        -- apply (QltT_to_Qlt 0 _). apply q_fact_pos.
        -- apply QleT'_to_Qle. apply eoe_fact_mono. exact HNm.
    + exact (QltT_to_Qlt _ _ (eoe_modulus_bound eps Hlt)).
  - (* n < m: |S_m - S_n| <= 2/n! <= 2/N! < eps. *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact n)).
      * apply QleT'_to_Qle. apply (eoe_tail_explicit n m); lia.
      * apply QleT'_to_Qle.
        apply (eoe_div_le (1 + 1)%Q (q_fact n) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply (QltT_to_Qlt 0 _). apply q_fact_pos.
        -- apply (QltT_to_Qlt 0 _). apply q_fact_pos.
        -- apply QleT'_to_Qle. apply eoe_fact_mono. exact HNn.
    + exact (QltT_to_Qlt _ _ (eoe_modulus_bound eps Hlt)).
Qed.

(* ============================================================ *)
(* Section 7. Assumption audit evidence lines. *)
(* ============================================================ *)

Print Assumptions eoe_two_sided.
Print Assumptions eoe_abs_bound.
Print Assumptions eoe_cauchy_modulus.
Print Assumptions eoe_mono.

Print Assumptions eoe_abs_bound.
Print Assumptions eoe_abs_Qle.
Print Assumptions qleT'_weaken.
Print Assumptions Qlt_to_QltT'.
Print Assumptions QltT'_to_Qlt.
