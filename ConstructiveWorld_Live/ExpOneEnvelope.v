(* ==========================================================================)
   ExpOneEnvelope - decision bridges and the monotone positivity envelope for
   the exponential partial sums, with a rational two-sided interval for e.

(** * ExpOneEnvelope: bridges and positivity envelope for exp partial sums.

    Mission. Decision bridges for the rationals, the monotone positivity
    family around the factorial (eoe_fact_mono, eoe_term_pos, eoe_step_pos),
    the explicit tail bound eoe_abs_bound, the eventual positivity of
    exp(-x) in even/odd split form (exists-N threshold shape), the all-x >= 0
    strict positivity of even partial sums, and the envelope statements
    elv_exp_partial_ge_lin (1+x <= exp_partial n x) and
    elv_exp_partial_le_one (for 0 <= x <= 1).

    Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp, S04 through
    S15, ExpNegPos, plus stdlib QArith, Qabs, Arith, Setoid, Lia, Morphisms,
    QArith.Qminmax.

    References. ConstructiveWorld-Main ConstructiveWorld_Live/ExpOneEnvelope.v
    (statement names carried over verbatim).

    Constructivity. Statements are Set-carried; proofs are Qed-closed with
    no axioms and Print Assumptions reports a closed global context.

    Build. Rocq 9.1 with -native-compiler no -Q <root> "".
 *)
   ========================================================================== *)

(* ============ Section 8. Eventual positivity of exp(-x), even/odd split (exists-N form) ============ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Lia.

(* Helper 1: 1/(2C) < 1/C for C >= 1, following the even branch
   of the S03 template: the difference 1/C - 1/(2C) == 1/(2C) via
   field and C <> 0, then 0 < Qinv(2C) <= 1*Qinv(2C). *)
Lemma enpf_halfC_lt_invC : forall C : Q, QleT' 1 C -> QltT (1 / (2 * C)) (1 / C).
Proof.
  intros C HC1.
  apply Qlt_to_QltT.
  apply (Qlt_minus_iff (1 / (2 * C)) (1 / C)).
  unfold Qdiv.
  assert (Hf : 1 / C + - (1 / (2 * C)) == 1 / (2 * C)).
  { field.
    intro Hz.
    destruct (q_neq_of_lt C
      (Qlt_to_QltT 0 C
         (Qlt_le_trans 0 1 C Z.lt_0_1 (QleT'_to_Qle 1 C HC1)))
      (qeq_imp_qeqT _ _ Hz)). }
  setoid_rewrite Hf.
  apply (Qlt_le_trans _ (Qinv (2 * C)) _).
  - apply Qinv_lt_0_compat.
    apply (Qmult_lt_0_compat 2 C).
    + exact (Z.lt_succ_diag_r 1).
    + apply (Qlt_le_trans 0 1 C).
      * exact Z.lt_0_1.
      * exact (QleT'_to_Qle 1 C HC1).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    apply Qeq_sym. apply (Qmult_1_l (Qinv (2 * C))).
Qed.

(* Helper 2: QltT form of 0 < 1/(2C) (qltT_div_pos with C >= 1). *)
Lemma enpf_halfC_posT : forall C : Q, QleT' 1 C -> QltT 0 (1 / (2 * C)).
Proof.
  intros C HC1.
  apply (qltT_div_pos 1 (2 * C)).
  - exact qltT_0_1.
  - apply (qmult_ltT_0_compat 2 C).
    + exact qltT_0_2.
    + apply (qltT_leT'_ltT 0 1 C).
      * exact qltT_0_1.
      * exact HC1.
Qed.

(* Even/odd split (Set-level sigT packaging): Nat.Even_or_Odd is a Prop-level
   or, which may not be eliminated into a Set goal; use the stdlib div2/odd
   decision (quotient m and parity flag b, cf. Nat.div2_odd). *)
Lemma enpf_split_even_odd : forall n : nat,
  sigT (fun m : nat => sigT (fun b : bool => n = 2 * m + (if b then 1 else 0))%nat).
Proof.
  intro n.
  refine (existT _ (Nat.div2 n) _).
  refine (existT _ (Nat.odd n) _).
  exact (Nat.div2_odd n).
Qed.

(* Main: eventual positivity of exp(-x) (exists-N form), from the two S03 lower-bound lemmas. *)
Theorem enpf_eventual_pos : forall x : Q, QleT' 0 x ->
  sigT (fun N : nat => forall n : nat, NatLe N n -> QltT 0 (exp_partial n (Qopp x))).
Proof.
  intros x Hx.
  assert (Hxle : Qle 0 x) by (exact (QleT'_to_Qle 0 x Hx)).
  (* Three bridges for M := 1+x. *)
  assert (HM1 : Qle 1 (1 + x)) by (apply (Qle_plus_nonneg_r 1 x); exact Hxle).
  assert (HM0 : QleT' 0 (1 + x)).
  { (* The goal shell is QleT'; route through Qle_to_QleT' and the Qle chain 0 <= 1 <= 1+x. *)
    apply Qle_to_QleT'.
    apply (Qle_trans 0 1 (1 + x)).
    - exact (QleT'_to_Qle _ _ Qle_0_1).
    - exact HM1. }
  assert (HxM : Qle x (1 + x)).
  { apply (Qle_trans x (x + 1) (1 + x)).
    - apply (Qle_plus_nonneg_r x 1). exact (QleT'_to_Qle _ _ Qle_0_1).
    - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring. }
  assert (Hneg : Qle (Qopp x) 0).
  { (* A change-with would re-trigger a setoid reflexivity fallback; Qopp 0 is convertible, apply directly. *)
    apply (Qopp_le_compat 0 x). exact Hxle. }
  assert (Habs : Qabs (Qopp x) == x).
  { rewrite (Qabs_neg (Qopp x) Hneg). apply Qopp_involutive. }
  assert (Hy : QleT' (Qabs (Qopp x)) (1 + x)).
  { apply Qle_to_QleT'. rewrite Habs. exact HxM. }
  (* C: series growth certificate (1 <= C and exp_series n M <= C for all n). *)
  destruct (exp_series_arch (1 + x) HM0) as [C [HC1 HC]].
  (* m0: odd-branch tail threshold (M^(2k+1)/(2k+1)! < 1/(2C) for k >= m0). *)
  destruct (exp_partial_tail_small (1 + x) C HM0 HC1) as [m0 Hm0].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  pose proof (enpf_halfC_posT C HC1) as Hhalfpos.
  (* N := 2*m0+1 covers both parities. *)
  exists (2 * m0 + 1)%nat.
  intros n Hn.
  apply NatLe_drop in Hn.
  (* Even/odd split (see enpf_split_even_odd); even branch first, odd branch second. *)
  destruct (enpf_split_even_odd n) as [k [b Hkb]].
  destruct b; subst n.
  - (* n odd (b = true, n = 2k+1) with k >= m0: 0 < 1/(2C) < exp_partial (2k+1) (-x). *)
    assert (Hk0 : (m0 <= k)%nat).
    { rewrite !Nat.add_1_r in Hn.
      apply (proj2 (Nat.mul_le_mono_pos_l m0 k 2 (Nat.lt_0_succ 1))).
      exact (proj2 (Nat.succ_le_mono (2 * m0) (2 * k)) Hn). }
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k + 1) (Qopp x))).
    + exact Hhalfpos.
    + exact (exp_partial_odd_lower (1 + x) C m0 k (Qopp x) HM0 HC1 HC Hm0 Hk0 Hy).
  - (* n even (b = false, n = 2k): 0 < 1/(2C) < 1/C <= exp_partial (2k) (-x). *)
    assert (Hkz : (2 * k + 0 = 2 * k)%nat) by apply Nat.add_0_r.
    rewrite Hkz.
    apply (qltT_trans 0 (1 / (2 * C)) (exp_partial (2 * k) (Qopp x))).
    + exact Hhalfpos.
    + apply (qltT_leT'_ltT (1 / (2 * C)) (1 / C)
               (exp_partial (2 * k) (Qopp x))).
      * exact (enpf_halfC_lt_invC C HC1).
      * exact (exp_partial_even_lower (1 + x) C (Qopp x) k HM0 HC1 HC Hy).
Qed.

Print Assumptions enpf_eventual_pos.

(* ============ Section 9. Strict positivity of even partial sums for all x >= 0 ============ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* Main: strict positivity of even partial sums for all x >= 0, the Set-level
   exit of the S03 even-branch lemma (direct re-export). *)
Theorem enpx_exp_partial_even_pos_all : forall (x : Q) (m : nat),
  QleT' 0 x -> QltT 0 (exp_partial (2 * m) (Qopp x)).
Proof.
  intros x m H0. exact (exp_even_neg_pos x m H0).
Qed.

(* Companion: nonnegativity form (one qltT_leT' step from the main statement). *)
Theorem enpx_exp_partial_even_nonneg_all : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' 0 (exp_partial (2 * m) (Qopp x)).
Proof.
  intros x m H0.
  exact (qltT_leT' 0 (exp_partial (2 * m) (Qopp x))
    (enpx_exp_partial_even_pos_all x m H0)).
Qed.

(* Honest boundary note (not a proof goal): S_1(-3) = 1 - 3 = -2 < 0, so
   odd partial sums are NOT positive for all x >= 0; eventual positivity
   (forall x >= 0, exists N, forall n >= N, 0 < S_n) is captured separately
   in Section 8 via the S03 lower-bound lemmas. *)

Print Assumptions enpx_exp_partial_even_pos_all.
Print Assumptions enpx_exp_partial_even_nonneg_all.

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
(* Section 7. Assumption audit                                   *)
(* ============================================================ *)

Print Assumptions eoe_two_sided.
Print Assumptions eoe_abs_bound.
Print Assumptions eoe_cauchy_modulus.
Print Assumptions eoe_mono.

(* ============ Section 10. elv_exp_partial_ge_lin and elv_exp_partial_le_one ============ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import ExpNegPos.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Part 1 (tail expansion): one-step definitional expansion of exp_partial,
   in the general y form (same recipe as enp_expSS). *)
(* ============================================================ *)

Lemma elv_exp_step_any : forall (n : nat) (y : Q),
  QeqT (exp_partial (Datatypes.S n) y)
       (exp_partial n y
        + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof. intros n y. apply qeq_imp_qeqT. exact (Qeq_refl (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))). Qed.

(* Base identity: S_1(x) == 1 + x.  Qinv (1 * 1) is not a ring atom
   (Qdiv = Qmult x (Qinv y)), so bridge it to 1 before ringing
   (same recipe as the enp_odd_ge base case). *)
Lemma elv_exp1 : forall x : Q, QeqT (exp_partial 1 x) (1 + x).
Proof.
  intros x.
  apply qeq_imp_qeqT.
  replace (exp_partial 1 x)
    with (exp_partial 0 x + q_pow x 1 / q_fact 1) by reflexivity.
  replace (exp_partial 0 x) with 1%Q by reflexivity.
  unfold Qdiv.
  replace (q_pow x 1) with (x * 1) by reflexivity.
  replace (q_fact 1) with (1 * 1) by reflexivity.
  replace (Qinv (1 * 1)) with 1 by reflexivity.
  ring.
Qed.

(* ============================================================ *)
(* Part 2 (Qle-lined main): 0 <= x and 1 <= n imply 1 + x <= S_n(x);
   the difference S_n(x) - (1+x) = sum of x^k/k! for k = 2..n is termwise
   nonnegative. *)
(* ============================================================ *)

Lemma elv_lin_le_all : forall (x : Q) (n : nat),
  Qle 0 x -> (1 <= n)%nat -> QleT' (1 + x) (exp_partial n x).
Proof.
  intros x n Hx0 Hn.
  apply Qle_to_QleT'.
  revert Hn.
  induction n as [| n IH]; intros Hn.
  - (* n = 0 contradicts 1 <= n (exfalso + lia). *)
    exfalso. lia.
  - destruct n as [| n'].
    + (* Base n = 1: S_1(x) == 1 + x. *)
      apply QleT'_to_Qle.
      exact (qeq_le (1 + x) (exp_partial 1 x)
               (qeq_imp_qeqT _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (elv_exp1 x))))).
    + (* Step n = S (S n'): tail expansion and nonnegative last-term transfer. *)
      assert (HIH : Qle (1 + x) (exp_partial (Datatypes.S n') x))
        by (apply IH; lia).
      assert (Hterm : Qle 0 (q_pow x (Datatypes.S (Datatypes.S n'))
                             / q_fact (Datatypes.S (Datatypes.S n'))))
        by (apply QleT'_to_Qle; apply enp_term_nonneg; exact Hx0).
      apply (Qle_trans (1 + x) (exp_partial (Datatypes.S n') x)
                       (exp_partial (Datatypes.S (Datatypes.S n')) x)).
      * exact HIH.
      * apply (Qle_trans (exp_partial (Datatypes.S n') x)
                         (exp_partial (Datatypes.S n') x
                          + q_pow x (Datatypes.S (Datatypes.S n'))
                            / q_fact (Datatypes.S (Datatypes.S n')))).
        -- (* Route the atomic LHS through E' + 0 (otherwise Qplus_le_compat
              mis-unfolds the x+z pattern). *)
           apply (Qle_trans (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)
                            (exp_partial (Datatypes.S n') x
                             + q_pow x (Datatypes.S (Datatypes.S n'))
                               / q_fact (Datatypes.S (Datatypes.S n')))).
           ++ apply QleT'_to_Qle.
              apply (qeq_le (exp_partial (Datatypes.S n') x)
                            (exp_partial (Datatypes.S n') x + 0)).
              ** apply qeq_imp_qeqT. ring.
           ++ apply Qplus_le_compat.
              ** apply Qle_refl.
              ** exact Hterm.
        -- (* Tail expansion as above (Qeq bridge). *)
           apply QleT'_to_Qle.
           exact (qeq_le _ _
                    (qeq_imp_qeqT _ _ (Qeq_sym _ _
                       (qeqT_imp_qeq _ _ (elv_exp_step_any (Datatypes.S n') x))))).
Qed.

(* ============================================================ *)
(* Part 3 (main, Set exit): 0 <= x and 1 <= n imply 1 + x <= S_n(x). *)
(* ============================================================ *)

Theorem elv_exp_partial_ge_lin : forall (x : Q) (n : nat),
  QleT' 0 x -> (1 <= n)%nat -> QleT' (1 + x) (exp_partial n x).
Proof.
  intros x n H0 Hn.
  apply elv_lin_le_all.
  - apply QleT'_to_Qle. exact H0.
  - exact Hn.
Qed.

(* ============================================================ *)
(* Part 4 (support): Qopp through division and odd/even power sign normalization. *)
(* ============================================================ *)

(* ring does not distribute over division: Qopp (u/v) == Qopp u / v. *)
Lemma elv_qopp_div : forall u v : Q, QeqT (Qopp (u / v)) (Qopp u / v).
Proof. intros u v. apply qeq_imp_qeqT. unfold Qdiv. ring. Qed.

(* Odd power: (-x)^{S(2k)} == -x^{S(2k)} (index S(2k) matches q_pow_neg_odd directly). *)
Lemma elv_neg_pow_odd : forall (x : Q) (k : nat),
  QeqT (q_pow (Qopp x) (Datatypes.S (2 * k)))
       (Qopp (q_pow x (Datatypes.S (2 * k)))).
Proof. intros x k. exact (q_pow_neg_odd x k). Qed.

(* Even power: (-x)^{S(S(2k))} == x^{S(S(2k))} (index normalized to 2 * S k). *)
Lemma elv_neg_pow_even : forall (x : Q) (k : nat),
  QeqT (q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * k))))
       (q_pow x (Datatypes.S (Datatypes.S (2 * k)))).
Proof.
  intros x k.
  replace (Datatypes.S (Datatypes.S (2 * k)))
    with (2 * Datatypes.S k)%nat by lia.
  exact (q_pow_neg_even x (Datatypes.S k)).
Qed.

(* ============================================================ *)
(* Part 5 (even-index induction, Set level): 0 <= x <= 1 implies S_{2m}(-x) <= 1.
   The two-step tail is -u + t2 with u := x^{2m+1}/(2m+1)! and t2 <= u
   (enp_decr), so S_{2m+2} <= S_{2m+1} + u = S_{2m} - u + u <= 1. *)
(* ============================================================ *)

Lemma elv_even_le_one : forall (x : Q) (m : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial (2 * m) (Qopp x)) 1.
Proof.
  intros x m H0 H1.
  induction m as [| m IH].
  - (* Base: S_0(-x) = 1. *)
    apply qeq_leT'. apply qeq_imp_qeqT. reflexivity.
  - (* Induction step: normalize 2 * S m to S(S(2m)) and expand two steps. *)
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    apply Qle_to_QleT'.
    (* E1 = S_{2m}(-x) + Qopp u (odd-term negativity bridge). *)
    assert (HE1 : exp_partial (Datatypes.S (2 * m)) (Qopp x)
                  == exp_partial (2 * m) (Qopp x)
                     + Qopp (q_pow x (Datatypes.S (2 * m))
                             / q_fact (Datatypes.S (2 * m)))).
    { rewrite (qeqT_imp_qeq _ _ (elv_exp_step_any (2 * m) (Qopp x))).
      rewrite (qeqT_imp_qeq _ _ (elv_neg_pow_odd x m)).
      rewrite (qeqT_imp_qeq _ _
                 (elv_qopp_div (q_pow x (Datatypes.S (2 * m)))
                               (q_fact (Datatypes.S (2 * m))))). reflexivity. }
    apply (Qle_trans
            (exp_partial (Datatypes.S (Datatypes.S (2 * m))) (Qopp x))
            (exp_partial (Datatypes.S (2 * m)) (Qopp x)
             + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
               / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
    + (* Tail expansion as above (Qeq bridge). *)
      apply QleT'_to_Qle.
      exact (qeq_le _ _
               (qeq_imp_qeqT _ _ (Qeq_sym _ _
                  (qeqT_imp_qeq _ _ (elv_exp_step_any (Datatypes.S (2 * m)) (Qopp x)))))).
    + (* Second limb: the LHS is in Qopp form; normalize by the even-power bridge, then pair terms by enp_decr. *)
      apply (Qle_trans
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow (Qopp x) (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))
              (exp_partial (Datatypes.S (2 * m)) (Qopp x)
               + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                 / q_fact (Datatypes.S (Datatypes.S (2 * m))))).
      * (* Even-power bridge: (-x)^{S(S(2m))} == x^{S(S(2m))}. *)
        apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ (elv_neg_pow_even x m)). reflexivity.
      * apply (Qle_trans
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (Datatypes.S (2 * m)))
                   / q_fact (Datatypes.S (Datatypes.S (2 * m))))
                (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                 + q_pow x (Datatypes.S (2 * m))
                   / q_fact (Datatypes.S (2 * m)))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. apply (enp_decr x (Datatypes.S (2 * m))).
              ** apply QleT'_to_Qle. exact H0.
              ** apply QleT'_to_Qle. exact H1.
        -- (* S_{2m+1} + u = S_{2m} - u + u = S_{2m} <= 1. *)
           apply (Qle_trans
                   (exp_partial (Datatypes.S (2 * m)) (Qopp x)
                    + q_pow x (Datatypes.S (2 * m))
                      / q_fact (Datatypes.S (2 * m)))
                   (exp_partial (2 * m) (Qopp x))).
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. rewrite HE1. ring.
           ++ apply QleT'_to_Qle. exact IH.
Qed.

(* ============================================================ *)
(* Part 6 (Qle-lined): 0 <= x <= 1 implies S_n(-x) <= 1.
   Even indices quote Part 5; odd indices use S_{2m+1} = S_{2m} - u <= S_{2m} <= 1
   (odd-term nonnegativity via enp_term_nonneg and Qopp_le_compat). *)
(* ============================================================ *)

Lemma elv_exp_le_one_prop : forall (x : Q) (n : nat),
  Qle 0 x -> Qle x 1 -> QleT' (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  apply Qle_to_QleT'.
  destruct (Nat.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - (* Even part: n = 2m. *)
    subst n.
    apply QleT'_to_Qle.
    apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0) (Qle_to_QleT' _ _ H1)).
  - (* Odd part: n = 2m+1, normalized to S(2m) and expanded one step. *)
    subst n.
    replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    apply (Qle_trans (exp_partial (Datatypes.S (2 * m)) (Qopp x))
                     (exp_partial (2 * m) (Qopp x)
                      + Qopp (q_pow x (Datatypes.S (2 * m))
                              / q_fact (Datatypes.S (2 * m))))).
    + (* S_{2m+1} == S_{2m} - u (tail expansion, odd power, Qopp through division). *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      rewrite (qeqT_imp_qeq _ _ (elv_exp_step_any (2 * m) (Qopp x))).
      rewrite (qeqT_imp_qeq _ _ (elv_neg_pow_odd x m)).
      rewrite (qeqT_imp_qeq _ _
                 (elv_qopp_div (q_pow x (Datatypes.S (2 * m)))
                               (q_fact (Datatypes.S (2 * m))))). reflexivity.
    + (* S_{2m} - u <= S_{2m} + 0 <= S_{2m} <= 1. *)
      apply (Qle_trans (exp_partial (2 * m) (Qopp x)
                        + Qopp (q_pow x (Datatypes.S (2 * m))
                                / q_fact (Datatypes.S (2 * m))))
                       (exp_partial (2 * m) (Qopp x) + 0)).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply (Qle_trans
                    (Qopp (q_pow x (Datatypes.S (2 * m))
                           / q_fact (Datatypes.S (2 * m))))
                    (Qopp 0) 0).
           ++ apply Qopp_le_compat. apply QleT'_to_Qle. apply enp_term_nonneg. exact H0.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans (exp_partial (2 * m) (Qopp x) + 0)
                         (exp_partial (2 * m) (Qopp x))).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply QleT'_to_Qle.
           apply (elv_even_le_one x m (Qle_to_QleT' _ _ H0)
                                  (Qle_to_QleT' _ _ H1)).
Qed.

(* ============================================================ *)
(* Part 7 (main, Set exit): 0 <= x <= 1 implies S_n(-x) <= 1. *)
(* ============================================================ *)

Theorem elv_exp_partial_le_one : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (exp_partial n (Qopp x)) 1.
Proof.
  intros x n H0 H1.
  apply elv_exp_le_one_prop.
  - apply QleT'_to_Qle. exact H0.
  - apply QleT'_to_Qle. exact H1.
Qed.

(* ============================================================ *)
(* Assumption audit *)
(* ============================================================ *)

Print Assumptions elv_exp_partial_ge_lin.
Print Assumptions elv_exp_partial_le_one.
