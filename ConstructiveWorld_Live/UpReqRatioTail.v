(* ConstructiveWorld-Set -- quantitative geometric tail-sum bounds. *)

(** * UpReqRatioTail: geometric caps on finite tail sums of ratio-decaying sequences.

    Mission.  A ratio certificate [u (S j) <= rho * u j] with [0 <= rho < 1]
      caps every finite tail sum at [u n * (1 - rho ^ N) / (1 - rho)]; the
      Q-layer toolkit [rtb_qleT_refl], [rtb_qleT_trans], [rtb_qleT_mult_l],
      [rtb_qleT_mult_r], [rtb_qleT_div_r], [rtb_pow_le_one], the sums
      [rtb_tsum] and [rtb_rsum], the mother lemmas [rtb_ratio_tail_Q_mult],
      [rtb_ratio_tail_Q] and [rtb_ratio_tail_real], and the site instances
      [rtb_exp_inst], [rtb_exp_real_inst] and [rtb_atan_inst].

    Dependencies.  Stdlib [QArith.Qring], [QArith.Qabs], [ZArith], [Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock] and [S15_TailFEPUp] of this development.

    References.  This development, UpReqRatioTail.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  Main theorems [rtb_ratio_tail_Q_mult], [rtb_ratio_tail_Q],
      [rtb_ratio_tail_real], [rtb_exp_inst], [rtb_exp_real_inst], [rtb_atan_inst]
      are carried by [Set] (boolean Q-carriers [QleT'], [QltT]; [Set]-sorted
      [Real]); the Stdlib-[Prop]-faced support lemmas serve reasoning only.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqRatioTail.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
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

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1: order and algebra utilities at the Q layer. *)
(* ============================================================ *)

Lemma rtb_qleT_refl : forall a : Q, QleT' a a.
Proof. intro a. exact (Qle_to_QleT' a a (Qle_refl a)). Qed.

Lemma rtb_qleT_trans : forall a b c : Q, QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hbc.
Qed.

(* Monotonicity of [QleT'] under left multiplication by a nonnegative constant. *)
Lemma rtb_qleT_mult_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  assert (Hb : Qle a b) by (apply QleT'_to_Qle; exact Hab).
  assert (Hc' : Qle 0 c) by (apply QleT'_to_Qle; exact Hc).
  pose proof (Qmult_le_compat_r a b c Hb Hc') as H.
  rewrite (Qmult_comm c a). rewrite (Qmult_comm c b). exact H.
Qed.

(* Monotonicity of [QleT'] under right multiplication by a nonnegative constant. *)
Lemma rtb_qleT_mult_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc.
  exact (Qle_to_QleT' (a * c) (b * c)
    (Qmult_le_compat_r a b c (QleT'_to_Qle a b Hab)
      (QleT'_to_Qle 0 c Hc))).
Qed.


(* A ratio at most one has [0 <= 1 - rho], by the converse of [Qopp_le_compat] and ring normalization. *)
Lemma rtb_qle_0_minus : forall rho : Q, QleT' rho 1 -> QleT' 0 (1 - rho).
Proof.
  intros rho H. apply Qle_to_QleT'. apply QleT'_to_Qle in H.
  apply (Qle_trans _ ((- 1) + 1)%Q).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - apply (Qle_trans _ ((- rho) + 1)%Q).
    + apply Qplus_le_compat.
      * apply (Qopp_le_compat rho 1 H).
      * apply Qle_refl.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* Positivity of the positive-integer denominator [Z.of_nat (S n) # 1], on the pattern of [q_fact_pos] in [S03_QExp]. *)
Lemma rtb_zpos_S : forall n : nat, QltT 0 (Z.of_nat (Datatypes.S n) # 1).
Proof. intro n. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* A positive rational is distinct from zero. *)
Lemma rtb_neq_of_ltT : forall q : Q, QltT 0 q -> ~ (q == 0).
Proof. intros q H Hz. destruct (q_neq_of_lt q H (qeq_imp_qeqT q 0 Hz)). Qed.

(* Division by a positive denominator preserves the order, [a <= b] giving [a / K <= b / K], reducing to [Qmult_le_r]. *)
Lemma rtb_qleT_div_r : forall a b K : Q,
  QleT' a b -> QltT 0 K -> QleT' (a / K) (b / K).
Proof.
  intros a b K Hab HK. apply Qle_to_QleT'.
  assert (HK' : Qlt 0 K) by (apply QltT_to_Qlt; exact HK).
  assert (HKnz : ~ (K == 0)) by (apply rtb_neq_of_ltT; exact HK).
  apply (proj1 (Qmult_le_r (a / K) (b / K) K HK')).
  apply (Qle_trans _ a).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. exact HKnz.
  - apply (Qle_trans _ b).
    + apply QleT'_to_Qle. exact Hab.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. exact HKnz.
Qed.

(* Strict subtraction: [a < b] gives [0 < b - a], by right translation in [Qplus_lt_r]. *)
Lemma rtb_qlt_0_minus : forall a b : Q, Qlt a b -> Qlt 0 (b - a).
Proof.
  intros a b H.
  pose proof (proj2 (Qplus_lt_r a b (- a)) H) as Ht.
  assert (E1 : ((- a) + a)%Q == 0) by field.
  assert (E2 : ((- a) + b)%Q == (b - a)) by field.
  setoid_rewrite E1 in Ht. setoid_rewrite E2 in Ht. exact Ht.
Qed.

(* ρ < 1 ⟹ 1-ρ ≠ 0.  The conclusion is a Stdlib [Prop] negation, kept for reasoning only and erasing at extraction. *)
Lemma rtb_one_minus_neq : forall rho : Q, QltT rho 1 -> ~ ((1 - rho) == 0).
Proof.
  intros rho H1 Hz.
  assert (Hr : rho == 1).
  { assert (Er : rho == (1 - (1 - rho))%Q) by ring.
    rewrite Er. rewrite Hz. ring. }
  apply (Qlt_not_eq rho 1 (QltT_to_Qlt rho 1 H1)). exact Hr.
Qed.

(* For [0 <= rho <= 1], every power satisfies [q_pow rho n <= 1]. *)
Lemma rtb_pow_le_one : forall (rho : Q) (n : nat),
  QleT' 0 rho -> QleT' rho 1 -> QleT' (q_pow rho n) 1.
Proof.
  intros rho n H0 H1. induction n as [| n IH].
  - apply Qle_to_QleT'. change (q_pow rho 0%nat) with 1%Q. apply Qle_refl.
  - change (q_pow rho (Datatypes.S n)) with (rho * q_pow rho n).
    apply (rtb_qleT_trans _ (1 * q_pow rho n)).
    + apply rtb_qleT_mult_r;
        [exact H1 | apply q_pow_nonneg; exact H0].
    + apply (rtb_qleT_trans _ (1 * 1)%Q).
      * apply rtb_qleT_mult_l; [exact IH | exact Qle_0_1].
      * apply qeq_leT'. apply qeq_imp_qeqT. ring.
Qed.

(* ============================================================ *)
(* Part 2: the mother lemma at the Q layer -- a ratio certificate caps the finite sum at the first term times the geometric factor. *)
(* ============================================================ *)

(* The finite sum of the terms [u (n + k)] for [k < N]. *)
Fixpoint rtb_tsum (u : nat -> Q) (n N : nat) : Q :=
  match N with
  | O => 0
  | Datatypes.S N' => u n + rtb_tsum u (Datatypes.S n) N'
  end.

(* Companion lemma: the sum with [S d] terms equals the sum with [d] terms plus the last term, aligning the mother theorem with the dependent shape of the site adapters. *)
Lemma rtb_tsum_S : forall (u : nat -> Q) (n d : nat),
  rtb_tsum u n (Datatypes.S d) == rtb_tsum u n d + u (n + d)%nat.
Proof.
  intros u n d. revert n. induction d as [| d IH]; intro n.
  - change (rtb_tsum u n 1%nat) with (u n + rtb_tsum u (Datatypes.S n) 0%nat).
    change (rtb_tsum u (Datatypes.S n) 0%nat) with 0%Q.
    change (rtb_tsum u n 0%nat) with 0%Q.
    replace (n + 0)%nat with n by lia. ring.
  - change (rtb_tsum u n (Datatypes.S (Datatypes.S d)))
      with (u n + rtb_tsum u (Datatypes.S n) (Datatypes.S d)).
    change (rtb_tsum u n (Datatypes.S d))
      with (u n + rtb_tsum u (Datatypes.S n) d).
    rewrite (IH (Datatypes.S n)).
    replace (Datatypes.S n + d)%nat with (n + Datatypes.S d)%nat by lia.
    ring.
Qed.

(* Core of the mother lemma in multiplicative form, by telescoping and Q ring normalization; it holds for any sequence [u] without a sign condition. *)
Lemma rtb_ratio_tail_Q_mult : forall (u : nat -> Q) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, QleT' (u (Datatypes.S j)) (rho * u j)) ->
  QleT' (rtb_tsum u n N * (1 - rho)) (u n * (1 - q_pow rho N)).
Proof.
  intros u rho N. induction N as [| N' IH]; intros n H0 H1 Hcert.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ 0%Q).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      change (rtb_tsum u n 0%nat) with 0%Q. ring.
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
      change (q_pow rho 0%nat) with 1%Q. ring.
  - assert (Hr1 : QleT' rho 1)
      by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
    assert (Hle0 : QleT' 0 (1 - rho)) by (apply rtb_qle_0_minus; exact Hr1).
    specialize (IH (Datatypes.S n) H0 H1 Hcert).
    apply Qle_to_QleT'.
    change (q_pow rho (Datatypes.S N')) with (rho * q_pow rho N').
    change (rtb_tsum u n (Datatypes.S N'))
      with (u n + rtb_tsum u (Datatypes.S n) N').
    apply (Qle_trans _ (u n * (1 - rho) + rtb_tsum u (Datatypes.S n) N' * (1 - rho))).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + apply (Qle_trans _ (u n * (1 - rho) + u (Datatypes.S n) * (1 - q_pow rho N'))).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact (QleT'_to_Qle _ _ IH).
      * apply (Qle_trans _ (u n * (1 - rho) + (rho * u n) * (1 - q_pow rho N'))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qmult_le_compat_r;
                [apply QleT'_to_Qle; apply Hcert
                | exact (QleT'_to_Qle _ _
                           (rtb_qle_0_minus (q_pow rho N')
                              (rtb_pow_le_one rho N' H0 Hr1)))].
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* Mother lemma, division form: [rtb_tsum u n N <= u n * (1 - q_pow rho N) / (1 - rho)]. *)
Lemma rtb_ratio_tail_Q : forall (u : nat -> Q) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, QleT' (u (Datatypes.S j)) (rho * u j)) ->
  QleT' (rtb_tsum u n N) (u n * ((1 - q_pow rho N) / (1 - rho))).
Proof.
  intros u rho N n H0 H1 Hcert.
  pose proof (rtb_ratio_tail_Q_mult u rho N n H0 H1 Hcert) as Hm.
  assert (Hle0 : Qle 0 (1 - rho)).
  { apply QleT'_to_Qle. apply rtb_qle_0_minus.
    apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact H1. }
  assert (Hnz : ~ ((1 - rho) == 0)) by (apply rtb_one_minus_neq; exact H1).
  assert (Hlt0 : Qlt 0 (1 - rho)).
  { destruct (Qle_lt_or_eq 0 (1 - rho) Hle0) as [Hlt | Heq].
    - exact Hlt.
    - exfalso. apply Hnz. apply Qeq_sym. exact Heq. }
  apply Qle_to_QleT'.
  apply (proj1 (Qmult_le_r (rtb_tsum u n N)
             (u n * ((1 - q_pow rho N) / (1 - rho))) (1 - rho)%Q Hlt0)).
  apply (Qle_trans _ (u n * (1 - q_pow rho N))).
  - exact (QleT'_to_Qle _ _ Hm).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. field. exact Hnz.
Qed.

(* ============================================================ *)
(* Part 3: the mother theorem at the Real layer, in Bishop/eps form. *)
(* ============================================================ *)

(* The Real-layer finite sum of [u (n + k)] for [k < N]. *)
Fixpoint rtb_rsum (u : nat -> Real) (n N : nat) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S N' => real_plus (u n) (rtb_rsum u (Datatypes.S n) N')
  end.

(* Pointwise ring-normalization tactic, in the style of [mix_rring] of UpReqMixingTime and [tvd_rring] of UpTVDoeblin. *)
Ltac rtb_rproj_ring :=
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_const real_of_nat] in *;
  apply qeq_imp_qeqT; ring.

(* Ring-normalization family for [real_const]; the quantifications are fully self-contained, so [destruct] applies safely. *)
Lemma rtb_rc_wd : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_const]. apply qeq_imp_qeqT. rewrite H. ring.
Qed.

Lemma rtb_rc_mult0_plus : forall (x e : Real),
  real_eq (real_plus (real_mult x (real_const 0)) e) e.
Proof. intros x e. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_mult_comm : forall (x : Real) (a : Q),
  real_eq (real_mult x (real_const a)) (real_mult (real_const a) x).
Proof. intros x a. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_plus_comm : forall x y : Real,
  real_eq (real_plus x y) (real_plus y x).
Proof. intros x y. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_step_eq : forall (x e : Real) (a b : Q),
  real_eq (real_plus x (real_plus (real_mult (real_mult (real_const a) x) (real_const b)) e))
          (real_plus (real_mult x (real_const (1 + a * b))) e).
Proof. intros x e a b. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

(* Transport of [real_lt] in both directions along [real_eq], reducing to [real_le_lt_trans] and [real_lt_le_trans]. *)
Lemma rtb_rlt_eq_l : forall x y z : Real,
  real_eq x y -> real_lt z x -> real_lt z y.
Proof.
  intros x y z Hxy Hlt.
  apply (real_lt_le_trans z x y Hlt).
  apply (RealSetoid.real_eq_le x y Hxy).
Qed.

Lemma rtb_rlt_eq_r : forall x y z : Real,
  real_eq y z -> real_lt x y -> real_lt x z.
Proof.
  intros x y z Hyz Hlt.
  apply (real_lt_le_trans x y z Hlt).
  apply (RealSetoid.real_eq_le y z Hyz).
Qed.

(* Right and left addition preserve [real_lt]. *)
Lemma rtb_rlt_plus_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt. destruct Hlt as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn. specialize (HN n Hn).
    destruct a as [ua Ha]; destruct b as [ub Hb]; destruct c as [uc Hc].
    cbn [projT1 real_plus] in *.
    pose proof (QltT_to_Qlt e (ub n - ua n) HN) as HN'.
    apply Qlt_to_QltT.
    assert (E : ub n + uc n - (ua n + uc n) == ub n - ua n) by ring.
    setoid_rewrite E. exact HN'.
Qed.

Lemma rtb_rlt_plus_l : forall a b c : Real,
  real_lt a b -> real_lt (real_plus c a) (real_plus c b).
Proof.
  intros a b c Hlt. destruct Hlt as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn. specialize (HN n Hn).
    destruct a as [ua Ha]; destruct b as [ub Hb]; destruct c as [uc Hc].
    cbn [projT1 real_plus] in *.
    pose proof (QltT_to_Qlt e (ub n - ua n) HN) as HN'.
    apply Qlt_to_QltT.
    assert (E : uc n + ub n - (uc n + ua n) == ub n - ua n) by ring.
    setoid_rewrite E. exact HN'.
Qed.

(* Additive bimonotonicity of [real_le]. *)
Lemma rtb_rplus_le_compat : forall a b c d : Real,
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct Hab as [Hltab | Heqab]; destruct Hcd as [Hltcd | Heqcd].
  - left. apply real_lt_plus_compat.
    + exact Hltab.
    + exact Hltcd.
  - left.
    apply (rtb_rlt_eq_r _ _ _
             (RealSetoid.real_eq_plus_compat b c b d (real_eq_refl b) Heqcd)).
    apply rtb_rlt_plus_r. exact Hltab.
  - left.
    apply (rtb_rlt_eq_r _ (real_plus d a) _
             (real_eq_trans (real_plus d a) (real_plus d b) (real_plus b d)
                (RealSetoid.real_eq_plus_compat d a d b (real_eq_refl d) Heqab)
                (rtb_rc_plus_comm d b))).
    apply (real_le_lt_trans _ (real_plus c a) (real_plus d a)
             (RealSetoid.real_eq_le _ _ (rtb_rc_plus_comm a c))).
    apply rtb_rlt_plus_r. exact Hltcd.
  - right. apply (RealSetoid.real_eq_plus_compat a c b d Heqab Heqcd).
Qed.

(* Monotonicity of [real_le] under left multiplication by a Q constant; the zero branch reduces to [real_eq], the positive branch scales the eps witness pointwise. *)
Lemma rtb_rmult_le_compat_l : forall (x y : Real) (c : Q),
  real_le x y -> QleT' 0 c ->
  real_le (real_mult (real_const c) x) (real_mult (real_const c) y).
Proof.
  intros x y c Hle Hc0. destruct Hle as [Hlt | Heq].
  - destruct (Qeq_dec c 0) as [Hc | Hc].
    + right.
      apply (real_eq_trans (real_mult (real_const c) x) real_zero
                           (real_mult (real_const c) y)).
      * apply real_eq_of_zero_diff. intro n0.
        destruct x; destruct y; cbn [projT1 real_mult real_const real_zero] in *;
          apply qeq_imp_qeqT. rewrite Hc. ring.
      * apply real_eq_sym. apply real_eq_of_zero_diff. intro n0.
        destruct x; destruct y; cbn [projT1 real_mult real_const real_zero] in *;
          apply qeq_imp_qeqT. rewrite Hc. ring.
    + left.
      assert (Hcpos : Qlt 0 c).
      { destruct (Qle_lt_or_eq 0 c (QleT'_to_Qle 0 c Hc0)) as [Hlt0 | Heq0].
        - exact Hlt0.
        - exfalso. apply Hc. apply Qeq_sym. exact Heq0. }
      destruct Hlt as [e [He [N HN]]].
      assert (Hepos : Qlt 0 e) by (apply QltT_to_Qlt; exact He).
      exists (c * e)%Q. split.
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat c e Hcpos Hepos).
      * exists N. intros n Hn. specialize (HN n Hn).
        destruct x as [vx Hvx]; destruct y as [vy Hvy].
        cbn [projT1 real_mult real_const real_zero] in *.
        pose proof (QltT_to_Qlt e (vy n - vx n) HN) as HN'.
        apply Qlt_to_QltT.
        assert (E : c * vy n - c * vx n == c * (vy n - vx n)) by ring.
        setoid_rewrite E.
        pose proof (Qmult_lt_compat_r e (vy n - vx n) c Hcpos HN') as HC.
        rewrite <- (Qmult_comm c e) in HC.
        rewrite (Qmult_comm (vy n - vx n) c) in HC.
        exact HC.
  - right.
    apply (RealSetoid.real_eq_mult_compat (real_const c) x (real_const c) y
             (real_eq_refl (real_const c)) Heq).
Qed.

(* Monotonicity of [real_le] under right multiplication by a Q constant, by commuting identities and the left-multiplication lemma. *)
Lemma rtb_rmult_le_compat_r : forall (x y : Real) (c : Q),
  real_le x y -> QleT' 0 c ->
  real_le (real_mult x (real_const c)) (real_mult y (real_const c)).
Proof.
  intros x y c Hle Hc0.
  apply (real_le_trans (real_mult x (real_const c))
           (real_mult (real_const c) y) (real_mult y (real_const c))).
  - apply (real_le_trans (real_mult x (real_const c))
             (real_mult (real_const c) x) (real_mult (real_const c) y)).
    + apply (RealSetoid.real_eq_le). apply (rtb_rc_mult_comm x c).
    + apply rtb_rmult_le_compat_l; assumption.
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult y (real_const c)) (real_mult (real_const c) y)
             (rtb_rc_mult_comm y c)).
Qed.

(* Recurrence identity for the geometric constants, closed by [field], available for rewriting in the inductive step. *)
Lemma rtb_c_rec : forall (rho : Q) (N : nat), ~ ((1 - rho) == 0) ->
  (1 - q_pow rho (Datatypes.S N)) / (1 - rho)
    == (1 + rho * ((1 - q_pow rho N) / (1 - rho)))%Q.
Proof.
  intros rho N Hnz. unfold Qdiv.
  change (q_pow rho (Datatypes.S N)) with (rho * q_pow rho N).
  field. intro Hzl. apply Hnz. rewrite Hzl. apply Qeq_refl.
Qed.

(* Nonnegativity of the geometric constant for [0 <= rho < 1]: [0 <= (1 - rho ^ N) / (1 - rho)], via [rtb_qleT_div_r] and [rtb_pow_le_one]. *)
Lemma rtb_c_nonneg : forall (rho : Q) (N : nat),
  QleT' 0 rho -> QltT rho 1 -> QleT' 0 ((1 - q_pow rho N) / (1 - rho)).
Proof.
  intros rho N H0 H1.
  assert (Hr1 : QleT' rho 1)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
  assert (Hle01 : QleT' 0 (1 - rho)) by (apply rtb_qle_0_minus; exact Hr1).
  assert (Hle0q : Qle 0 (1 - rho)) by (apply QleT'_to_Qle; exact Hle01).
  assert (Hlt0 : Qlt 0 (1 - rho)).
  { destruct (Qle_lt_or_eq 0 (1 - rho) Hle0q) as [Hlt | Heq].
    - exact Hlt.
    - exfalso. apply (rtb_one_minus_neq rho H1). apply Qeq_sym. exact Heq. }
  apply (rtb_qleT_trans _ (0 / (1 - rho))).
  - apply qeq_leT'. apply qeq_imp_qeqT. unfold Qdiv. ring.
  - apply rtb_qleT_div_r.
    + apply rtb_qle_0_minus. apply rtb_pow_le_one; assumption.
    + apply Qlt_to_QltT. exact Hlt0.
Qed.

(* Isolating the step estimate [u (S n) * cN + eps <= (rho * u n) * cN + eps] as a single-level lemma to avoid deep nesting. *)
Lemma rtb_step_le : forall (u : nat -> Real) (rho cN : Q) (n : nat) (eps : Real),
  real_le (u (Datatypes.S n)) (real_mult (real_const rho) (u n)) ->
  QleT' 0 cN ->
  real_le (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps)
          (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps).
Proof.
  intros u rho cN n eps Hcert HcN.
  apply rtb_rplus_le_compat.
  - apply rtb_rmult_le_compat_r; assumption.
  - apply real_le_refl.
Qed.

(* Mother theorem: a ratio certificate gives the strict bound [tail sum < u n * (1 - rho ^ N) / (1 - rho) + eps] in Bishop/eps form. *)
Lemma rtb_ratio_tail_real : forall (u : nat -> Real) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, real_le (u (Datatypes.S j)) (real_mult (real_const rho) (u j))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt (rtb_rsum u n N)
          (real_plus (real_mult (u n) (real_const ((1 - q_pow rho N) / (1 - rho)))) eps).
Proof.
  intros u rho N. induction N as [| N' IH]; intros n H0 H1 Hcert eps Heps.
  - (* Base case: the empty tail sum [0] is below [0 * u n + eps]. *)
    assert (Hz : ((1 - 1) / (1 - rho))%Q == 0%Q)
      by (field; exact (rtb_one_minus_neq rho H1)).
    change (q_pow rho 0%nat) with 1%Q.
    assert (E0 : real_eq (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps) eps).
    { apply (real_eq_trans
               (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
               (real_plus (real_mult (u n) (real_const 0)) eps) eps).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps
                 (real_mult (u n) (real_const 0)) eps).
        + apply (RealSetoid.real_eq_mult_compat (u n)
                   (real_const ((1 - 1) / (1 - rho))%Q) (u n) (real_const 0)
                   (real_eq_refl (u n)) (rtb_rc_wd _ _ Hz)).
        + apply real_eq_refl.
      - exact (rtb_rc_mult0_plus (u n) eps). }
    apply (rtb_rlt_eq_r real_zero eps
             (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
             (real_eq_sym
                (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
                eps E0) Heps).
  - (* Inductive step: the recurrence [c (S N') == 1 + rho * c N'] plus the single-step certificate. *)
    assert (Hr1 : QleT' rho 1)
      by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
    specialize (IH (Datatypes.S n) H0 H1 Hcert eps Heps).
    set (cN := ((1 - q_pow rho N') / (1 - rho))%Q) in *.
    set (cS := ((1 - q_pow rho (Datatypes.S N')) / (1 - rho))%Q) in *.
    assert (Hrec : cS == (1 + rho * cN)%Q).
    { unfold cS, cN. apply rtb_c_rec. intro Hz. apply (rtb_one_minus_neq rho H1 Hz). }
    assert (Hstep_eq : real_eq
             (real_plus (u n) (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
             (real_plus (real_mult (u n) (real_const cS)) eps)).
    { apply (real_eq_trans
               (real_plus (u n) (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
               (real_plus (real_mult (u n) (real_const (1 + rho * cN))) eps)
               (real_plus (real_mult (u n) (real_const cS)) eps)).
      - apply rtb_rc_step_eq.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult (u n) (real_const (1 + rho * cN))) eps
                 (real_mult (u n) (real_const cS)) eps).
        + apply (RealSetoid.real_eq_mult_compat (u n) (real_const (1 + rho * cN)) (u n) (real_const cS)
                   (real_eq_refl (u n)) (rtb_rc_wd (1 + rho * cN) cS (Qeq_sym _ _ Hrec))).
        + apply real_eq_refl. }
    apply (real_lt_le_trans
             _ (real_plus (u n)
                  (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps))).
    + apply rtb_rlt_plus_l. exact IH.
    + assert (Hcert' : real_le (u (Datatypes.S n))
                         (real_mult (real_const rho) (u n))) by (apply Hcert).
      apply (real_le_trans
               _ (real_plus (u n)
                    (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
               (real_plus (real_mult (u n) (real_const cS)) eps)).
      * apply (rtb_rplus_le_compat (u n) (u n)
                   (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps)
                   (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps));
          [apply real_le_refl
          | apply (rtb_step_le u rho cN n eps (Hcert n) (rtb_c_nonneg rho N' H0 H1))].
      * apply (RealSetoid.real_eq_le). exact Hstep_eq.
Qed.

(* Transport of the Stdlib order [Qle] along [Qeq] in both directions, combined with [qeq_le].  Both statements are [Qle]-sorted ([Prop]) and kept for reasoning only. *)
Lemma rtb_qle_eq_l : forall X Y Z : Q, X == Y -> Qle Y Z -> Qle X Z.
Proof.
  intros X Y Z Hxy Hyz. apply (Qle_trans X Y Z).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hxy.
  - exact Hyz.
Qed.

Lemma rtb_qle_eq_r : forall X Y Z : Q, Qle X Y -> Y == Z -> Qle X Z.
Proof.
  intros X Y Z Hxy Hyz. apply (Qle_trans X Y Z).
  - exact Hxy.
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact Hyz.
Qed.

(* ============================================================ *)
(* Part 4a: the exponential site instance, running through the mother theorem proper. *)
(* ============================================================ *)

(* The exponential tail family: [u j := A ^ (S (m + j)) / (S (m + j)) !]. *)
Definition rtb_exp_term (A : Q) (m j : nat) : Q :=
  q_pow A (Datatypes.S (m + j)%nat) / q_fact (Datatypes.S (m + j)%nat).

(* One step of division algebra, closed by [field] with the side conditions made explicit. *)
Lemma rtb_field_test : forall X dd D : Q, 0 < dd -> 0 < D -> 0 < dd * D ->
  ((1 / 2) * (X * dd)) / (dd * D) == (1 / 2) * (X / D).
Proof.
  intros X dd D H1 H2 H3. unfold Qdiv. field.
  split.
  - apply rtb_neq_of_ltT. apply Qlt_to_QltT. exact H2.
  - apply rtb_neq_of_ltT. apply Qlt_to_QltT. exact H1.
Qed.

(* Ratio certificate: [u (S j) <= (1/2) * u j], from the geometric condition [(1 + 1) * A <= t + 1] of [S03_QExp] at [t := m + j + 1]. *)
Lemma rtb_exp_ratio : forall (A : Q) (m j : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  QleT' (rtb_exp_term A m (Datatypes.S j)) ((1 / 2) * rtb_exp_term A m j).
Proof.
  intros A m j HA Hgeom.
  unfold rtb_exp_term.
  replace (m + Datatypes.S j)%nat with (Datatypes.S (m + j)) by lia.
  set (k := (m + j)%nat).
  assert (Hpow : q_pow A (Datatypes.S (Datatypes.S k)) == A * q_pow A (Datatypes.S k))
    by reflexivity.
  assert (Hfact : q_fact (Datatypes.S (Datatypes.S k))
                  == (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k))
    by (apply qeqT_imp_qeq; apply q_fact_succ).
  assert (Hm : (m <= Datatypes.S k)%nat) by (unfold k; lia).
  specialize (Hgeom (Datatypes.S k) Hm).
  replace (Datatypes.S k + 1)%nat with (Datatypes.S (Datatypes.S k)) in Hgeom by lia.
  assert (HX0 : Qle 0 (q_pow A (Datatypes.S k)))
    by (apply QleT'_to_Qle; apply q_pow_nonneg; exact HA).
  assert (HgeoQ : Qle ((1 + 1) * A) (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1))
    by (apply QleT'_to_Qle; exact Hgeom).
  pose proof (Qmult_le_compat_r _ _ _ HgeoQ HX0) as Hmid.
  setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                      (q_pow A (Datatypes.S k))) in Hmid.
  assert (Hstep : QleT' (A * q_pow A (Datatypes.S k))
                        ((1 / 2) * (q_pow A (Datatypes.S k)
                           * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))).
  { apply (rtb_qleT_trans _ ((1 / 2) * ((1 + 1) * A * q_pow A (Datatypes.S k)))).
    - apply qeq_leT'. apply qeq_imp_qeqT. field.
    - apply rtb_qleT_mult_l.
      + apply Qle_to_QleT'.
        apply (Qle_trans _ (((1 + 1) * A) * q_pow A (Datatypes.S k)));
          [apply QleT'_to_Qle; apply qeq_le; apply qeq_imp_qeqT; ring | exact Hmid].
      + apply Qle_to_QleT'. unfold Qle. simpl. lia. }
  assert (HddD_nz : ~ (((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                          * q_fact (Datatypes.S k)) == 0)).
  { intro Hz.
    exact (rtb_neq_of_ltT
             ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k))
             (Qlt_to_QltT _ _
                (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                   (q_fact (Datatypes.S k))
                   (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                   (QltT_to_Qlt _ _ (q_fact_pos (Datatypes.S k))))) Hz). }
  assert (HqD_nz : ~ (q_fact (Datatypes.S k) == 0)).
  { intro Hz. exact (rtb_neq_of_ltT (q_fact (Datatypes.S k)) (q_fact_pos (Datatypes.S k)) Hz). }
  apply (rtb_qleT_trans _
    ((A * q_pow A (Datatypes.S k))
       / ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k)))).
  - apply rtb_qleT_refl.
  - apply (rtb_qleT_trans _
      (((1 / 2) * (q_pow A (Datatypes.S k)
             * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))
          / ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k)))).
    + apply rtb_qleT_div_r.
      * exact Hstep.
      * apply Qlt_to_QltT.
        apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                 (q_fact (Datatypes.S k))
                 (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                 (QltT_to_Qlt _ _ (q_fact_pos (Datatypes.S k)))).
    + apply qeq_leT'. apply qeq_imp_qeqT. apply rtb_field_test.
      * apply QltT_to_Qlt. apply rtb_zpos_S.
      * apply QltT_to_Qlt. apply q_fact_pos.
      * apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                 (q_fact (Datatypes.S k))
                 (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                 (QltT_to_Qlt _ _ (q_fact_pos (Datatypes.S k)))).
Qed.

(* Adapter lemma: the dependent form of [exp_tail_abs] equals the [rtb_tsum] form consumed by the mother theorem. *)
Lemma rtb_exp_tsum_eq : forall (A : Q) (m d : nat),
  exp_tail_abs m (m + d)%nat A
    == rtb_tsum (fun k => rtb_exp_term A m k) 0%nat d.
Proof.
  intros A m d. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia.
    rewrite (qeqT_imp_qeq _ _ (exp_tail_abs_le_m m m A (Nat.le_refl m))).
    reflexivity.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    change (exp_tail_abs m (Datatypes.S (m + d)) A) with
      (exp_tail_abs m (m + d)%nat A
         + (if Nat.leb m (m + d)%nat
            then q_pow A (Datatypes.S (m + d)%nat) / q_fact (Datatypes.S (m + d)%nat)
            else 0)).
    assert (Hleb : (Nat.leb m (m + d)%nat) = true)
      by (apply (proj2 (Nat.leb_le m (m + d))); lia).
    rewrite Hleb.
    rewrite IH. rewrite rtb_tsum_S.
    replace (0 + d)%nat with d by lia. cbn beta. reflexivity.
Qed.

(* The exponential site instance at the Q layer, running through [rtb_ratio_tail_Q] proper. *)
Lemma rtb_exp_inst : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A)
        ((q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
           * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))).
Proof.
  intros A m n HA Hgeom Hmn.
  replace n with ((m + (n - m))%nat) by lia.
  assert (Hrho0 : QleT' 0 (1 / 2)%Q) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (Hrho1 : QltT (1 / 2)%Q 1) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hcert : forall j : nat,
            QleT' (rtb_exp_term A m (Datatypes.S j)) ((1 / 2) * rtb_exp_term A m j)).
  { intro j. apply rtb_exp_ratio; assumption. }
  assert (Hq0 : rtb_exp_term A m 0%nat
                == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
    by (unfold rtb_exp_term; replace (m + 0)%nat with m by lia; reflexivity).
  assert (HR : rtb_exp_term A m 0%nat
                 * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))
               == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)
                    * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))).
  { rewrite Hq0. ring. }
  assert (Hshim2 : exp_tail_abs m n A
                     == rtb_tsum (rtb_exp_term A m) 0%nat (n - m)%nat).
  { pose proof (rtb_exp_tsum_eq A m (n - m)%nat) as Hs.
    replace ((m + (n - m))%nat) with n in Hs by lia. exact Hs. }
  replace (m + (n - m))%nat with n by lia.
  pose proof (rtb_ratio_tail_Q (rtb_exp_term A m) (1 / 2)%Q (n - m)%nat 0%nat
                Hrho0 Hrho1 Hcert) as Hmother.
  apply QleT'_to_Qle in Hmother.
  replace (m + 0)%nat with m in Hmother by lia.
  apply Qle_to_QleT'.
  - apply (rtb_qle_eq_l (exp_tail_abs m n A)
             (rtb_tsum (rtb_exp_term A m) 0%nat (n - m)%nat)
             (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)
                * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2)))).
    + exact Hshim2.
    + apply (rtb_qle_eq_r _ _ _ Hmother HR).
Qed.

(* [real_le] between embedded constants: the certificate lifts from [QleT'], with the [Qle_lt_or_eq] dichotomy driving the case split. *)
Lemma rtb_rc_le : forall a b : Q, QleT' a b -> real_le (real_const a) (real_const b).
Proof.
  intros a b H.
  destruct (Qlt_le_dec a b) as [Hlt | Hle].
  - left.
    pose proof (rtb_qlt_0_minus a b Hlt) as Hba.
    assert (E : ((b - a) / 2)%Q == (1 / 2) * (b - a)) by (unfold Qdiv; ring).
    exists ((b - a) / 2)%Q. split.
    + apply Qlt_to_QltT. rewrite E. apply Qmult_lt_0_compat;
        [unfold Qlt; simpl; lia | exact Hba].
    + exists 0%nat. intros n Hn.
      cbn [projT1 real_const].
      apply Qlt_to_QltT. rewrite E.
      apply (Qlt_le_trans _ (1 * (b - a))).
      * assert (Hhalf : Qlt (1 / 2) 1) by (unfold Qlt; simpl; lia).
        apply (Qmult_lt_compat_r (1 / 2) 1 (b - a) Hba Hhalf).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. apply Qmult_1_l.
  - right. apply rtb_rc_wd.
    apply (Qle_antisym a b).
    + apply QleT'_to_Qle. exact H.
    + exact Hle.
Qed.

(* A product of embedded constants folds back to an embedded constant. *)
Lemma rtb_rc_mult_eq : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_mult real_const]. apply qeq_imp_qeqT. ring.
Qed.

(* The dependent Real-layer instance: a Q sequence embedded through [real_const], running through [rtb_ratio_tail_real] proper. *)
Lemma rtb_exp_real_inst : forall (A : Q) (m N : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt (rtb_rsum (fun k => real_const (rtb_exp_term A m k)) 0%nat N)
          (real_plus
             (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2))))
             eps).
Proof.
  intros A m N HA Hgeom eps Heps.
  assert (Hrho0 : QleT' 0 (1 / 2)%Q) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (Hrho1 : QltT (1 / 2)%Q 1) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hcert : forall j : nat,
            real_le (real_const (rtb_exp_term A m (Datatypes.S j)))
                    (real_mult (real_const (1 / 2))
                               (real_const (rtb_exp_term A m j)))).
  { intro j.
    apply (real_le_trans (real_const (rtb_exp_term A m (Datatypes.S j)))
             (real_const ((1 / 2) * rtb_exp_term A m j))
             (real_mult (real_const (1 / 2)) (real_const (rtb_exp_term A m j)))).
    - apply rtb_rc_le.
      unfold rtb_exp_term.
      apply rtb_exp_ratio; assumption.
    - apply (RealSetoid.real_eq_le).
      apply (rtb_rc_mult_eq (1 / 2) (rtb_exp_term A m j)). }
  pose proof (rtb_ratio_tail_real (fun k => real_const (rtb_exp_term A m k))
                (1 / 2)%Q N 0%nat Hrho0 Hrho1 Hcert eps Heps) as H.
  assert (Hu0 : rtb_exp_term A m 0%nat
                == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
    by (unfold rtb_exp_term; replace (m + 0)%nat with m by lia; reflexivity).
  apply (rtb_rlt_eq_r
           (rtb_rsum (fun k => real_const (rtb_exp_term A m k)) 0%nat N)
           (real_plus (real_mult (real_const (rtb_exp_term A m 0%nat))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps)
           (real_plus (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps)
          (RealSetoid.real_eq_plus_compat
             (real_mult (real_const (rtb_exp_term A m 0%nat))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps
             (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps
             (RealSetoid.real_eq_mult_compat (real_const (rtb_exp_term A m 0%nat))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))
                (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))
                (rtb_rc_wd _ _ Hu0) (real_eq_refl (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))))
             (real_eq_refl eps))
          H).
Qed.

(* Ratio certificate for the arctangent site, unconditional and by closed-form algebra: *)
(*   atan_mag (S j) x = |x|^{2j+3}/(2j+3) ≤ x²·atan_mag j x          *)
(*   where [x² = |x|·|x|] holds by [atan_sq_abs]; the nonlinear goal goes through multiplication monotonicity rather than [lia]. *)
Lemma rtb_atan_ratio : forall (x : Q) (j : nat),
  QleT' (atan_mag (Datatypes.S j) x) (Qabs x * Qabs x * atan_mag j x).
Proof.
  intros x j. unfold atan_mag.
  replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
  assert (Hdd : QltT 0 (Z.of_nat (2 * j + 3)%nat # 1)).
  { replace (2 * j + 3)%nat with (2 * Datatypes.S j + 1)%nat by lia.
    apply atan_odd_pos. }
  assert (Hd1 : QltT 0 (Z.of_nat (2 * j + 1)%nat # 1))
    by apply atan_odd_pos.
  assert (Hprod : QltT 0 ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))
    by (apply Qlt_to_QltT;
        apply (Qmult_lt_0_compat (Z.of_nat (2 * j + 1)%nat # 1)
                                 (Z.of_nat (2 * j + 3)%nat # 1)
                                 (QltT_to_Qlt _ _ Hd1) (QltT_to_Qlt _ _ Hdd))).
  assert (HP0 : QleT' 0 (q_pow (Qabs x) (2 * j + 3)%nat))
    by (apply q_pow_nonneg; apply Qle_to_QleT'; apply Qabs_nonneg).
  assert (Hp : q_pow (Qabs x) (2 * j + 3)%nat
               == q_pow (Qabs x) (2 * j + 1)%nat * Qabs x * Qabs x).
  { replace (2 * j + 3)%nat with (Datatypes.S (Datatypes.S (2 * j + 1)))%nat by lia.
    simpl. ring. }
  assert (Hsub : QleT' (1 / (Z.of_nat (2 * j + 3)%nat # 1))
                       (1 / (Z.of_nat (2 * j + 1)%nat # 1))).
  { assert (Hle : QleT' (Z.of_nat (2 * j + 1)%nat # 1)
                        (Z.of_nat (2 * j + 3)%nat # 1))
      by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
    apply (rtb_qleT_trans _
             ((Z.of_nat (2 * j + 1)%nat # 1)
                / ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))).
    - apply qeq_leT'. apply qeq_imp_qeqT. unfold Qdiv. field.
      + split.
        * exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 3)%nat # 1) Hdd).
        * exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 1)%nat # 1) Hd1).
    - (* for the common denominator [d1 * dd], the order [d1 <= dd] gives [d1 / (d1 * dd) <= dd / (d1 * dd) = 1 / d1], by order-preserving division and ring normalization. *)
      apply (rtb_qleT_trans _
               ((Z.of_nat (2 * j + 3)%nat # 1)
                  / ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))).
      + apply (rtb_qleT_div_r
                   (Z.of_nat (2 * j + 1)%nat # 1)
                   (Z.of_nat (2 * j + 3)%nat # 1)
                   ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1))).
        * exact Hle.
        * exact Hprod.
      + apply qeq_leT'. apply qeq_imp_qeqT. unfold Qdiv. field.
        * split.
          -- exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 1)%nat # 1) Hd1).
          -- exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 3)%nat # 1) Hdd). }
  apply (rtb_qleT_trans _
           (q_pow (Qabs x) (2 * j + 3)%nat * (1 / (Z.of_nat (2 * j + 1)%nat # 1)))).
  - apply (rtb_qleT_trans _
             (q_pow (Qabs x) (2 * j + 3)%nat * (1 / (Z.of_nat (2 * j + 3)%nat # 1)))).
    + apply qeq_leT'. apply qeq_imp_qeqT. unfold Qdiv. ring.
    + apply rtb_qleT_mult_l; [exact Hsub | exact HP0].
  - apply qeq_leT'. apply qeq_imp_qeqT. rewrite Hp. unfold Qdiv. ring.
Qed.

(* Index-shift certificate: [u (S j) <= x²·u j] for [u j := atan_mag (S (m + j)) x], *)
(*   by [rtb_atan_ratio] at [j' := m + S j] and the square/absolute-value switch of [atan_sq_abs]. *)
Lemma rtb_atan_cert : forall (x : Q) (m j : nat),
  QleT' (atan_mag (Datatypes.S (m + Datatypes.S j)%nat) x)
        ((x * x) * atan_mag (Datatypes.S (m + j)%nat) x).
Proof.
  intros x m j.
  pose proof (rtb_atan_ratio x (m + Datatypes.S j)%nat) as Hr.
  apply (rtb_qleT_trans _ ((Qabs x * Qabs x) * atan_mag (m + Datatypes.S j)%nat x)).
  - exact Hr.
  - apply qeq_leT'. apply qeq_imp_qeqT.
    replace (m + Datatypes.S j)%nat with (Datatypes.S (m + j)) by lia.
    pose proof (qeqT_imp_qeq (x * x) (Qabs x * Qabs x) (atan_sq_abs x)) as Hsq.
    rewrite Hsq. reflexivity.
Qed.

(* The arctangent site instance at the Q layer, running through [rtb_ratio_tail_Q] proper: *)
(*   for [|x| < 1], Σ_{k<d} atan_mag (S (m+k)) x ≤ atan_mag (S m) x·(1-(x²)^d)/(1-x²). *)
Lemma rtb_atan_inst : forall (x : Q) (m d : nat),
  QltT (Qabs x) 1 ->
  QleT' (rtb_tsum (fun j => atan_mag (Datatypes.S (m + j)%nat) x) 0%nat d)
        (atan_mag (Datatypes.S m) x * ((1 - q_pow (x * x) d) / (1 - x * x))).
Proof.
  intros x m d Hx.
  assert (Hrho0 : QleT' 0 (x * x)).
  { apply (rtb_qleT_trans _ (Qabs x * Qabs x)).
    - apply Qle_to_QleT'. apply Qmult_le_0_compat; apply Qabs_nonneg.
    - apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym.
      apply (qeqT_imp_qeq _ _ (atan_sq_abs x)). }
  assert (Hrho1 : QltT (x * x) 1).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans (x * x) (Qabs x * 1) (1 * 1)).
    - apply (Qle_trans (x * x) (Qabs x * Qabs x) (Qabs x * 1)).
      + apply QleT'_to_Qle. apply qeq_le. apply atan_sq_abs.
      + rewrite (Qmult_comm (Qabs x) 1).
        apply Qmult_le_compat_r.
        * apply Qlt_le_weak. apply QltT_to_Qlt. exact Hx.
        * apply Qabs_nonneg.
    - apply (Qmult_lt_compat_r (Qabs x) 1 1).
      + unfold Qlt. simpl. lia.
      + apply QltT_to_Qlt. exact Hx. }
  assert (Hcert : forall j : nat,
            QleT' (atan_mag (Datatypes.S (m + Datatypes.S j)%nat) x)
                  ((x * x) * atan_mag (Datatypes.S (m + j)%nat) x))
    by (intro j; apply rtb_atan_cert).
  pose proof (rtb_ratio_tail_Q
                (fun j => atan_mag (Datatypes.S (m + j)%nat) x) (x * x) d 0%nat
                Hrho0 Hrho1 Hcert) as Hmother.
  cbv beta in Hmother.
  apply QleT'_to_Qle in Hmother.
  assert (Hu0 : atan_mag (Datatypes.S (m + 0)%nat) x
                  * ((1 - q_pow (x * x) d) / (1 - x * x))
                == atan_mag (Datatypes.S m) x
                  * ((1 - q_pow (x * x) d) / (1 - x * x)))
    by (replace (m + 0)%nat with m by lia; reflexivity).
  apply Qle_to_QleT'.
  exact (rtb_qle_eq_r
           (rtb_tsum (fun j => atan_mag (Datatypes.S (m + j)%nat) x) 0%nat d)
           (atan_mag (Datatypes.S (m + 0)%nat) x
              * ((1 - q_pow (x * x) d) / (1 - x * x)))
           (atan_mag (Datatypes.S m) x
              * ((1 - q_pow (x * x) d) / (1 - x * x)))
           Hmother Hu0).
Qed.

(* ============================================================ *)
(* Audit exits: [Print Assumptions] for the main statements. *)
(* ============================================================ *)

Print Assumptions rtb_ratio_tail_Q_mult.
Print Assumptions rtb_ratio_tail_Q.
Print Assumptions rtb_ratio_tail_real.
Print Assumptions rtb_exp_inst.
Print Assumptions rtb_exp_real_inst.
Print Assumptions rtb_atan_inst.
