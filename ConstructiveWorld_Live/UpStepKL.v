(* ConstructiveWorld-Set -- real-layer exponential alignment and policy-iteration KL decay. *)

(** * UpStepKL: real-layer resolution of step_kl_eta_bound with geometric iteration.

    Mission.  Real-layer resolution of [step_kl_eta_bound] together with the
      iterative companion of the [step_kl] family: two-point convexity of
      [cauchy_real_exp] ([real_exp_two_point_cvx_eps]), pointwise AM-GM
      ([real_amgm_pointwise_eps]), the summed interpolation bound
      ([real_interp_Z_le_one_eps]), the exact KL identity and eps bound
      [real_step_kl_eta_bound_eps] for the geometric interpolation update
      [real_step_next], and the geometric-rate iteration theorems
      [real_iter_step_geom_eps], [real_iter_kl_step], [real_iter_kl_geom].

    Dependencies.  Stdlib [List], [QArith.Qring]; requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, UpStepKL.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpStepKL.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Import RealInterfaceEnhancedMod.

(* ================= Section 1. Bridges from real_lt and real_eq to real_le ================= *)

Lemma kl_lt_le_bridge : forall a b : Real, real_lt a b -> real_le a b.
Proof. intros a b H. unfold real_le. exact (inl H). Qed.

Lemma kl_eq_le_bridge : forall a b : Real, real_eq a b -> real_le a b.
Proof. intros a b H. unfold real_le. exact (inr H). Qed.

Lemma kl_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof. intros a b c Hab Hbc. unfold real_le in Hab |- *.
  destruct Hab as [Hlt | Heq].
  - exact (inl (RealSetoid.real_lt_compat a a b c (real_eq_refl a) Hbc Hlt)).
  - exact (inr (real_eq_trans a b c Heq Hbc)). Qed.

Lemma kl_le_eq_l : forall a b c : Real,
  real_le a b -> real_eq a c -> real_le c b.
Proof.
  intros a b c Hab Hac.
  exact (real_le_trans c a b (inr (real_eq_sym a c Hac)) Hab).
  Qed.

(* ================= Section 2. Ring identity family (pointwise [ring] via real_eq_of_zero_diff) ================= *)

Lemma kl_zero_plus_zero : real_eq (real_plus real_zero real_zero) real_zero.
Proof. apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof. intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof. intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

(* (1−η) + η == 1 *)
Lemma kl_ring_m_plus_eta : forall eta : Real,
  real_eq (real_plus (real_plus real_one (real_opp eta)) eta) real_one.
Proof. intros eta. destruct eta as [v Hv]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

(* Varberg cone master identity: E·m̂·(1+ηs) + E·η·(1+m̂·(−s)) == E, with m̂ := 1−η expanded *)
Lemma kl_ring_core : forall (E eta s : Real),
  real_eq (real_plus
    (real_mult (real_mult E (real_plus real_one (real_opp eta)))
               (real_plus real_one (real_mult eta s)))
    (real_mult (real_mult E eta)
               (real_plus real_one
                 (real_mult (real_plus real_one (real_opp eta)) (real_opp s)))))
    E.
Proof. intros E eta s. destruct E as [u Hu]. destruct eta as [v Hv]. destruct s as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

(* z + η·s == x where z := (1−η)x + ηy and s := x−y *)
Lemma kl_z_tA : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult eta (real_plus x (real_opp y)))) x.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

(* z + (1−η)·(−s) == y *)
Lemma kl_z_tB : forall x y eta : Real,
  real_eq (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                (real_mult eta y))
                     (real_mult (real_plus real_one (real_opp eta))
                                (real_opp (real_plus x (real_opp y))))) y.
Proof. intros x y eta. destruct x as [u Hu]. destruct y as [v Hv]. destruct eta as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_sum_prod_r : forall a b w : Real,
  real_eq (real_plus (real_mult a w) (real_mult b w)) (real_mult (real_plus a b) w).
Proof. intros a b w. destruct a as [u Hu]. destruct b as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_swap3 : forall c e w : Real,
  real_eq (real_mult c (real_mult e w)) (real_mult e (real_mult c w)).
Proof. intros c e w. destruct c as [u Hu]. destruct e as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_assoc_swap : forall E m w : Real,
  real_eq (real_mult (real_mult E m) w) (real_mult m (real_mult E w)).
Proof. intros E m w. destruct E as [u Hu]. destruct m as [v Hv]. destruct w as [w' Hw'].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

(* ================= Section 3. Order helpers ================= *)

(* η ≤ 1 ⟹ 0 ≤ 1−η, branchwise on the sum encoding of real_le *)
Lemma kl_one_minus_eta_nonneg : forall eta : Real,
  real_le eta real_one -> real_le real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hle. destruct Hle as [Hlt | Heq].
  - exact (inl (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))
                  (real_plus real_one (real_opp eta))
                  (real_eq_sym (real_plus eta (real_opp eta)) real_zero
                     (real_plus_opp eta))
                  (real_lt_plus_compat_lt_le eta real_one (real_opp eta) (real_opp eta)
                    Hlt (real_le_refl (real_opp eta))))).
  - exact (inr (real_eq_sym (real_plus real_one (real_opp eta)) real_zero
                    (real_eq_trans (real_plus real_one (real_opp eta))
                                 (real_plus eta (real_opp eta)) real_zero
                    (RealSetoid.real_eq_plus_compat real_one (real_opp eta)
                       eta (real_opp eta)
                       (real_eq_sym eta real_one Heq) (real_eq_refl (real_opp eta)))
                    (real_plus_opp eta)))).
Qed.

(* 0 ≤ a and 0 < b ⟹ 0 < a+b *)
Lemma kl_le_lt_plus : forall a b : Real,
  real_le real_zero a -> real_lt real_zero b ->
  real_lt real_zero (real_plus a b).
Proof.
  intros a b Ha Hb. destruct Ha as [Hlt | Heq].
  - exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b)
             kl_zero_plus_zero
             (real_lt_plus_compat real_zero a real_zero b Hlt Hb)).
  - apply (real_lt_eq_lt real_zero b (real_plus a b) Hb).
    exact (real_eq_sym (real_plus a b) b
             (real_eq_trans (real_plus a b) (real_plus real_zero b) b
                (RealSetoid.real_eq_plus_compat a b real_zero b
                   (real_eq_sym real_zero a Heq) (real_eq_refl b))
                (kl_plus_zero_l b))).
Qed.

(* 0 ≤ m and 0 < E ⟹ 0 ≤ E·m (order-weak multiplication composed with an eq exchange) *)
Lemma kl_le_mult_weak_swap : forall m E : Real,
  real_le real_zero m -> real_lt real_zero E -> real_le real_zero (real_mult E m).
Proof.
  intros m E Hm HE.
  exact (kl_le_eq_r real_zero (real_mult m E) (real_mult E m)           (kl_le_eq_l (real_mult real_zero E) (real_mult m E) real_zero              (real_le_mult_compat_weak real_zero m E (inl HE) Hm)              (kl_mult_zero_l E))           (real_mult_comm m E)).
Qed.

(* seed bound multiplied by a nonnegative factor: c·(1+t) ≤ c·e^t + c·δ *)
Lemma kl_seed_mul : forall (c t e2 : Real),
  real_le real_zero c -> real_lt real_zero e2 ->
  real_le (real_mult c (real_plus real_one t))
          (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)).
Proof.
  intros c t e2 Hc0 He2.
  assert (Hseed : real_le (real_plus real_one t) (real_plus (cauchy_real_exp t) e2))
    by (apply real_exp_ge_linear_eps; exact He2).
  assert (Hab : real_le (real_mult (real_plus real_one t) c)
                        (real_mult (real_plus (cauchy_real_exp t) e2) c))
    by (exact (real_le_mult_compat_weak (real_plus real_one t)
                 (real_plus (cauchy_real_exp t) e2) c Hc0 Hseed)).
  assert (Hdis : real_eq (real_mult (real_plus (cauchy_real_exp t) e2) c)
                         (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2)))
    by (exact (real_eq_trans
                 (real_mult (real_plus (cauchy_real_exp t) e2) c)
                 (real_plus (real_mult (cauchy_real_exp t) c) (real_mult e2 c))
                 (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                 (kl_distrib_r (cauchy_real_exp t) e2 c)
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (cauchy_real_exp t) c) (real_mult e2 c)
                    (real_mult c (cauchy_real_exp t)) (real_mult c e2)
                    (real_mult_comm (cauchy_real_exp t) c)
                    (real_mult_comm e2 c)))).
  apply (kl_le_eq_l (real_mult (real_plus real_one t) c)
                    (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                    (real_mult c (real_plus real_one t))).
  - apply (kl_le_eq_r (real_mult (real_plus real_one t) c)
                      (real_mult (real_plus (cauchy_real_exp t) e2) c)
                      (real_plus (real_mult c (cauchy_real_exp t)) (real_mult c e2))
                      Hab Hdis).
  - apply real_mult_comm.
Qed.


(* ================= Section 4. Two-point convexity kernel (Varberg cone) =================
   e^{(1−η)x+ηy} ≤ (1−η)·e^x + η·e^y + eps.
   This is the true direction of the exponential form of AM-GM; the reversed
   inequality (1−η)e^x+ηe^y ≤ e^z+eps runs Jensen backwards and fails in
   general. The proof is the Varberg cone argument: multiply the two seed
   bounds by e^z > 0 and merge them with the weights. *)
Lemma real_exp_two_point_cvx_eps : forall (x y eta : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                      (real_mult eta y)))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                            (cauchy_real_exp x))
                                (real_mult eta (cauchy_real_exp y)))
                     eps).
Proof.
  intros x y eta Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (z := real_plus (real_mult m x) (real_mult eta y)).
  set (s := real_plus x (real_opp y)).
  set (tA := real_mult eta s).
  set (tB := real_mult m (real_opp s)).
  assert (HEpos : real_lt real_zero (cauchy_real_exp z)) by apply cauchy_real_exp_pos.
  set (E := cauchy_real_exp z).
  set (cA := real_mult E m).
  set (cB := real_mult E eta).
  assert (Hm0 : real_le real_zero m)
    by exact (kl_one_minus_eta_nonneg eta Heta_le).
  assert (HcA0 : real_le real_zero cA) by exact (kl_le_mult_weak_swap m E Hm0 HEpos).
  assert (HcBpos : real_lt real_zero cB)
    by exact (real_mult_positive E eta HEpos Heta_pos).
  set (c := real_plus cA cB).
  assert (Hcpos : real_lt real_zero c) by exact (kl_le_lt_plus cA cB HcA0 HcBpos).
  set (d := real_mult eps (real_inv_pos c Hcpos)).
  assert (Hdpos : real_lt real_zero d)
    by exact (real_mult_positive eps (real_inv_pos c Hcpos) Heps
                (real_inv_pos_pos c Hcpos)).
  (* each seed bound multiplied by cA / cB, then the results added *)
  assert (HseedA : real_le (real_mult cA (real_plus real_one tA))
                           (real_plus (real_mult cA (cauchy_real_exp tA))
                                      (real_mult cA d)))
    by exact (kl_seed_mul cA tA d HcA0 Hdpos).
  assert (HseedB : real_le (real_mult cB (real_plus real_one tB))
                           (real_plus (real_mult cB (cauchy_real_exp tB))
                                      (real_mult cB d)))
    by exact (kl_seed_mul cB tB d (inl HcBpos) Hdpos).
  assert (Hsumle : real_le (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                 (real_mult cA d))
                                      (real_plus (real_mult cB (cauchy_real_exp tB))
                                                 (real_mult cB d))))
    by exact (real_le_plus_compat _ _ _ _ HseedA HseedB).
  (* cone identity: the weighted left side equals E (pure ring once m is expanded) *)
  assert (EqCore : real_eq (real_plus (real_mult cA (real_plus real_one tA))
                                      (real_mult cB (real_plus real_one tB)))
                           E)
    by exact (kl_ring_core E eta s).
  (* exponential regrouping: E·e^{tA} == e^x and E·e^{tB} == e^y *)
  assert (HEqA : real_eq (real_mult E (cauchy_real_exp tA)) (cauchy_real_exp x))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tA))
                            (cauchy_real_exp (real_plus z tA)) (cauchy_real_exp x)
                 (real_eq_sym (cauchy_real_exp (real_plus z tA))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tA))
                              (cauchy_real_exp_plus z tA))
                 (cauchy_real_exp_wd (real_plus z tA) x (kl_z_tA x y eta))).
  assert (HEqB : real_eq (real_mult E (cauchy_real_exp tB)) (cauchy_real_exp y))
    by exact (real_eq_trans (real_mult E (cauchy_real_exp tB))
                            (cauchy_real_exp (real_plus z tB)) (cauchy_real_exp y)
                 (real_eq_sym (cauchy_real_exp (real_plus z tB))
                              (real_mult (cauchy_real_exp z) (cauchy_real_exp tB))
                              (cauchy_real_exp_plus z tB))
                 (cauchy_real_exp_wd (real_plus z tB) y (kl_z_tB x y eta))).
  (* error absorption: cA·d + cB·d == eps, with d := eps·(1/c) *)
  assert (ErrEq : real_eq (real_plus (real_mult cA d) (real_mult cB d)) eps)
    by exact (real_eq_trans (real_plus (real_mult cA d) (real_mult cB d))
                            (real_mult c d) eps
                 (kl_sum_prod_r cA cB d)
                 (real_eq_trans (real_mult c d)
                    (real_mult eps (real_mult c (real_inv_pos c Hcpos))) eps
                    (kl_swap3 c eps (real_inv_pos c Hcpos))
                    (real_eq_trans
                       (real_mult eps (real_mult c (real_inv_pos c Hcpos)))
                       (real_mult eps real_one) eps
                       (RealSetoid.real_eq_mult_compat eps
                          (real_mult c (real_inv_pos c Hcpos)) eps real_one
                          (real_eq_refl eps) (real_inv_pos_correct c Hcpos))
                       (real_mult_one eps)))).
  (* final eq assembly: four-term rearrangement, exponential regrouping and error absorption *)
  assert (EqFinal : real_eq (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                                  (real_mult cA d))
                                       (real_plus (real_mult cB (cauchy_real_exp tB))
                                                  (real_mult cB d)))
                            (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                                  (real_mult eta (cauchy_real_exp y)))
                                       eps)).
  { apply (real_eq_trans
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                        (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
             (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                   (real_mult cB (cauchy_real_exp tB)))
                        (real_plus (real_mult cA d) (real_mult cB d)))
             (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                   (real_mult eta (cauchy_real_exp y))) eps)).
    - exact (real_plus_swap_mid (real_mult cA (cauchy_real_exp tA)) (real_mult cA d)
                                (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)).
    - exact (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult cA (cauchy_real_exp tA))
                          (real_mult cB (cauchy_real_exp tB)))
               (real_plus (real_mult cA d) (real_mult cB d))
               (real_plus (real_mult m (cauchy_real_exp x))
                          (real_mult eta (cauchy_real_exp y)))
               eps
               (RealSetoid.real_eq_plus_compat
                  (real_mult cA (cauchy_real_exp tA))
                  (real_mult cB (cauchy_real_exp tB))
                  (real_mult m (cauchy_real_exp x))
                  (real_mult eta (cauchy_real_exp y))
                  (real_eq_trans (real_mult cA (cauchy_real_exp tA))
                                 (real_mult m (real_mult E (cauchy_real_exp tA)))
                                 (real_mult m (cauchy_real_exp x))
                    (kl_assoc_swap E m (cauchy_real_exp tA))
                    (RealSetoid.real_eq_mult_compat m
                       (real_mult E (cauchy_real_exp tA)) m (cauchy_real_exp x)
                       (real_eq_refl m) HEqA))
                  (real_eq_trans (real_mult cB (cauchy_real_exp tB))
                                 (real_mult eta (real_mult E (cauchy_real_exp tB)))
                                 (real_mult eta (cauchy_real_exp y))
                    (kl_assoc_swap E eta (cauchy_real_exp tB))
                    (RealSetoid.real_eq_mult_compat eta
                       (real_mult E (cauchy_real_exp tB)) eta (cauchy_real_exp y)
                       (real_eq_refl eta) HEqB)))
               ErrEq). }
  exact (kl_le_eq_r E
           (real_plus (real_plus (real_mult cA (cauchy_real_exp tA)) (real_mult cA d))
                      (real_plus (real_mult cB (cauchy_real_exp tB)) (real_mult cB d)))
           (real_plus (real_plus (real_mult m (cauchy_real_exp x))
                                 (real_mult eta (cauchy_real_exp y))) eps)
           (kl_le_eq_l
              (real_plus (real_mult cA (real_plus real_one tA))
                         (real_mult cB (real_plus real_one tB)))
              (real_plus (real_plus (real_mult cA (cauchy_real_exp tA))
                                    (real_mult cA d))
                         (real_plus (real_mult cB (cauchy_real_exp tB))
                                    (real_mult cB d)))
              E Hsumle EqCore)
           EqFinal).
Qed.

(* ================= Section 5. Pointwise AM-GM =================
   a^{1−η}·b^η ≤ (1−η)·a + η·b + eps, where a^{α} := e^{α·log a} *)
Definition real_pow_pos (a alpha : Real) (Ha : real_lt real_zero a) : Real :=
  cauchy_real_exp (real_mult alpha (cw_log a Ha)).

Lemma real_amgm_pointwise_eps : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                     (real_pow_pos b eta Hb))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                (real_mult eta b)) eps).
Proof.
  intros a b eta Ha Hb Heta_pos Heta_le eps Heps.
  assert (Hcvx : real_le
            (cauchy_real_exp (real_plus
               (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
               (real_mult eta (cw_log b Hb))))
            (real_plus (real_plus
               (real_mult (real_plus real_one (real_opp eta))
                          (cauchy_real_exp (cw_log a Ha)))
               (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps))
    by exact (real_exp_two_point_cvx_eps (cw_log a Ha) (cw_log b Hb) eta
                Heta_pos Heta_le eps Heps).
  exact (kl_le_eq_r
           (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                      (real_pow_pos b eta Hb))
           (real_plus (real_plus
                        (real_mult (real_plus real_one (real_opp eta))
                                   (cauchy_real_exp (cw_log a Ha)))
                        (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                 (real_mult eta b)) eps)
           (kl_le_eq_l
              (cauchy_real_exp (real_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
              (real_plus (real_plus
                            (real_mult (real_plus real_one (real_opp eta))
                                       (cauchy_real_exp (cw_log a Ha)))
                            (real_mult eta (cauchy_real_exp (cw_log b Hb)))) eps)
              (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                         (real_pow_pos b eta Hb))
              Hcvx
              (cauchy_real_exp_plus
                 (real_mult (real_plus real_one (real_opp eta)) (cw_log a Ha))
                 (real_mult eta (cw_log b Hb))))
           (RealSetoid.real_eq_plus_compat
              (real_plus (real_mult (real_plus real_one (real_opp eta))
                                    (cauchy_real_exp (cw_log a Ha)))
                         (real_mult eta (cauchy_real_exp (cw_log b Hb))))
              eps
              (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                         (real_mult eta b))
              eps
              (RealSetoid.real_eq_plus_compat
                 (real_mult (real_plus real_one (real_opp eta))
                            (cauchy_real_exp (cw_log a Ha)))
                 (real_mult eta (cauchy_real_exp (cw_log b Hb)))
                 (real_mult (real_plus real_one (real_opp eta)) a)
                 (real_mult eta b)
                 (RealSetoid.real_eq_mult_compat
                    (real_plus real_one (real_opp eta))
                    (cauchy_real_exp (cw_log a Ha))
                    (real_plus real_one (real_opp eta)) a
                    (real_eq_refl (real_plus real_one (real_opp eta)))
                    (cw_log_exp_right a Ha))
                 (RealSetoid.real_eq_mult_compat eta
                    (cauchy_real_exp (cw_log b Hb)) eta b
                    (real_eq_refl eta) (cw_log_exp_right b Hb)))
              (real_eq_refl eps))).
Qed.

(* ================= Section 6. Summed interpolation inequality (Z ≤ 1 + eps) =================
   Z := Σ_i π_t(i)^{1−η}·π*(i)^η ≤ 1 + eps.
   Error absorption: each pointwise error carries the weight eps·π_t(i),
   a positive weight, so once the normalization Σπ_t == 1 is applied the
   total error is Σ(eps·π_t) == eps·1 == eps — no division and no
   bisection, absorption by normalization alone. *)
Lemma real_interp_Z_le_one_eps :
  forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (real_list_sum nat pit (seq 0 n)) real_one)
    (Hnormq : real_eq (real_list_sum nat pist (seq 0 n)) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_mult
                (real_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                (real_pow_pos (pist i) eta (Hpist i)))
             (seq 0 n))
          (real_plus real_one eps).
Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  (* pointwise AM-GM with the error term weighted by eps·pit i *)
  assert (Hpt : forall i : nat,
            real_le (real_mult (real_pow_pos (pit i) m (Hpit i))
                               (real_pow_pos (pist i) eta (Hpist i)))
                    (real_plus (real_plus (real_mult m (pit i))
                                          (real_mult eta (pist i)))
                               (real_mult eps (pit i)))).
  { intro i.
    exact (real_amgm_pointwise_eps (pit i) (pist i) eta (Hpit i) (Hpist i)
             Heta_pos Heta_le (real_mult eps (pit i))
             (real_mult_positive eps (pit i) Heps (Hpit i))). }
  assert (Hsumle : real_le
            (real_list_sum nat (fun i : nat => real_mult
                                  (real_pow_pos (pit i) m (Hpit i))
                                  (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n)))
    by exact (real_list_sum_le nat _ _ (seq 0 n) Hpt).
  (* Qsum == Σf + Σg where f i := m·pit i + η·pist i and g i := eps·pit i *)
  assert (Hsplit : real_eq
            (real_list_sum nat (fun i : nat => real_plus
                                  (real_plus (real_mult m (pit i))
                                             (real_mult eta (pist i)))
                                  (real_mult eps (pit i))) (seq 0 n))
            (real_plus (real_list_sum nat (fun i : nat => real_plus
                                              (real_mult m (pit i))
                                              (real_mult eta (pist i))) (seq 0 n))
                       (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                          (seq 0 n))))
    by exact (real_list_sum_add nat _ _ (seq 0 n)).
  (* Σf == m·Σpit + η·Σpist == m + η == 1 *)
  assert (Hf : real_eq (real_list_sum nat (fun i : nat => real_plus
                                             (real_mult m (pit i))
                                             (real_mult eta (pist i))) (seq 0 n))
                       real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum nat (fun i : nat => real_mult m (pit i)) (seq 0 n))
                        (real_list_sum nat (fun i : nat => real_mult eta (pist i)) (seq 0 n)))).
    - exact (real_list_sum_add nat _ _ (seq 0 n)).
    - apply (real_eq_trans _
                (real_plus (real_mult m (real_list_sum nat pit (seq 0 n)))
                           (real_mult eta (real_list_sum nat pist (seq 0 n))))).
      + exact (RealSetoid.real_eq_plus_compat _ _ _ _
                   (real_list_sum_linear nat m pit (seq 0 n))
                   (real_list_sum_linear nat eta pist (seq 0 n))).
      + apply (real_eq_trans _ (real_plus m eta)).
        * exact (RealSetoid.real_eq_plus_compat
                    (real_mult m (real_list_sum nat pit (seq 0 n)))
                    (real_mult eta (real_list_sum nat pist (seq 0 n))) m eta
                    (real_eq_trans (real_mult m (real_list_sum nat pit (seq 0 n)))
                       (real_mult m real_one) m
                       (RealSetoid.real_eq_mult_compat m
                          (real_list_sum nat pit (seq 0 n)) m real_one
                          (real_eq_refl m) Hnormp)
                       (real_mult_one m))
                    (real_eq_trans (real_mult eta (real_list_sum nat pist (seq 0 n)))
                       (real_mult eta real_one) eta
                       (RealSetoid.real_eq_mult_compat eta
                          (real_list_sum nat pist (seq 0 n)) eta real_one
                          (real_eq_refl eta) Hnormq)
                       (real_mult_one eta))).
        * exact (kl_ring_m_plus_eta eta). }
  (* Σg == eps·Σpit == eps·1 == eps *)
  assert (Hg : real_eq (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n)) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum nat pit (seq 0 n)))).
    - exact (real_list_sum_linear nat eps pit (seq 0 n)).
    - exact (real_eq_trans (real_mult eps (real_list_sum nat pit (seq 0 n)))
                           (real_mult eps real_one) eps
               (RealSetoid.real_eq_mult_compat eps (real_list_sum nat pit (seq 0 n))
                  eps real_one (real_eq_refl eps) Hnormp)
               (real_mult_one eps)). }
  (* closing step: Z ≤ Σf + Σg == 1 + eps *)
  exact (kl_le_eq_r
           (real_list_sum nat (fun i : nat => real_mult
                                 (real_pow_pos (pit i) m (Hpit i))
                                 (real_pow_pos (pist i) eta (Hpist i))) (seq 0 n))
           (real_list_sum nat (fun i : nat => real_plus
                                 (real_plus (real_mult m (pit i))
                                            (real_mult eta (pist i)))
                                 (real_mult eps (pit i))) (seq 0 n))
           (real_plus real_one eps)
           Hsumle
           (real_eq_trans
              (real_list_sum nat (fun i : nat => real_plus
                                    (real_plus (real_mult m (pit i))
                                               (real_mult eta (pist i)))
                                    (real_mult eps (pit i))) (seq 0 n))
              (real_plus (real_list_sum nat (fun i : nat => real_plus
                                                (real_mult m (pit i))
                                                (real_mult eta (pist i))) (seq 0 n))
                         (real_list_sum nat (fun i : nat => real_mult eps (pit i))
                            (seq 0 n)))
              (real_plus real_one eps)
              Hsplit
              (RealSetoid.real_eq_plus_compat
                 (real_list_sum nat (fun i : nat => real_plus
                                       (real_mult m (pit i))
                                       (real_mult eta (pist i))) (seq 0 n))
                 (real_list_sum nat (fun i : nat => real_mult eps (pit i)) (seq 0 n))
                 real_one eps Hf Hg))).
Qed.

(* ================= Section 7. Log algebra and ring identities ================= *)

(* a + b == 0 ⟹ b == −a *)
Lemma kl_eq_plus_opp_uniq_r : forall a b : Real,
  real_eq (real_plus a b) real_zero -> real_eq b (real_opp a).
Proof.
  intros a b H.
  assert (Hstep1 : real_eq (real_plus (real_opp a) (real_plus a b))
                           (real_plus (real_opp a) real_zero))
    by exact (RealSetoid.real_eq_plus_compat (real_opp a) (real_plus a b)
                (real_opp a) real_zero (real_eq_refl (real_opp a)) H).
  assert (Hstep2 : real_eq (real_plus (real_opp a) real_zero) (real_opp a))
    by exact (real_plus_zero (real_opp a)).
  assert (Hstep3 : real_eq (real_plus (real_opp a) (real_plus a b)) b).
  { exact (real_eq_trans (real_plus (real_opp a) (real_plus a b))
                         (real_plus (real_plus (real_opp a) a) b) b
             (real_plus_assoc (real_opp a) a b)
             (real_eq_trans (real_plus (real_plus (real_opp a) a) b)
                            (real_plus real_zero b) b
                (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) a) b
                   real_zero b
                   (real_eq_trans (real_plus (real_opp a) a)
                      (real_plus a (real_opp a)) real_zero
                      (real_plus_comm (real_opp a) a) (real_plus_opp a))
                   (real_eq_refl b))
                (kl_plus_zero_l b))). }
  exact (real_eq_trans b (real_plus (real_opp a) (real_plus a b)) (real_opp a)
           (real_eq_sym _ _ Hstep3) (real_eq_trans _ _ _ Hstep1 Hstep2)).
Qed.


Lemma kl_log_inv : forall (x : Real) (Hx : real_lt real_zero x)
    (Hix : real_lt real_zero (real_inv_pos x Hx)),
  real_eq (cw_log (real_inv_pos x Hx) Hix) (real_opp (cw_log x Hx)).
Proof.
  intros x Hx Hix.
  assert (Hprodpos : real_lt real_zero (real_mult x (real_inv_pos x Hx)))
    by exact (real_mult_positive x (real_inv_pos x Hx) Hx Hix).
  assert (Hmult : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                           (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)))
    by exact (log_inv_mult_thm x (real_inv_pos x Hx) Hx Hix Hprodpos).
  assert (Hone : real_eq (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero).
  { apply (real_eq_trans _ (cw_log real_one real_lt_zero_one)).
    - exact (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one Hprodpos
                real_lt_zero_one (real_inv_pos_correct x Hx)).
    - exact (real_log_one real_lt_zero_one). }
  exact (kl_eq_plus_opp_uniq_r (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)
           (real_eq_trans (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix))
              (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos) real_zero
              (real_eq_sym
                 (cw_log (real_mult x (real_inv_pos x Hx)) Hprodpos)
                 (real_plus (cw_log x Hx) (cw_log (real_inv_pos x Hx) Hix)) Hmult)
              Hone)).
Qed.

(* ring identity family *)
Lemma kl_ring_reassoc : forall X Y Z W : Real,
  real_eq (real_mult (real_mult (real_mult X Y) Z) W)
          (real_mult X (real_mult Y (real_mult Z W))).
Proof. intros X Y Z W. destruct X as [a Ha]. destruct Y as [b Hb]. destruct Z as [c Hc].
  destruct W as [d Hd]. apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_opp_swap : forall X Y : Real,
  real_eq (real_opp (real_plus X (real_opp Y))) (real_plus Y (real_opp X)).
Proof. intros X Y. destruct X as [a Ha]. destruct Y as [b Hb].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_log4 : forall eta lp lr LZ : Real,
  real_eq (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                     (real_plus (real_mult eta lr)
                                (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                (real_mult eta lr))
                     (real_plus (real_opp LZ) (real_opp lp))).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_neg4 : forall eta lp lr LZ : Real,
  real_eq (real_opp (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) lp)
                                          (real_mult eta lr))
                               (real_plus (real_opp LZ) (real_opp lp))))
          (real_plus (real_mult eta (real_plus lp (real_opp lr))) LZ).
Proof. intros eta lp lr LZ. destruct eta as [e He]. destruct lp as [u Hu].
  destruct lr as [v Hv]. destruct LZ as [w Hw]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.

Lemma kl_ring_kl_split : forall eta W X Z : Real,
  real_eq (real_mult W (real_plus (real_mult eta X) Z))
          (real_plus (real_mult eta (real_mult W X)) (real_mult W Z)).
Proof. intros eta W X Z. destruct eta as [e He]. destruct W as [w Hw].
  destruct X as [x Hx]. destruct Z as [z Hz]. apply real_eq_of_zero_diff.
  intro n. simpl. apply qeq_imp_qeqT. ring. Qed.


Lemma kl_log_le_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (real_log_lt_mono a b Ha Hb Hlt)).
  - exact (inr (real_log_wd a b Ha Hb Heq)).
Qed.

(* ================= Section 8. Exact KL identity assembly =================
   π_{t+1}(i) := π_t(i)^{1−η}·π*(i)^η / Z (geometric interpolation policy).
   Exact identity: KL(π_t‖π_{t+1}) == η·KL(π_t‖π★) + log Z, by pointwise
   real_kl_term algebra plus the normalization absorption Σp == 1; combined
   with the interpolation bound Z ≤ 1+eps and the strict seed
   1+eps < e^eps this yields KL(π_t‖π_{t+1}) ≤ η·KL(π_t‖π★) + eps. *)

(* partition function of the geometric interpolation: Z := Σ_i π_t(i)^{1−η}·π*(i)^η *)
Definition real_interp_Z (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_mult
       (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
       (real_pow_pos (r i) eta (Hr i)))
    (seq 0 n).

(* next policy: π_{t+1}(i) := π_t(i)^{1−η}·π*(i)^η / Z *)
Definition real_step_next (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr)) : nat -> Real :=
  fun i : nat => real_mult
    (real_mult (real_pow_pos (p i) (real_plus real_one (real_opp eta)) (Hp i))
               (real_pow_pos (r i) eta (Hr i)))
    (real_inv_pos (real_interp_Z n p r eta Hp Hr) HZ).

Theorem real_step_kl_eta_bound_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (real_list_sum nat p (seq 0 n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (seq 0 n)) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum nat
             (fun i : nat => real_kl_term (p i)
                             (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i))
             (seq 0 n))
          (real_plus (real_mult eta
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                           (seq 0 n)))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  set (Z := real_interp_Z n p r eta Hp Hr).
  set (q := real_step_next n p r eta Hp Hr HZ).
  set (LZ := cw_log Z HZ).
  set (Rsum := real_list_sum nat
                 (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i)) (seq 0 n)).
  (* ---- pointwise KL identity (exact real_eq) ---- *)
  assert (Hpi : forall i : nat,
    real_eq (real_kl_term (p i) (q i) (Hp i) (Hqv i))
            (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                       (real_mult (p i) LZ))).
  { intro i.
    set (ipp := real_inv_pos (p i) (Hp i)).
    set (izz := real_inv_pos Z HZ).
    set (pA := real_pow_pos (p i) m (Hp i)).
    set (pB := real_pow_pos (r i) eta (Hr i)).
    
    assert (Hip : real_lt real_zero ipp) by exact (real_inv_pos_pos (p i) (Hp i)).
    assert (Hizp : real_lt real_zero izz) by exact (real_inv_pos_pos Z HZ).
    assert (HpA : real_lt real_zero pA)
      by exact (cauchy_real_exp_pos (real_mult m (cw_log (p i) (Hp i)))).
    assert (HpB : real_lt real_zero pB)
      by exact (cauchy_real_exp_pos (real_mult eta (cw_log (r i) (Hr i)))).
    set (Hqqlog := real_mult_positive (q i) (real_inv_pos (p i) (Hp i)) (Hqv i)
                  (real_inv_pos_pos (p i) (Hp i))).
    set (Hrplog := real_mult_positive (r i) (real_inv_pos (p i) (Hp i)) (Hr i)
                  (real_inv_pos_pos (p i) (Hp i))).
    
    assert (HlA : real_eq (cw_log pA HpA) (real_mult m (cw_log (p i) (Hp i))))
      by exact (log_inv_exp_neg_thm (real_mult m (cw_log (p i) (Hp i))) HpA).
    assert (HlB : real_eq (cw_log pB HpB) (real_mult eta (cw_log (r i) (Hr i))))
      by exact (log_inv_exp_neg_thm (real_mult eta (cw_log (r i) (Hr i))) HpB).
    assert (HlZ : real_eq (cw_log izz Hizp) (real_opp LZ))
      by exact (kl_log_inv Z HZ Hizp).
    assert (HlP : real_eq (cw_log ipp Hip) (real_opp (cw_log (p i) (Hp i))))
      by exact (kl_log_inv (p i) (Hp i) Hip).
    
    assert (Hlogrp : real_eq (cw_log (real_mult (r i) ipp) Hrplog)
                             (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i))))).
    { exact (real_eq_trans (cw_log (real_mult (r i) ipp) Hrplog)
               (real_plus (cw_log (r i) (Hr i)) (cw_log ipp Hip))
               (real_plus (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i))))
               (log_inv_mult_thm (r i) ipp (Hr i) Hip Hrplog)
               (RealSetoid.real_eq_plus_compat (cw_log (r i) (Hr i)) (cw_log ipp Hip)
                  (cw_log (r i) (Hr i)) (real_opp (cw_log (p i) (Hp i)))
                  (real_eq_refl (cw_log (r i) (Hr i))) HlP)). }
    (* product regrouping of q·inv p (pure ring) *)
    assert (Hring1 : real_eq (real_mult (q i) ipp)
                             (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (kl_ring_reassoc pA pB izz ipp).
    assert (Hpos3 : real_lt real_zero (real_mult izz ipp))
      by exact (real_mult_positive izz ipp Hizp Hip).
    assert (Hpos2 : real_lt real_zero (real_mult pB (real_mult izz ipp)))
      by exact (real_mult_positive pB (real_mult izz ipp) HpB Hpos3).
    assert (HAB4 : real_lt real_zero (real_mult pA (real_mult pB (real_mult izz ipp))))
      by exact (real_mult_positive pA (real_mult pB (real_mult izz ipp)) HpA Hpos2).
    
    assert (Hlog4 : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (cw_log pA HpA)
                          (real_plus (cw_log pB HpB)
                             (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))).
      - exact (real_log_wd (real_mult (q i) ipp)
                 (real_mult pA (real_mult pB (real_mult izz ipp))) Hqqlog HAB4 Hring1).
      - exact (real_eq_trans
                  (cw_log (real_mult pA (real_mult pB (real_mult izz ipp))) HAB4)
                  (real_plus (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2))
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (log_inv_mult_thm pA (real_mult pB (real_mult izz ipp)) HpA Hpos2 HAB4)
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                     (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_eq_refl (cw_log pA HpA))
                     (real_eq_trans
                        (cw_log (real_mult pB (real_mult izz ipp)) Hpos2)
                        (real_plus (cw_log pB HpB) (cw_log (real_mult izz ipp) Hpos3))
                        (real_plus (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                        (log_inv_mult_thm pB (real_mult izz ipp) HpB Hpos3 Hpos2)
                        (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                           (cw_log (real_mult izz ipp) Hpos3)
                           (cw_log pB HpB)
                           (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                           (real_eq_refl (cw_log pB HpB))
                           (log_inv_mult_thm izz ipp Hizp Hip Hpos3))))). }
    
    assert (Hlog4' : real_eq (cw_log (real_mult (q i) ipp) Hqqlog)
                       (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                             (real_mult eta (cw_log (r i) (Hr i))))
                                  (real_plus (real_opp LZ)
                                             (real_opp (cw_log (p i) (Hp i)))))).
    { apply (real_eq_trans (cw_log (real_mult (q i) ipp) Hqqlog)
               (real_plus (cw_log pA HpA)
                  (real_plus (cw_log pB HpB)
                     (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
               (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                     (real_mult eta (cw_log (r i) (Hr i))))
                          (real_plus (real_opp LZ)
                                     (real_opp (cw_log (p i) (Hp i)))))).
      - exact Hlog4.
      - exact (real_eq_trans
                  (real_plus (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))))
                  (real_plus (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))))
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  (RealSetoid.real_eq_plus_compat (cw_log pA HpA)
                     (real_plus (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip)))
                     (real_mult m (cw_log (p i) (Hp i)))
                     (real_plus (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                     HlA
                     (RealSetoid.real_eq_plus_compat (cw_log pB HpB)
                        (real_plus (cw_log izz Hizp) (cw_log ipp Hip))
                        (real_mult eta (cw_log (r i) (Hr i)))
                        (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i))))
                        HlB
                        (RealSetoid.real_eq_plus_compat (cw_log izz Hizp)
                           (cw_log ipp Hip) (real_opp LZ)
                           (real_opp (cw_log (p i) (Hp i))) HlZ HlP)))
                  (kl_ring_log4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    
    assert (Hneg : real_eq (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
                       (real_plus (real_mult eta
                                     (real_plus (cw_log (p i) (Hp i))
                                                (real_opp (cw_log (r i) (Hr i)))))
                                  LZ)).
    { exact (real_eq_trans (real_opp (cw_log (real_mult (q i) ipp) Hqqlog))
               (real_opp (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                                (real_mult eta (cw_log (r i) (Hr i))))
                                    (real_plus (real_opp LZ)
                                               (real_opp (cw_log (p i) (Hp i))))))
               (real_plus (real_mult eta
                             (real_plus (cw_log (p i) (Hp i))
                                        (real_opp (cw_log (r i) (Hr i)))))
                          LZ)
               (RealSetoid.real_eq_opp_compat
                  (cw_log (real_mult (q i) ipp) Hqqlog)
                  (real_plus (real_plus (real_mult m (cw_log (p i) (Hp i)))
                                        (real_mult eta (cw_log (r i) (Hr i))))
                     (real_plus (real_opp LZ) (real_opp (cw_log (p i) (Hp i)))))
                  Hlog4')
               (kl_ring_neg4 eta (cw_log (p i) (Hp i)) (cw_log (r i) (Hr i)) LZ)). }
    
    assert (HnegR : real_eq (real_plus (cw_log (p i) (Hp i))
                                       (real_opp (cw_log (r i) (Hr i))))
                            (real_opp (cw_log (real_mult (r i) ipp) Hrplog))).
    { exact (real_eq_trans
                (real_plus (cw_log (p i) (Hp i)) (real_opp (cw_log (r i) (Hr i))))
                (real_opp (real_plus (cw_log (r i) (Hr i))
                                     (real_opp (cw_log (p i) (Hp i)))))
                (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                (real_eq_sym (real_opp (real_plus (cw_log (r i) (Hr i))
                                                  (real_opp (cw_log (p i) (Hp i)))))
                   (real_plus (cw_log (p i) (Hp i))
                              (real_opp (cw_log (r i) (Hr i))))
                   (kl_ring_opp_swap (cw_log (r i) (Hr i)) (cw_log (p i) (Hp i))))
                (real_eq_sym (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                   (real_opp (real_plus (cw_log (r i) (Hr i))
                                        (real_opp (cw_log (p i) (Hp i)))))
                   (RealSetoid.real_eq_opp_compat
                      (cw_log (real_mult (r i) ipp) Hrplog)
                      (real_plus (cw_log (r i) (Hr i))
                                 (real_opp (cw_log (p i) (Hp i))))
                      Hlogrp))). }
    (* final assembly: kl(p,q) == η·kl(p,r) + p·LZ *)
    exact (real_eq_trans
              (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
              (real_plus
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ))
              (real_plus (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                         (real_mult (p i) LZ))
              (real_eq_trans
                 (real_mult (p i) (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)))
                 (real_mult (p i)
                    (real_plus (real_mult eta
                                  (real_plus (cw_log (p i) (Hp i))
                                             (real_opp (cw_log (r i) (Hr i)))))
                               LZ))
                 (real_plus
                    (real_mult eta
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))))
                    (real_mult (p i) LZ))
                 (RealSetoid.real_eq_mult_compat (p i)
                    (real_opp (cw_log (real_mult (q i) ipp) Hqqlog)) (p i)
                    (real_plus (real_mult eta
                                 (real_plus (cw_log (p i) (Hp i))
                                            (real_opp (cw_log (r i) (Hr i)))))
                               LZ)
                    (real_eq_refl (p i)) Hneg)
                 (kl_ring_kl_split eta (p i)
                    (real_plus (cw_log (p i) (Hp i))
                               (real_opp (cw_log (r i) (Hr i))))
                    LZ))
              (RealSetoid.real_eq_plus_compat
                 (real_mult eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i))))))
                 (real_mult (p i) LZ)
                 (real_mult eta (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                 (real_mult (p i) LZ)
                 (RealSetoid.real_eq_mult_compat eta
                    (real_mult (p i)
                       (real_plus (cw_log (p i) (Hp i))
                                  (real_opp (cw_log (r i) (Hr i)))))
                    eta (real_kl_term (p i) (r i) (Hp i) (Hr i))
                    (real_eq_refl eta)
                    (real_eq_trans
                       (real_mult (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i)))))
                       (real_mult (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog)))
                       (real_kl_term (p i) (r i) (Hp i) (Hr i))
                       (RealSetoid.real_eq_mult_compat (p i)
                          (real_plus (cw_log (p i) (Hp i))
                                     (real_opp (cw_log (r i) (Hr i))))
                          (p i)
                          (real_opp (cw_log (real_mult (r i) ipp) Hrplog))
                          (real_eq_refl (p i)) HnegR)
                       (real_eq_refl (real_kl_term (p i) (r i) (Hp i) (Hr i)))))
                 (real_eq_refl (real_mult (p i) LZ)))). }
  (* ---- sum level: Σ kl(p,q) == η·Σ kl(p,r) + LZ (normalization absorption) ---- *)
  assert (Hsum : real_eq
      (real_list_sum nat
         (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
      (real_plus (real_mult eta Rsum) LZ)).
  { apply (real_eq_trans
             (real_list_sum nat
                (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
             (real_list_sum nat
                (fun i : nat => real_plus
                                   (real_mult eta
                                      (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                   (real_mult (p i) LZ))
                (seq 0 n))
             (real_plus (real_mult eta Rsum) LZ)).
    - exact (real_list_sum_ext nat _ _ (seq 0 n) Hpi).
    - apply (real_eq_trans
                (real_list_sum nat
                   (fun i : nat => real_plus
                                      (real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                                      (real_mult (p i) LZ))
                   (seq 0 n))
                (real_plus
                   (real_list_sum nat
                      (fun i : nat => real_mult eta
                                       (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                      (seq 0 n))
                   (real_list_sum nat (fun i : nat => real_mult (p i) LZ) (seq 0 n)))
                (real_plus (real_mult eta Rsum) LZ)).
      + exact (real_list_sum_add nat _ _ (seq 0 n)).
      + exact (real_eq_trans
                  (real_plus
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n)))
                  (real_plus (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n))))
                  (real_plus (real_mult eta Rsum) LZ)
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum nat
                        (fun i : nat => real_mult eta
                                         (real_kl_term (p i) (r i) (Hp i) (Hr i)))
                        (seq 0 n))
                     (real_list_sum nat (fun i : nat => real_mult (p i) LZ)
                        (seq 0 n))
                     (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_list_sum_linear nat eta
                        (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))
                        (seq 0 n))
                     (real_list_sum_linear_r nat LZ p (seq 0 n)))
                  (RealSetoid.real_eq_plus_compat (real_mult eta Rsum)
                     (real_mult LZ (real_list_sum nat p (seq 0 n)))
                     (real_mult eta Rsum) LZ
                     (real_eq_refl (real_mult eta Rsum))
                     (real_eq_trans (real_mult LZ (real_list_sum nat p (seq 0 n)))
                        (real_mult LZ real_one) LZ
                        (RealSetoid.real_eq_mult_compat LZ
                           (real_list_sum nat p (seq 0 n)) LZ real_one
                           (real_eq_refl LZ) Hnormp)
                        (real_mult_one LZ)))). }
  (* ---- log Z ≤ eps: interpolation bound, strict seed and log monotonicity ---- *)
  assert (HLZ : real_le LZ eps).
  { assert (HZle : real_le Z (real_plus real_one eps))
      by exact (real_interp_Z_le_one_eps n p r eta Hp Hr Hnormp Hnormr
                  Heta_pos Heta_le eps Heps).
    assert (Honep : real_lt real_zero (real_plus real_one eps))
      by exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus real_one eps) kl_zero_plus_zero
                  (real_lt_plus_compat real_zero real_one real_zero eps
                     real_lt_zero_one Heps)).
    assert (Hlogle : real_le LZ (cw_log (real_plus real_one eps) Honep))
      by exact (kl_log_le_mono Z (real_plus real_one eps) HZ Honep HZle).
    assert (Hloglt : real_lt (cw_log (real_plus real_one eps) Honep) eps).
    { apply (real_lt_eq_lt (cw_log (real_plus real_one eps) Honep)
               (cw_log (cauchy_real_exp eps) (cauchy_real_exp_pos eps)) eps).
      - exact (real_log_lt_mono (real_plus real_one eps) (cauchy_real_exp eps)
                  Honep (cauchy_real_exp_pos eps) (real_exp_ge_linear eps Heps)).
      - exact (log_inv_exp_neg_thm eps (cauchy_real_exp_pos eps)). }
    exact (real_le_trans LZ (cw_log (real_plus real_one eps) Honep) eps
             Hlogle (inl Hloglt)). }
  (* ---- conclusion ---- *)
  apply (real_le_trans
           (real_list_sum nat
              (fun i : nat => real_kl_term (p i) (q i) (Hp i) (Hqv i)) (seq 0 n))
           (real_plus (real_mult eta Rsum) LZ)
           (real_plus (real_mult eta Rsum) eps)).
  - exact (inr Hsum).
  - exact (real_le_plus_compat (real_mult eta Rsum) (real_mult eta Rsum) LZ eps
             (real_le_refl (real_mult eta Rsum)) HLZ).
Qed.

(* ============================ Section 9. Iterative companion of the step_kl resolution, real layer ============================ *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
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
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== Basic definitions ========== *)

(* discrete state table: the n states [0;1;...;n-1] as a list *)
Definition m3_states (n : nat) : list nat := seq 0 n.

(* list form of KL: a folded sum of pointwise real_kl_term values *)
Definition m3_kl_list (n : nat) (f g : nat -> Real)
    (Hf : forall i : nat, real_lt real_zero (f i))
    (Hg : forall i : nat, real_lt real_zero (g i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (f i) (g i) (Hf i) (Hg i))
    (m3_states n).

(* geometric rate base: κ := 1−η *)
Definition m3_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* t-th power of κ by iterated multiplication on nat; S is shadowed here, so the constructor is spelled Datatypes.S *)
Fixpoint m3_rpow (a : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S t' => real_mult a (m3_rpow a t')
  end.

(* t·x by iterated addition on nat (the t-step arithmetic accumulation of a per-step eps) *)
Fixpoint m3_nmul (k : nat) (x : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S k' => real_plus x (m3_nmul k' x)
  end.

(* 1+1 > 0: the denominator in the halving of eps *)
Lemma m3_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)           (real_plus real_one real_one)           (real_eq_sym (real_plus real_zero real_zero) real_zero              kl_zero_plus_zero)           (real_lt_plus_compat real_zero real_one real_zero real_one              real_lt_zero_one real_lt_zero_one)).
Qed.

(* halving of eps: d := eps·inv(1+1), one budget shared by the two eps slots of the one-step recurrence *)
Definition m3_half (eps : Real) : Real :=
  real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos).

Lemma m3_half_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (m3_half eps).
Proof.
  intros eps Heps.
  unfold m3_half.
  exact (real_mult_positive eps           (real_inv_pos (real_plus real_one real_one) m3_two_pos)           Heps           (real_inv_pos_pos (real_plus real_one real_one) m3_two_pos)).
Qed.

Lemma m3_half_double_eq : forall eps : Real,
  real_eq (real_plus (m3_half eps) (m3_half eps)) eps.
Proof.
  intros eps. unfold m3_half.
  set (dd := real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos)).
  set (two := real_plus real_one real_one).
  apply (real_eq_trans (real_plus dd dd) (real_mult two dd)).
  - exact (real_eq_trans (real_plus dd dd)
             (real_plus (real_mult real_one dd) (real_mult real_one dd))
             (real_mult two dd)
             (RealSetoid.real_eq_plus_compat dd dd
                (real_mult real_one dd) (real_mult real_one dd)
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd))
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd)))
             (kl_sum_prod_r real_one real_one dd)).
  - exact (real_eq_trans (real_mult two dd)
             (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
             eps
             (kl_swap3 two eps (real_inv_pos two m3_two_pos))
             (real_eq_trans
                (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
                (real_mult eps real_one)
                eps
                (RealSetoid.real_eq_mult_compat eps
                   (real_mult two (real_inv_pos two m3_two_pos)) eps real_one
                   (real_eq_refl eps)
                   (real_inv_pos_correct two m3_two_pos))
                (real_mult_one eps))).
Qed.

(* ========== Ring and order helpers ========== *)

(* η + (1−η) == 1 *)
Lemma m3_ring_eta_kappa : forall eta : Real,
  real_eq (real_plus eta (m3_kappa eta)) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. unfold m3_kappa.
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring.
Qed.

(* η < 1 ⟹ 0 < 1−η *)
Lemma m3_kappa_pos : forall eta : Real,
  real_lt eta real_one -> real_lt real_zero (m3_kappa eta).
Proof.
  intros eta Hlt.
  unfold m3_kappa.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < η ⟹ 1−η ≤ 1 *)
Lemma m3_kappa_le_one : forall eta : Real,
  real_lt real_zero eta -> real_le (m3_kappa eta) real_one.
Proof.
  intros eta Hpos. unfold m3_kappa. apply kl_lt_le_bridge.
  set (X := real_plus real_one (real_opp eta)).
  assert (Hstep1 : real_lt (real_plus real_zero X) (real_plus eta X))
    by exact (real_lt_plus_compat_lt_le real_zero eta X X Hpos (real_le_refl X)).
  assert (Hstep2 : real_lt (real_plus real_zero X) real_one)
    by exact (real_lt_eq_lt (real_plus real_zero X) (real_plus eta X) real_one
                Hstep1 (m3_ring_eta_kappa eta)).
  exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus real_zero X) real_one
           (real_eq_trans (real_plus real_one (real_opp eta)) X (real_plus real_zero X)
              (real_eq_refl X)
              (real_eq_sym (real_plus real_zero X) X (kl_plus_zero_l X)))
           Hstep2).
Qed.

(* κ ≤ 1 and 0 ≤ y ⟹ κ·y ≤ y *)
Lemma m3_le_kappa_mul : forall kappa y : Real,
  real_le real_zero y -> real_le kappa real_one ->
  real_le (real_mult kappa y) y.
Proof.
  intros kappa y Hy0 Hk1.
  apply (kl_le_eq_r (real_mult kappa y) (real_mult real_one y) y).
  - exact (real_le_mult_compat_weak kappa real_one y Hy0 Hk1).
  - apply kl_mult_one_l.
Qed.

(* 0 ≤ c and a ≤ b ⟹ c·a ≤ c·b (left multiplication) *)
Lemma m3_le_mult_compat_l : forall c a b : Real,
  real_le real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc Hab.
  apply (kl_le_eq_r (real_mult c a) (real_mult b c) (real_mult c b)).
  - apply (kl_le_eq_l (real_mult a c) (real_mult b c) (real_mult c a)).
    + exact (real_le_mult_compat_weak a b c Hc Hab).
    + apply real_mult_comm.
  - apply real_mult_comm.
Qed.

(* ring: a·(b+c) == a·b + a·c *)
Lemma m3_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring.
Qed.

(* ring: a·(b·c) == (a·b)·c *)
Lemma m3_ring_reassoc2 : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. apply qeq_imp_qeqT. ring.
Qed.

(* 0 < x ⟹ 0 ≤ t·x *)
Lemma m3_nmul_nonneg : forall (k : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (m3_nmul k x).
Proof.
  intros k x Hx. induction k as [| k IH].
  - apply real_le_refl.
  - exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus x (m3_nmul k x)) real_zero
             (real_le_plus_compat real_zero x real_zero (m3_nmul k x)
                (kl_lt_le_bridge real_zero x Hx) IH)
             kl_zero_plus_zero).
Qed.

(* n ≠ 0 ⟹ the state table is nonempty *)
Lemma m3_seq_nonnil : forall n : nat, n <> 0 -> m3_states n <> nil.
Proof.
  intros n Hn Hnil. unfold m3_states in Hnil.
  destruct n as [| m].
  - exact (Hn eq_refl).
  - simpl in Hnil. discriminate Hnil.
Qed.

(* a list sum of pointwise positive terms is positive (positivity core of the partition function) *)
Lemma m3_interp_Z_pos2 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k e : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero
    (real_list_sum nat
       (fun i : nat => real_mult
          (real_pow_pos (q i) k (Hq i)) (real_pow_pos (r i) e (Hr i)))
       (m3_states n)).
Proof.
  intros n Hn q r k e Hq Hr.
  apply (real_list_sum_pos nat).
  - intro i.
    exact (real_mult_positive (real_pow_pos (q i) k (Hq i))
             (real_pow_pos (r i) e (Hr i))
             (cauchy_real_exp_pos (real_mult k (cw_log (q i) (Hq i))))
             (cauchy_real_exp_pos (real_mult e (cw_log (r i) (Hr i))))).
  - exact (m3_seq_nonnil n Hn).
Qed.

(* same statement with the conclusion in the native real_interp_Z shape, so the sigT component of the iteration package matches directly *)
Lemma m3_interp_Z_pos3 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n q r k Hq Hr).
Proof.
  intros n Hn q r k Hq Hr.
  exact (m3_interp_Z_pos2 n Hn q r (real_plus real_one (real_opp k)) k Hq Hr).
Qed.

(* pointwise positivity of the one-step update: π'(i) := (r(i)^{1−k}·p(i)^k)·inv Z > 0 *)
Definition m3_step_pos_pt (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp))
    (i : nat)
  : real_lt real_zero (real_step_next n r p k Hr Hp HZ i) :=
  real_mult_positive
    (real_mult (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
               (real_pow_pos (p i) k (Hp i)))
    (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
    (real_mult_positive
       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
       (real_pow_pos (p i) k (Hp i))
       (cauchy_real_exp_pos
          (real_mult (real_plus real_one (real_opp k)) (cw_log (r i) (Hr i))))
       (cauchy_real_exp_pos (real_mult k (cw_log (p i) (Hp i)))))
    (real_inv_pos_pos (real_interp_Z n r p k Hr Hp) HZ).

(* normalization of the one-step update: Σ π' == inv Z·Z == 1 (partition function absorption) *)
Lemma m3_step_next_norm : forall (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp)),
  real_eq
    (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
    real_one.
Proof.
  intros n r p k Hr Hp HZ.
  exact (real_eq_trans           (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))           (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                      (real_list_sum nat                         (fun i : nat => real_mult                            (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                            (real_pow_pos (p i) k (Hp i)))                         (m3_states n)))           real_one           (real_list_sum_linear_r nat              (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)              (fun i : nat => real_mult                 (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                 (real_pow_pos (p i) k (Hp i)))              (m3_states n))           (real_eq_trans              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_list_sum nat                            (fun i : nat => real_mult                               (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                               (real_pow_pos (p i) k (Hp i)))                            (m3_states n)))              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                         (real_interp_Z n r p k Hr Hp))              real_one              (RealSetoid.real_eq_mult_compat                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_list_sum nat                    (fun i : nat => real_mult                       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))                       (real_pow_pos (p i) k (Hp i)))                    (m3_states n))                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                 (real_interp_Z n r p k Hr Hp)                 (real_eq_refl (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 (real_eq_refl (real_interp_Z n r p k Hr Hp)))              (real_eq_trans                 (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                            (real_interp_Z n r p k Hr Hp))                 (real_mult (real_interp_Z n r p k Hr Hp)                            (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))                 real_one                 (real_mult_comm (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)                                 (real_interp_Z n r p k Hr Hp))                 (real_inv_pos_correct (real_interp_Z n r p k Hr Hp) HZ)))).
Qed.

(* ========== Policy iteration sequence (sigT package: policy, pointwise positivity, partition function positivity, normalization) ========== *)

(* iteration package type: p := π_t together with its pointwise positivity, the positivity of its next partition function and the normalization identity *)
Definition m3_pkg_type (n : nat) (r : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) : Type :=
  { p : nat -> Real &
    { Hp : forall i : nat, real_lt real_zero (p i) &
      { HZ : real_lt real_zero (real_interp_Z n r p (m3_kappa eta) Hr Hp) &
        real_eq (real_list_sum nat p (m3_states n)) real_one } } }.

(* π_{t+1} by real_step_next n r π_t (1−η): the geometric interpolation
   update π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z_t.
   A single Fixpoint on t: the Datatypes.O case carries the initial
   four-component package, and the Datatypes.S case rebuilds all four
   components in step through m3_step_pos_pt, m3_interp_Z_pos3 and
   m3_step_next_norm. *)
Fixpoint m3_pi_pkg (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) {struct t} : m3_pkg_type n r eta Hr :=
  match t with
  | Datatypes.O => existT _ p0 (existT _ Hp0 (existT _ HZ1 Hnorm0))
  | Datatypes.S t' =>
      let pkg := m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t' in
      let p := projT1 pkg in
      let Hp := projT1 (projT2 pkg) in
      let HZ := projT1 (projT2 (projT2 pkg)) in
      (existT _ (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
         (existT _ (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)
           (existT
              (fun HZ' : real_lt real_zero
                          (real_interp_Z n r
                             (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                             (m3_kappa eta) Hr
                             (fun i : nat =>
                                m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)) =>
                 real_eq
                   (real_list_sum nat
                      (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                      (m3_states n))
                   real_one)
              (m3_interp_Z_pos3 n Hn r
                 (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                 (m3_kappa eta) Hr
                 (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i))
              (m3_step_next_norm n r p (m3_kappa eta) Hr Hp HZ)))
       : m3_pkg_type n r eta Hr)
  end.

(* the four projections: iterated policy sequence, pointwise positivity, partition function positivity, normalization *)
Definition m3_pi_seq (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) : nat -> Real :=
  projT1 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t).

Definition m3_pi_seq_pos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  forall i : nat,
    real_lt real_zero (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t i) :=
  fun i : nat => projT1 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) i.

Definition m3_pi_seq_Zpos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_lt real_zero
    (real_interp_Z n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
       (m3_kappa eta) Hr (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) :=
  projT1 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

Definition m3_pi_seq_norm (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_eq
    (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) (m3_states n))
    real_one :=
  projT2 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

(* ========== Preliminary for the one-step recurrences: the reversed one-step geometric contraction ========== *)

(* one-step geometric rate: KL(π★‖π_{t+1}) ≤ (1−η)·KL(π★‖π_t) + eps,
   the direct instance of real_step_kl_eta_bound_eps at step t of the
   iteration with the two policy roles exchanged: the first policy is
   r (the reference policy), the second policy is π_t, and the weight
   is κ := 1−η. *)
Corollary real_iter_step_geom_eps :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       eps).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  exact (real_step_kl_eta_bound_eps n r           (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_kappa eta) Hr           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           Hnormr (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))           (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)           eps Heps).
Qed.

(* ========== One-step backward KL recurrence ========== *)
(* KL(π★‖π_{t+1}) ≤ (1−η)·KL(π★‖π_t) + KL(π_t‖π_{t+1}) + eps.
   Route: the reversed instance gives KL(π★‖π_{t+1}) ≤ (1−η)KL(π★‖π_t) + d
   with d := eps/2, the Gibbs lower bound gives 0 ≤ KL(π_t‖π_{t+1}) + d,
   and adding the two bounds absorbs eps through the halved budget. *)
Theorem real_iter_kl_step :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       (real_plus
          (m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
          eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  assert (HnormP : forall s : nat,
            real_eq
              (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 s)
                 (m3_states n))
              real_one)
    by exact (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0).
  set (A := real_mult (m3_kappa eta)
              (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                 (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).
  set (B := m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))).
  set (d := m3_half eps).
  apply (real_le_trans
           (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
           (real_plus (real_plus A d) (real_plus B d))
           (real_plus A (real_plus B eps))).
  - apply (real_le_trans
             (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
                (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
             (real_plus A d)
             (real_plus (real_plus A d) (real_plus B d))).
    + (* reversed instance: KL(π★‖π_{t+1}) ≤ κ·KL(π★‖π_t) + d *)
      exact (real_step_kl_eta_bound_eps n r
               (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_kappa eta) Hr
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               Hnormr (HnormP t)
               (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
               (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
               d (m3_half_pos eps Heps)).
    + (* (A+d) ≤ (A+d) + (B+d): Gibbs lower bound 0 ≤ B + d *)
      exact (kl_le_eq_l (real_plus (real_plus A d) real_zero)
               (real_plus (real_plus A d) (real_plus B d))
               (real_plus A d)
               (real_le_plus_compat (real_plus A d) (real_plus A d)
                  real_zero (real_plus B d)
                  (real_le_refl (real_plus A d))
                  (real_gibbs_inequality_eps nat (m3_states n)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (HnormP t) (HnormP (Datatypes.S t)) d (m3_half_pos eps Heps)))
               (real_plus_zero (real_plus A d))).
  - (* eq exchange: (A+d)+(B+d) == A+(B+eps) *)
    exact (kl_eq_le_bridge (real_plus (real_plus A d) (real_plus B d))
             (real_plus A (real_plus B eps))
             (real_eq_trans (real_plus (real_plus A d) (real_plus B d))
             (real_plus (real_plus A B) (real_plus d d))
             (real_plus A (real_plus B eps))
             (real_plus_swap_mid A d B d)
             (real_eq_trans (real_plus (real_plus A B) (real_plus d d))
                (real_plus (real_plus A B) eps)
                (real_plus A (real_plus B eps))
                (RealSetoid.real_eq_plus_compat (real_plus A B) (real_plus d d)
                   (real_plus A B) eps
                   (real_eq_refl (real_plus A B))
                   (m3_half_double_eq eps))
                (real_eq_sym (real_plus A (real_plus B eps))
                   (real_plus (real_plus A B) eps)
                   (real_plus_assoc A B eps))))).
Qed.

(* ========== Geometric-rate iteration ========== *)
(* KL(π★‖π_t) ≤ (1−η)^t·KL(π★‖π_0) + t·eps:
   induction on t over the one-step contraction real_iter_step_geom_eps,
   the error accumulating arithmetically over the t steps. *)
Theorem real_iter_kl_geom :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))
    (real_plus
       (real_mult (m3_rpow (m3_kappa eta) t)
          (m3_kl_list n r p0 Hr Hp0))
       (m3_nmul t eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1
         t eps Heps.
  induction t as [| t IH].
  - (* t = 0: κ^0 == 1 and 0·eps == 0, so the goal reads KL ≤ 1·KL + 0 == KL *)
    cbn [m3_rpow m3_nmul].
    apply kl_eq_le_bridge.
    apply (real_eq_sym
             (real_plus
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero)
             (m3_kl_list n r p0 Hr Hp0)).
    exact (real_eq_trans
             (real_plus (real_mult real_one (m3_kl_list n r p0 Hr Hp0))
                        real_zero)
             (real_plus (m3_kl_list n r p0 Hr Hp0) real_zero)
             (m3_kl_list n r p0 Hr Hp0)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero
                (m3_kl_list n r p0 Hr Hp0) real_zero
                (kl_mult_one_l (m3_kl_list n r p0 Hr Hp0))
                (real_eq_refl real_zero))
             (real_plus_zero (m3_kl_list n r p0 Hr Hp0))).
  - (* t = S t: one-step contraction, monotone scaling by the induction premise, regrouping of the κ factors and accumulation of the error *)
    cbn [m3_rpow m3_nmul].
    pose proof (real_iter_step_geom_eps n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                  Hnormr Heta_pos Heta_lt1 t eps Heps) as Hstep.
    set (KL0 := m3_kl_list n r p0 Hr Hp0).
    set (KLt := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)).
    set (KLs := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                  Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                     (Datatypes.S t))).
    set (Y := m3_nmul t eps).
    set (X := real_mult (m3_rpow (m3_kappa eta) t) KL0).
    (* monotonicity in κ: 0 ≤ κ and the induction premise give κ·KL_t ≤ κ·(κ^t·KL0 + t·eps) *)
    assert (Hmono : real_le (real_mult (m3_kappa eta) KLt)
                            (real_mult (m3_kappa eta) (real_plus X Y))).
    { apply (m3_le_mult_compat_l (m3_kappa eta)).
      - exact (kl_lt_le_bridge real_zero (m3_kappa eta)
                 (m3_kappa_pos eta Heta_lt1)).
      - exact IH. }
    (* one-step chain: KL_{t+1} ≤ κ·KL_t + eps ≤ κ·(κ^t·KL0 + Y) + eps *)
    assert (Hchain : real_le KLs
                       (real_plus (real_mult (m3_kappa eta) (real_plus X Y))
                          eps)).
    { apply (real_le_trans KLs (real_plus (real_mult (m3_kappa eta) KLt) eps)).
      - exact Hstep.
      - exact (real_le_plus_compat (real_mult (m3_kappa eta) KLt)
                  (real_mult (m3_kappa eta) (real_plus X Y)) eps eps
                  Hmono (real_le_refl eps)). }
    (* final assembly: κ·(X+Y)+eps ≤ (κ·κ^t)·KL0 + (Y+eps), using κ·Y ≤ Y *)
    apply (real_le_trans KLs
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps))
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus eps Y))).
    + apply (kl_le_eq_r _ (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)).
      * exact Hchain.
      * exact (real_eq_trans
                 (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)
                 (real_plus (real_plus (real_mult (m3_kappa eta) X)
                              (real_mult (m3_kappa eta) Y)) eps)
                 (real_plus
                    (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                       KL0)
                    (real_plus (real_mult (m3_kappa eta) Y) eps))
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (m3_kappa eta) (real_plus X Y))
                    eps
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_mult (m3_kappa eta) Y))
                    eps
                    (m3_distrib_l (m3_kappa eta) X Y)
                    (real_eq_refl eps))
                 (real_eq_trans
                    (real_plus
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y)) eps)
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_plus
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_eq_sym
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_plus (real_mult (m3_kappa eta) Y) eps))
                       (real_plus
                          (real_plus (real_mult (m3_kappa eta) X)
                             (real_mult (m3_kappa eta) Y)) eps)
                       (real_plus_assoc (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y) eps))
                    (RealSetoid.real_eq_plus_compat
                       (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (m3_ring_reassoc2 (m3_kappa eta) (m3_rpow (m3_kappa eta) t) KL0)
                       (real_eq_refl (real_plus (real_mult (m3_kappa eta) Y) eps))))).
    + exact (real_le_plus_compat
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps)
                (real_plus eps Y)
                (real_le_refl
                   (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0))
                (kl_le_eq_r
                   (real_plus (real_mult (m3_kappa eta) Y) eps)
                   (real_plus Y eps)
                   (real_plus eps Y)
                   (real_le_plus_compat (real_mult (m3_kappa eta) Y) Y eps eps
                      (m3_le_kappa_mul (m3_kappa eta) Y
                         (m3_nmul_nonneg t eps Heps)
                         (m3_kappa_le_one eta Heta_pos))
                      (real_le_refl eps))
                   (real_plus_comm Y eps))).
Qed.

(* ---------- assumption audit (self-certified, zero acknowledgments):
   live Print Assumptions lines are the audit port -- every compile prints
   the Closed line for each audited statement face. ---------- *)
Print Assumptions real_exp_two_point_cvx_eps.
Print Assumptions real_amgm_pointwise_eps.
Print Assumptions real_interp_Z_le_one_eps.
Print Assumptions real_step_kl_eta_bound_eps.
Print Assumptions real_iter_step_geom_eps.
Print Assumptions real_iter_kl_step.
Print Assumptions real_iter_kl_geom.
