(* ConstructiveWorld-Set — one-step geometric KL inequality and interpolation partition on the enhanced real interface. *)

(** * UpReqGeomD: geometric step inequality for policy-iteration KL bounds.

    Mission.  The interface-level Bishop order [geod_le_b], the summation
      collapse machine [geod_sum_collapse], the interpolation partition
      bound [geod_interp_Z_le_one_eps], and the interface-form one-step KL
      contraction statements [geod_step_kl_eta_bound_eps] and
      [geod_policy_iter_kl_geom_step_eps].

    Dependencies.  Stdlib [QArith], [Arith], [Lia], [Setoid].  Requires the
      backbone [S01_BaseRing] .. [S15_TailFEPUp]; statements are fixed to
      the global instance [RealEnhancedReal].

    References.  The same-named baseline module in ConstructiveWorld-Main;
      statement names are carried over verbatim (statement-face Set-carrier
      completion).

    Constructivity.  All statements are carried by [Set]; relations are the
      global [real_lt]/[real_le]/[real_eq].  Honest boundary: an Or-form
      ([real_le]) conclusion is not derivable from the eps-language engines
      (constructive orders allow no elimination), so the exact Or-form
      statement is not claimed.  Statements extract with [Obj.magic] = 0;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqGeomD.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

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
(* The interface class in this tree is unparameterized; its carrier is the global Real. *)
Notation R := Real.

(* ============================================================ *)
(* Part A: the interface-level eps-order language, usable at any enhanced *)
(* interface instance. *)
(* ============================================================ *)
Section GeodLeB.


(* The eps-order: x <=_ge y := forall positive eps, x <= y + eps (Set-level *)
(* forall; same family as [real_le_b] of UpRealLeB, with the weak branch so *)
(* that sum_le collapses directly). *)
Definition geod_le_b (x y : R) : Set :=
  forall eps : R, real_lt zero eps -> real_le x (plus y eps).

(* Positive shift: 0 < eps gives y <= y + eps (le_plus_compat + lt_le_iff). *)
Lemma geod_shift_le : forall (y eps : R),
  real_lt zero eps -> real_le y (plus y eps).
Proof.
  intros y eps Heps.
  apply (le_id_l y (plus y zero) (plus y eps)).
  - apply (req_sym (plus y zero) y). apply (plus_zero y).
  - apply (le_plus_compat y y zero eps).
    + apply (le_refl y).
    + exact (lt_le_iff zero eps (inl Heps)).
Qed.

(* One-way bridge: interface [real_le] implies the eps-order (one le_trans step). *)
Lemma geod_le_to_le_b : forall x y : R,
  real_le x y -> geod_le_b x y.
Proof.
  intros x y Hle eps Heps.
  exact (le_trans x y (plus y eps) Hle (geod_shift_le y eps Heps)).
Qed.

End GeodLeB.

(* ============================================================ *)

(* Pointwise eps-weighting (weight u with sumf u == 1) makes the total error *)
(* exactly eps: no division, no bisection — only sum_le, sum_add, sum_linear *)
(* and normalization absorption. *)
(* ============================================================ *)
Section GeodSum.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_le : forall f g : S -> R,
  (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g).
Hypothesis sum_add : forall f g : S -> R,
  real_eq (sumf (fun s => plus (f s) (g s)))
       (plus (sumf f) (sumf g)).
Hypothesis sum_linear : forall (a : R) (f : S -> R),
  real_eq (sumf (fun s => mult a (f s))) (mult a (sumf f)).

Lemma geod_sum_collapse : forall (u f g : S -> R),
  real_eq (sumf u) one ->
  (forall (eps : R), real_lt zero eps -> forall s : S,
     real_le (f s) (plus (g s) (mult eps (u s)))) ->
  geod_le_b (sumf f) (sumf g).
Proof.
  intros u f g Hnorm Hpt eps Heps.
  apply (le_id_r (sumf f)
                 (sumf (fun s => plus (g s) (mult eps (u s))))
                 (plus (sumf g) eps)).
  - (* Sum-side rewriting: sum(g + eps*u) == sum g + eps*sum u == sum g + eps. *)
    apply (req_trans
             (sumf (fun s => plus (g s) (mult eps (u s))))
             (plus (sumf g) (sumf (fun s => mult eps (u s))))
             (plus (sumf g) eps)).
    + exact (sum_add g (fun s => mult eps (u s))).
    + apply (req_plus_compat (sumf g) (sumf g)
                               (sumf (fun s => mult eps (u s))) eps
                               (req_refl (sumf g))).
      apply (req_trans (sumf (fun s => mult eps (u s)))
                         (mult eps (sumf u))
                         eps).
      * exact (sum_linear eps u).
      * apply (req_trans (mult eps (sumf u))
                             (mult eps one)
                             eps).
        -- apply (req_mult_compat eps eps (sumf u) one
                    (req_refl eps) Hnorm).
        -- exact (mult_one eps).
  - (* Lifting the pointwise eps-weighting through the sum. *)
    apply (sum_le f (fun s => plus (g s) (mult eps (u s)))).
    exact (Hpt eps Heps).
Qed.

End GeodSum.

(* ============================================================ *)
(* Part C: the Real instance — power carrier and baseline pointwise convexity. *)

(* All interface fields are RealEnhancedReal instance projections, transparently delta-equal to the global real_* operations. *)
(* ============================================================ *)
Definition geod_pow_pos (a alpha : Real) (Ha : real_lt real_zero a) : Real :=
  real_exp_neg (real_opp (real_mult alpha (real_log a Ha))).

(* Ring helper: double negation elimination (pointwise rational computation). *)
Lemma geod_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Carrier rewriting: the interface-form power equals the real_pow_pos of the *)
(* log layer (delta transparency plus double-negation elimination). *)
Lemma geod_pow_pos_correct : forall (a alpha : Real) (Ha : real_lt real_zero a),
  real_eq (geod_pow_pos a alpha Ha) (real_pow_pos a alpha Ha).
Proof.
  intros a alpha Ha.
  apply (real_eq_trans (geod_pow_pos a alpha Ha)
                       (cauchy_real_exp (real_opp (real_opp (real_mult alpha (cw_log a Ha)))))
                       (real_pow_pos a alpha Ha)).
  - exact (real_eq_refl _).
  - apply (cauchy_real_exp_wd _ _). apply geod_opp_opp.
Qed.

(* Baseline: weighted AM-GM, a^{1-e}*b^e <= (1-e)*a + e*b + eps, by *)
(* compatibility rewriting plus direct composition with the backbone engine *)
(* real_amgm_pointwise_eps. *)
Theorem geod_amgm_pointwise_eps : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                     (geod_pow_pos b eta Hb))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                                (real_mult eta b)) eps).
Proof.
  intros a b eta Ha Hb Heta Hetale eps Heps.
  exact (RealSetoid.real_le_compat           (real_mult (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)                      (real_pow_pos b eta Hb))           (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)                      (geod_pow_pos b eta Hb))           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)                                 (real_mult eta b)) eps)           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)                                 (real_mult eta b)) eps)           (RealSetoid.real_eq_mult_compat              (real_pow_pos a (real_plus real_one (real_opp eta)) Ha)              (real_pow_pos b eta Hb)              (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)              (geod_pow_pos b eta Hb)              (real_eq_sym _ _ (geod_pow_pos_correct a (real_plus real_one (real_opp eta)) Ha))              (real_eq_sym _ _ (geod_pow_pos_correct b eta Hb)))           (real_eq_refl _)           (real_amgm_pointwise_eps a b eta Ha Hb Heta Hetale eps Heps)).
Qed.

(* Interface-syntax variant: conclusion and premises spelled through interface *)
(* projections (same body as the baseline lemma). *)
Theorem geod_amgm_pointwise_iface : forall (a b eta : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_lt real_zero eta ->
  real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_mult (geod_pow_pos a (real_plus real_one (real_opp eta)) Ha)
                (geod_pow_pos b eta Hb))
     (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta)) a)
                           (real_mult eta b)) eps).
Proof.
  exact (fun a b eta Ha Hb => geod_amgm_pointwise_eps a b eta Ha Hb).
Qed.

(* ============================================================ *)
(* Part D: the list summation machine and the interpolation bound Z <= 1 + eps. *)
(* ============================================================ *)
Definition geod_lsum (n : nat) (f : nat -> Real) : Real :=
  real_list_sum nat f (List.seq 0 n).

(* The three summation lemmas, applied with X := nat. *)
Lemma geod_lsum_le : forall (n : nat) (f g : nat -> Real),
  (forall i : nat, real_le (f i) (g i)) ->
  real_le (geod_lsum n f) (geod_lsum n g).
Proof.
  intros n f g H.
  unfold geod_lsum.
  exact (real_list_sum_le nat f g (List.seq 0 n) H).
Qed.

Lemma geod_lsum_add : forall (n : nat) (f g : nat -> Real),
  real_eq (geod_lsum n (fun i => real_plus (f i) (g i)))
          (real_plus (geod_lsum n f) (geod_lsum n g)).
Proof.
  intros n f g.
  unfold geod_lsum.
  exact (real_list_sum_add nat f g (List.seq 0 n)).
Qed.

Lemma geod_lsum_linear : forall (n : nat) (a : Real) (f : nat -> Real),
  real_eq (geod_lsum n (fun i => real_mult a (f i)))
          (real_mult a (geod_lsum n f)).
Proof.
  intros n a f.
  unfold geod_lsum.
  exact (real_list_sum_linear nat a f (List.seq 0 n)).
Qed.

(* Ring helper: eta + (1-eta) == 1. *)
Lemma geod_eta_plus_kappa : forall eta : Real,
  real_eq (real_plus eta (real_plus real_one (real_opp eta))) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Ring helper: 0 + x == x. *)
Lemma geod_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Normalization of the interpolated weights: sum (m*pi_t + eta*pi_s) == *)
(* (1-eta)*sum pi_t + eta*pi_s == 1 (list lemmas, direct composition). *)
Lemma geod_lsum_pair_norm : forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hnormp : real_eq (geod_lsum n pit) real_one)
    (Hnormr : real_eq (geod_lsum n pist) real_one),
  real_eq (geod_lsum n (fun i => real_plus
                          (real_mult (real_plus real_one (real_opp eta)) (pit i))
                          (real_mult eta (pist i))))
          real_one.
Proof.
  intros n pit pist eta Hnormp Hnormr.
  apply (real_eq_trans _
           (real_plus (real_mult (real_plus real_one (real_opp eta)) (geod_lsum n pit))
                      (real_mult eta (geod_lsum n pist)))).
  - (* sum(f+g) == sum f + sum g by linearity. *)
    apply (real_eq_trans _
             (real_plus (geod_lsum n (fun i => real_mult (real_plus real_one (real_opp eta)) (pit i)))
                        (geod_lsum n (fun i => real_mult eta (pist i))))).
    + exact (geod_lsum_add n _ _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (geod_lsum_linear n (real_plus real_one (real_opp eta)) pit)
               (geod_lsum_linear n eta pist)).
  - (* Normalization absorption plus (1-eta)+eta == 1. *)
    apply (real_eq_trans _
             (real_plus (real_mult (real_plus real_one (real_opp eta)) real_one)
                        (real_mult eta real_one))).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) Hnormp)
               (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) Hnormr)).
    + apply (real_eq_trans _
               (real_plus (real_plus real_one (real_opp eta)) eta)).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_mult_one _) (real_mult_one _)).
      * (* (1-eta)+eta == 1 by commutativity. *)
        apply (real_eq_trans _
                 (real_plus eta (real_plus real_one (real_opp eta)))).
        -- apply real_plus_comm.
        -- exact (geod_eta_plus_kappa eta).
Qed.

(* The list-surface sum collapse (same shape as the abstract machine, with *)
(* sumf instantiated to the list sum). *)
Lemma geod_lsum_collapse_real : forall (n : nat) (u f g : nat -> Real),
  real_eq (geod_lsum n u) real_one ->
  (forall (eps : Real), real_lt real_zero eps -> forall i : nat,
     real_le (f i) (real_plus (g i) (real_mult eps (u i)))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n f) (real_plus (geod_lsum n g) eps).
Proof.
  intros n u f g Hnorm Hpt eps Heps.
  apply (RealSetoid.real_le_id_r (geod_lsum n f)
         (geod_lsum n (fun i => real_plus (g i) (real_mult eps (u i))))
         (real_plus (geod_lsum n g) eps)).
  - apply (real_eq_trans
             (geod_lsum n (fun i => real_plus (g i) (real_mult eps (u i))))
             (real_plus (geod_lsum n g) (geod_lsum n (fun i => real_mult eps (u i))))
             (real_plus (geod_lsum n g) eps)).
    + exact (geod_lsum_add n g (fun i => real_mult eps (u i))).
    + apply (RealSetoid.real_eq_plus_compat (geod_lsum n g)
               (geod_lsum n (fun i => real_mult eps (u i)))
               (geod_lsum n g) eps).
      * apply real_eq_refl.
      * apply (real_eq_trans (geod_lsum n (fun i => real_mult eps (u i)))
                             (real_mult eps (geod_lsum n u)) eps).
        -- exact (geod_lsum_linear n eps u).
        -- exact (real_eq_trans (real_mult eps (geod_lsum n u))
                   (real_mult eps real_one) eps
                   (RealSetoid.real_eq_mult_compat eps (geod_lsum n u) eps real_one
                      (real_eq_refl _) Hnorm)
                   (real_mult_one eps)).
  - apply (geod_lsum_le n f (fun i => real_plus (g i) (real_mult eps (u i)))).
    exact (Hpt eps Heps).
Qed.

(* Main lemma: the interpolation partition Z := sum pi_t^{1-eta} * pi_s^eta *)
(* satisfies Z <= 1 + eps — pointwise AM-GM (the baseline lemma) with weight *)
(* eps*pi_t(i), absorbed by the sum collapse (both normalization premises). *)
Theorem geod_interp_Z_le_one_eps : forall (n : nat) (pit pist : nat -> Real) (eta : Real)
    (Hpit : forall i : nat, real_lt real_zero (pit i))
    (Hpist : forall i : nat, real_lt real_zero (pist i))
    (Hnormp : real_eq (geod_lsum n pit) real_one)
    (Hnormr : real_eq (geod_lsum n pist) real_one),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i))))
          (real_plus real_one eps).
Proof.
  intros n pit pist eta Hpit Hpist Hnormp Hnormr Heta Hetale eps Heps.
  pose proof (geod_lsum_collapse_real n pit
                (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i)))
                (fun i => real_plus (real_mult (real_plus real_one (real_opp eta)) (pit i))
                                    (real_mult eta (pist i)))
                Hnormp
                (fun e He i => geod_amgm_pointwise_eps (pit i) (pist i) eta (Hpit i) (Hpist i)
                                 Heta Hetale (real_mult e (pit i))
                                 (real_mult_positive e (pit i) He (Hpit i)))
                eps Heps) as Hm.
  apply (RealSetoid.real_le_id_r
           (geod_lsum n (fun i => real_mult
                            (geod_pow_pos (pit i) (real_plus real_one (real_opp eta)) (Hpit i))
                            (geod_pow_pos (pist i) eta (Hpist i))))
           (real_plus (geod_lsum n (fun i => real_plus
                            (real_mult (real_plus real_one (real_opp eta)) (pit i))
                            (real_mult eta (pist i)))) eps)
           (real_plus real_one eps)).
  - apply (RealSetoid.real_eq_plus_compat
              (geod_lsum n (fun i => real_plus
                              (real_mult (real_plus real_one (real_opp eta)) (pit i))
                              (real_mult eta (pist i))))
              eps real_one eps
              (geod_lsum_pair_norm n pit pist eta Hnormp Hnormr) (real_eq_refl _)).
  - exact Hm.
Qed.

(* ============================================================ *)
(* Part E: the resolved interface-form statements of the step KL bound. *)
(* ============================================================ *)
(* eta scaling helper: 0 < eta gives 1-eta > 0 (ring identity plus order translation). *)
Lemma geod_kappa_pos : forall eta : Real,
  real_lt eta real_one ->
  real_lt real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hlt.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))           (real_plus real_one (real_opp eta))           (real_eq_sym (real_plus eta (real_opp eta)) real_zero              (real_plus_opp eta))           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < eta gives 1-eta <= 1 (the real_lt branch injected into the Or-encoded order). *)
Lemma geod_kappa_le_one : forall eta : Real,
  real_lt real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
  assert (Hlt : real_lt (real_plus real_one (real_opp eta)) real_one).
  { apply (real_lt_eq_lt (real_plus real_one (real_opp eta))
             (real_plus eta (real_plus real_one (real_opp eta))) real_one).
    - exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
               (real_plus real_zero (real_plus real_one (real_opp eta)))
               (real_plus eta (real_plus real_one (real_opp eta)))
               (real_eq_sym _ _ (geod_plus_zero_l (real_plus real_one (real_opp eta))))
               (real_lt_plus_compat_lt_le real_zero eta
                  (real_plus real_one (real_opp eta))
                  (real_plus real_one (real_opp eta))
                  Hpos (real_le_refl (real_plus real_one (real_opp eta))))).
    - exact (geod_eta_plus_kappa eta). }
  exact (inl Hlt).
Qed.

(* Resolved assumption slot: the interface-form eps version of the one-step *)
(* KL contraction, KL(pi_t||next) <= eta*KL(pi_t||pi_s) + eps with next the *)
(* geometric interpolation policy; certificate: the backbone engine *)
(* real_step_kl_eta_bound_eps, applied once. *)
Theorem geod_step_kl_eta_bound_eps :
  forall (n : nat) (p r : nat -> Real) (eta : Real)
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (HZ : real_lt real_zero (real_interp_Z n p r eta Hp Hr))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n p r eta Hp Hr HZ i)),
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n
             (fun i : nat => real_kl_term (p i)
                             (real_step_next n p r eta Hp Hr HZ i) (Hp i) (Hqv i)))
          (real_plus (real_mult eta
                        (geod_lsum n
                           (fun i : nat => real_kl_term (p i) (r i) (Hp i) (Hr i))))
                     eps).
Proof.
  intros n p r eta Hp Hr Hnormp Hnormr HZ Hqv Heta Hetale eps Heps.
  unfold geod_lsum.
  exact (real_step_kl_eta_bound_eps n p r eta Hp Hr Hnormp Hnormr HZ Hqv           Heta Hetale eps Heps).
Qed.

(* Main conclusion: the true one-step geometric contraction (the interface-form *)
(* eps counterpart of the policy-iteration step), with the policy and *)
(* step-size slots instantiated (p := pi_s, r := pi_t, eta := 1-eta); the *)
(* premise slot is *)
(* fed by the engine once, leaving no hypotheses: *)
(* KL(pi_s||next) <= (1-eta)*KL(pi_s||pi_t) + eps. *)
Theorem geod_policy_iter_kl_geom_step_eps :
  forall (n : nat) (r p : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (HZ : real_lt real_zero (real_interp_Z n r p (real_plus real_one (real_opp eta)) Hr Hp))
    (Hqv : forall i : nat,
             real_lt real_zero (real_step_next n r p (real_plus real_one (real_opp eta)) Hr Hp HZ i)),
  real_lt real_zero eta -> real_lt eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (geod_lsum n
             (fun i : nat => real_kl_term (r i)
                             (real_step_next n r p (real_plus real_one (real_opp eta)) Hr Hp HZ i)
                             (Hr i) (Hqv i)))
          (real_plus (real_mult (real_plus real_one (real_opp eta))
                        (geod_lsum n
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))))
                     eps).
Proof.
  intros n r p eta Hr Hp Hnormr Hnormp HZ Hqv Heta Hlt1 eps Heps.
  unfold geod_lsum.
  exact (real_step_kl_eta_bound_eps n r p (real_plus real_one (real_opp eta))           Hr Hp Hnormr Hnormp HZ Hqv           (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta) eps Heps).
Qed.
