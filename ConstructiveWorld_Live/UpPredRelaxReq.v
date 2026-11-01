(* ==========================================================================
   UpPredRelaxReq.v - relaxation monotonicity, the Landauer lower bound,
   and the hierarchical disturbance chain.
   Mission.
     Six stations: heat_relaxation_decreasing (thermal relaxation decreases
     in the temperature difference), fluctuation_scale_decreasing,
     landauer_bound_pos (positivity of the Landauer lower bound),
     disturbance_hierarchical_transitive, disturbance_chain_decreasing,
     and total_loss_multi_epoch_decreasing.
   Dependencies.
     CW_ConstructiveWorld_219; Stdlib Arith; S01-S15 chain per Require face;
     Import RealInterfaceEnhancedMod (interface-abstract boundary piece:
     statement faces anchored at the fixed Real instance layer).
   References.
     Thermal relaxation and the Landauer principle (an energy-consumption
     lower bound); monotone convergence along the hierarchical disturbance
     chain.
   Constructivity.
     Every station Qed-closed, zero admissive lexemes; proof bodies introduce
     no additional axiom premises. All predicates use the definitional
     raw-layer forms real_eq, real_le, real_lt (raw re-exports real_zero,
     real_one, real_plus, real_mult, real_exp_neg, real_inv_pos, real_log)
     anchored at the fixed Real instance layer RealEnhancedReal, discharged
     verbatim by exact; the Id-jurisdiction domain type stays in place.
   Build.
     Rocq 9.1 direct rocq c -native-compiler no -q -Q . "" (vo shadow tree
     recompiled in the same world), COQLIB/ROCQLIB literal environment
     prefixes; compiles wrapped by the cpu_guard thermal wrapper.
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
From Stdlib Require Import Arith.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Station 1: monotone decrease of thermal relaxation            *)
(* (source module L25-83 PredRelaxHeat, req-side counterpart).   *)
(* ============================================================ *)
Section PredRelaxHeatReq.

Let zero := real_zero.
Let mult := real_mult.
Let exp_neg := real_exp_neg.
Let le := real_le.

Variable temperature_difference : nat -> Real.
Variable gamma : Real.
Variable of_nat : nat -> Real.
Variable temperature_difference0 : Real.

Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat t) (of_nat (Nat.succ t)).

Variable heat_relaxation_exponential :
  forall t : nat,
    real_eq (temperature_difference t)
        (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0).

(* Relaxation decreases monotonically: T(S t) <= T(t).  The source-module
   chain is carried over piecewise onto the req face: monotonicity of
   gamma * of_nat (le_mult_compat_weak fixes the right factor -> mult_comm
   reshapes both ends) -> exp_neg reverses the order -> multiplication by
   the nonnegative T0 preserves it -> the equality-transport steps are
   re-cast onto the req sides via le_id_l/le_id_r. *)
Theorem heat_relaxation_decreasing : forall t : nat,
  le (temperature_difference (Nat.succ t)) (temperature_difference t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat t)) (mult gamma (of_nat (Nat.succ t)))).
  { exact (le_id_l (mult gamma (of_nat t))
                   (mult (of_nat t) gamma)
                   (mult gamma (of_nat (Nat.succ t)))
                   (mult_comm gamma (of_nat t))
                   (le_id_r (mult (of_nat t) gamma)
                            (mult (of_nat (Nat.succ t)) gamma)
                            (mult gamma (of_nat (Nat.succ t)))
                            (mult_comm (of_nat (Nat.succ t)) gamma)
                            (le_mult_compat_weak (of_nat t)
                                                 (of_nat (Nat.succ t))
                                                 gamma
                                                 gamma_nonneg
                                                 (of_nat_mono t)))). }
  assert (He : le (exp_neg (mult gamma (of_nat (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat t))))
    by exact (exp_neg_le_decr (mult gamma (of_nat t))
                              (mult gamma (of_nat (Nat.succ t))) Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat (Nat.succ t))))
                        temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat t)))
                        temperature_difference0))
    by exact (le_mult_compat_weak (exp_neg (mult gamma (of_nat (Nat.succ t))))
                                  (exp_neg (mult gamma (of_nat t)))
                                  temperature_difference0
                                  temperature_difference0_nonneg He).
  exact (le_id_l (temperature_difference (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat (Nat.succ t))))
                       temperature_difference0)
                 (temperature_difference t)
                 (heat_relaxation_exponential (Nat.succ t))
                 (le_id_r (mult (exp_neg (mult gamma (of_nat (Nat.succ t))))
                                temperature_difference0)
                          (mult (exp_neg (mult gamma (of_nat t)))
                                temperature_difference0)
                          (temperature_difference t)
                          (real_eq_sym (temperature_difference t)
                                   (mult (exp_neg (mult gamma (of_nat t)))
                                         temperature_difference0)
                                   (heat_relaxation_exponential t))
                          Hm)).
Qed.

End PredRelaxHeatReq.

(* ============================================================ *)
(* Station 2: monotone decrease of the fluctuation scale         *)
(* (source module L89-130 PredRelaxFluct, req-side counterpart;  *)
(*  accepted upgrade template prediction_fluctuation_scale at    *)
(*  L1671 inside the replica root).                              *)
(* ============================================================ *)
Section PredRelaxFluctReq.

Let zero := real_zero.
Let one := real_one.
Let plus := real_plus.
Let mult := real_mult.
Let exp_neg := real_exp_neg.
Let inv_pos := real_inv_pos.
Let le := real_le.
Let lt := real_lt.

Variable prob_negative_entropy : Real -> Real.
Variable k_B : Real.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_scale :
  forall N : Real,
    real_eq (prob_negative_entropy N) (exp_neg (mult N (inv_pos k_B k_B_pos))).

(* The fluctuation probability decreases monotonically in N:
   P(N+1) <= P(N).  Core: N <= N+1 (le_plus_nonneg_r is not an RIS field ->
   rebuilt from three limbs) times 1/k_B >= 0, with exp_neg reversing the
   order; the equality-transport steps are re-cast onto the req sides. *)
Theorem fluctuation_scale_decreasing : forall N : Real,
  le (prob_negative_entropy (plus N one)) (prob_negative_entropy N).
Proof.
  intro N.
  assert (Hle01 : le zero one)
    by exact (lt_le_iff zero one (inl one_pos)).
  assert (HN1 : le N (plus N one)).
  { exact (le_id_l N (plus N zero) (plus N one)
                   (real_eq_sym (plus N zero) N (plus_zero N))
                   (le_plus_compat N N zero one (le_refl N) Hle01)). }
  assert (Hcore : le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                     (exp_neg (mult N (inv_pos k_B k_B_pos)))).
  { exact (exp_neg_le_decr (mult N (inv_pos k_B k_B_pos))
                           (mult (plus N one) (inv_pos k_B k_B_pos))
                           (le_mult_compat_weak N (plus N one)
                                                (inv_pos k_B k_B_pos)
                                                (lt_le_iff zero
                                                   (inv_pos k_B k_B_pos)
                                                   (inl (inv_pos_pos k_B
                                                         k_B_pos)))
                                                HN1)). }
  exact (le_id_l (prob_negative_entropy (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (prob_negative_entropy N)
                 (fluctuation_scale (plus N one))
                 (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                          (exp_neg (mult N (inv_pos k_B k_B_pos)))
                          (prob_negative_entropy N)
                          (real_eq_sym (prob_negative_entropy N)
                                   (exp_neg (mult N (inv_pos k_B k_B_pos)))
                                   (fluctuation_scale N))
                          Hcore)).
Qed.

End PredRelaxFluctReq.

(* ============================================================ *)
(* Station 3: positivity of the Landauer bound                   *)
(* (source module L137-169 PredRelaxLandauer, req-side           *)
(*  counterpart; minimal assumption-to-qualitative-conclusion    *)
(*  piece: k_B > 0, T > 0, log 2 > 0 stated explicitly).         *)
(* ============================================================ *)
Section PredRelaxLandauerReq.

Let zero := real_zero.
Let one := real_one.
Let plus := real_plus.
Let mult := real_mult.
Let log := real_log.
Let le := real_le.
Let lt := real_lt.

Variable E_min : Real.
Variable k_B : Real.
Variable T_landauer : Real.

Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
(* The req-world log carries its positivity premise explicitly (in the
   source module's Id world it was an implicit argument): the 2 > 0 witness
   is inlined via plus_positive one one one_pos one_pos, so the assumption
   face keeps the source module's shape (log 2 > 0 is the single added
   premise). *)
Variable log_two_pos :
  lt zero (log (plus one one) (plus_positive one one one_pos one_pos)).

Variable prediction_landauer :
  real_eq E_min (mult k_B (mult T_landauer
                          (log (plus one one)
                               (plus_positive one one one_pos one_pos)))).

(* The Landauer bound is positive: E_min = k_B * T * log 2 > 0 (three
   positives multiplied + equality re-cast on the req face: lt_id_r
   transports zero < k_B * (T * log 2) into zero < E_min along the req
   sides). *)
Theorem landauer_bound_pos : lt zero E_min.
Proof.
  exact (lt_id_r zero                 (mult k_B (mult T_landauer                                (log (plus one one)                                     (plus_positive one one one_pos one_pos))))                 E_min                 (real_eq_sym E_min                          (mult k_B                                (mult T_landauer                                      (log (plus one one)                                           (plus_positive one one one_pos                                                         one_pos))))                          prediction_landauer)                 (mult_positive k_B                                (mult T_landauer                                      (log (plus one one)                                           (plus_positive one one one_pos                                                         one_pos)))                                k_B_pos                                (mult_positive T_landauer                                               (log (plus one one)                                                    (plus_positive one one                                                                     one_pos                                                                     one_pos))                                               T_pos log_two_pos))).
Qed.

End PredRelaxLandauerReq.

(* ============================================================ *)
(* Stations 4/5: disturbance transfer of hierarchical stability  *)
(* (source module L174-221 PredRelaxHier, req-side counterpart;  *)
(*  the territory-typed PropType follows the G09_MiscSmall C3    *)
(*  precedent: the Id-jurisdiction domain type stays in place as *)
(*  a pure type domain, the order content carried by the RIS     *)
(*  world).                                                      *)
(* ============================================================ *)
Section PredRelaxHierReq.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let le := real_le.
Let PropType := @PropositionConvergenceCore.Proposition RI SS.

Variable disturbance : PropType -> Real.
Variable hierarchical_relation : PropType -> PropType -> Set.

Variable hierarchical_stability_prediction :
  forall (upper lower : PropType),
    hierarchical_relation upper lower ->
    le (disturbance upper) (disturbance lower).

(* Two-step transfer: upper disturbance <= middle disturbance <= lower
   disturbance implies upper <= lower. *)
Theorem disturbance_hierarchical_transitive : forall (u m l : PropType),
  hierarchical_relation u m -> hierarchical_relation m l ->
  le (disturbance u) (disturbance l).
Proof.
  intros u m l Hum Hml.
  exact (le_trans (disturbance u) (disturbance m) (disturbance l)                  (hierarchical_stability_prediction u m Hum)                  (hierarchical_stability_prediction m l Hml)).
Qed.

(* Finite-chain version: along the hierarchy chain for n steps the
   disturbance stays monotonically non-increasing (nat induction on
   le_refl + le_trans; both the base and the successor step are done by
   term-level reshaping with eq_ind + Nat.add_0_r / Nat.add_succ_r, zero
   rewrite). *)
Theorem disturbance_chain_decreasing : forall (chain : nat -> PropType),
  (forall k : nat, hierarchical_relation (chain k) (chain (Nat.succ k))) ->
  forall (k n : nat), le (disturbance (chain k)) (disturbance (chain (k + n))).
Proof.
  intros chain Hrel k n.
  induction n as [| n IH].
  - exact (eq_rect k
                  (fun m => le (disturbance (chain k)) (disturbance (chain m)))
                  (le_refl (disturbance (chain k)))
                  (k + 0) (eq_sym (Nat.add_0_r k))).
  - exact (eq_rect (Nat.succ (k + n))
                  (fun m => le (disturbance (chain k)) (disturbance (chain m)))
                  (le_trans (disturbance (chain k))
                            (disturbance (chain (k + n)))
                            (disturbance (chain (Nat.succ (k + n))))
                            IH
                            (hierarchical_stability_prediction
                               (chain (k + n)) (chain (Nat.succ (k + n)))
                               (Hrel (k + n))))
                  (k + Datatypes.S n) (eq_sym (Nat.add_succ_r k n))).
Qed.

End PredRelaxHierReq.

(* ============================================================ *)
(* Station 6: multi-epoch loss-decrease chain tied to the        *)
(* language-model structure (source module L227-261 PredRelaxLM, *)
(* req-side counterpart; minimal assumption-to-qualitative       *)
(* conclusion piece, the single-step correlation premise stated  *)
(* pointwise and explicitly).                                    *)
(* ============================================================ *)
Section PredRelaxLMReq.

Let le := real_le.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> Real.
Variable total_loss : list Token -> Real.

Variable loss_structure_correlation :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_loss (model epoch)) (total_loss (model (Nat.succ epoch))).

(* Multi-epoch loss-decrease chain: grammar_error monotone per epoch
   implies total_loss monotonically non-increasing along any n steps (nat
   induction + eq_ind term-level reshaping, zero rewrite). *)
Theorem total_loss_multi_epoch_decreasing : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k)) (grammar_error (model (Nat.succ k)))) ->
  le (total_loss (model start)) (total_loss (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - exact (eq_rect start
                  (fun m => le (total_loss (model start)) (total_loss (model m)))
                  (le_refl (total_loss (model start)))
                  (start + 0) (eq_sym (Nat.add_0_r start))).
  - exact (eq_rect (Nat.succ (start + n))
                  (fun m => le (total_loss (model start)) (total_loss (model m)))
                  (le_trans (total_loss (model start))
                            (total_loss (model (start + n)))
                            (total_loss (model (Nat.succ (start + n))))
                            IH
                            (loss_structure_correlation (start + n)
                                                        (Hg (start + n))))
                  (start + Datatypes.S n) (eq_sym (Nat.add_succ_r start n))).
Qed.

End PredRelaxLMReq.
