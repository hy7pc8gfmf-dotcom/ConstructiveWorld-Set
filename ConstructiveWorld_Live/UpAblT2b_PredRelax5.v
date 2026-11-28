(* ========================================================================= *)
(* Module   : UpAblT2b_PredRelax5                                            *)
(* Mission.  Five-zone prediction-relaxation instantiation and export piece: *)
(*   heat relaxation, fluctuation scaling, cross-domain scaling, Landauer    *)
(*   bound, loss structure. Each zone carries a discharge form (the assembled*)
(*   carrier equals its unpacked formula, by conversion) and an export form  *)
(*   (downstream monotonicity/positivity re-proved after pruning). Interface *)
(*   half: S01 RealInterfaceEnhanced + fa56/fa56b/fa56c carriers. Req half:  *)
(*   four stations re-anchored to the fixed global Real layer (this tree's   *)
(*   Setoid class is zero-argument at Real, so the baseline parameterized    *)
(*   assembly bridge has no counterpart; carriers mount as their definitional*)
(*   formulas, per abl_tail_sum_pos_bridge / UpPredRelaxReq idiom).          *)
(* Dependencies. S01_BaseRing, S02_CauchyComplete (real_* twins), S03_QExp  *)
(*   (real_inv_pos), S07_RealSetoidExpLog (real_exp_neg/real_log, module     *)
(*   RealInterfaceEnhancedMod), fa56_id_carrier, fa56b_ext, fa56c_ext;       *)
(*   Stdlib Lists.List, Arith.                                               *)
(* References. G04_ProjFam prediction zones; S05 prediction slots (fa56     *)
(*   donor headers); UpPredRelaxReq stations 1/2/3/6.                        *)
(* Constructivity. Statement faces Set-carried throughout: Id/sigT (S01),   *)
(*   the interface orders le/lt and the fixed-Real twins real_eq/real_le/   *)
(*   real_lt are all Set-valued, so every predicate face is a Set-order     *)
(*   carrier of this tree (the Q-layer analogue of QltT/QeqT); zero Prop    *)
(*   statements, zero Prop components in Set-carrier positions. Proof bodies*)
(*   use only constructive steps (Stdlib eq_rect/eq_sym on nat indices).    *)
(*   Every proof closes Defined: statements are Set-carried, so all exits   *)
(*   are transparent extraction units with no opaque bridge. Section        *)
(*   Variables are discharged into statements (premises, not assumptions);  *)
(*   zero axioms/admits; tail Print Assumptions audit covers every theorem. *)
(* Build. rocq c -native-compiler no -q -Q <Set Live root> "" (r237 driver, sandbox-born). *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import fa56_id_carrier.
Require Import fa56b_ext.
Require Import fa56c_ext.
From Stdlib Require Import Lists.List Arith.

(* ============ Zone 1: heat relaxation, interface half (G04 donor) ========= *)

Section UabT2bG04Heat.

Context {RI : RealInterfaceEnhanced}.

Let R       := @R RI.
Let zero    := @zero RI.
Let mult    := @mult RI.
Let exp_neg := @exp_neg RI.
Let le      := @le RI.

Variable gamma : R.
Variable of_nat_R : nat -> R.
Variable temperature_difference0 : R.
Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat_R t) (of_nat_R (Nat.succ t)).

(* Discharge form: the fa56 mounting of temperature_difference unpacks
   definitionally to the relaxation formula. *)
Theorem uabt2b_g04_heat_discharge :
  forall t : nat,
    Id (fa56_temp_difference gamma of_nat_R temperature_difference0 t)
       (mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0).
Proof.
  intro t.
  exact (@id_refl _
           (mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0)).
Defined.

(* Export form: heat_relaxation_decreasing re-proved after pruning the
   exponential-decay premise. *)
Theorem uabt2b_g04_heat_decreasing_wo : forall t : nat,
  le (fa56_temp_difference gamma of_nat_R temperature_difference0 (Nat.succ t))
     (fa56_temp_difference gamma of_nat_R temperature_difference0 t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat_R t))
                  (mult gamma (of_nat_R (Nat.succ t)))).
  { apply (le_id_l (mult gamma (of_nat_R t)) (mult (of_nat_R t) gamma)
                   (mult gamma (of_nat_R (Nat.succ t)))).
    - apply (mult_comm gamma (of_nat_R t)).
    - apply (le_id_r (mult (of_nat_R t) gamma)
                     (mult (of_nat_R (Nat.succ t)) gamma)
                     (mult gamma (of_nat_R (Nat.succ t)))).
      + apply (mult_comm (of_nat_R (Nat.succ t)) gamma).
      + apply (le_mult_compat_weak (of_nat_R t) (of_nat_R (Nat.succ t)) gamma).
        * exact gamma_nonneg.
        * exact (of_nat_mono t). }
  assert (He : le (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat_R t))))
    by exact (exp_neg_le_decr _ _ Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                        temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0))
    by exact (le_mult_compat_weak _ _ temperature_difference0
              temperature_difference0_nonneg He).
  apply (le_id_l (fa56_temp_difference gamma of_nat_R temperature_difference0 (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t)))) temperature_difference0)
                 (fa56_temp_difference gamma of_nat_R temperature_difference0 t)).
  - exact (uabt2b_g04_heat_discharge (Nat.succ t)).
  - apply (le_id_r (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t)))) temperature_difference0)
                   (mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0)
                   (fa56_temp_difference gamma of_nat_R temperature_difference0 t)).
    + exact (id_sym (uabt2b_g04_heat_discharge t)).
    + exact Hm.
Defined.

End UabT2bG04Heat.

(* ============ Zone 2: fluctuation scaling, interface half ================= *)

Section UabT2bG04Fluct.

Context {RI : RealInterfaceEnhanced}.

Let R       := @R RI.
Let zero    := @zero RI.
Let one     := @one RI.
Let plus    := @plus RI.
Let mult    := @mult RI.
Let exp_neg := @exp_neg RI.
Let inv_pos := @inv_pos RI.
Let le      := @le RI.
Let lt      := @lt RI.

Variable k_B : R.
Variable k_B_pos : lt zero k_B.

(* Discharge form: the fa56 mounting of prob_negative_entropy. *)
Theorem uabt2b_g04_fluctuation_discharge :
  forall N : R,
    Id (fa56_prob_neg_entropy k_B k_B_pos N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).
Proof.
  intro N.
  exact (@id_refl _ (exp_neg (mult N (inv_pos k_B k_B_pos)))).
Defined.

(* Export form: fluctuation_scale_decreasing re-proved after pruning. *)
Theorem uabt2b_g04_fluctuation_decreasing_wo : forall N : R,
  le (fa56_prob_neg_entropy k_B k_B_pos (plus N one))
     (fa56_prob_neg_entropy k_B k_B_pos N).
Proof.
  intro N.
  assert (Hcore : le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                     (exp_neg (mult N (inv_pos k_B k_B_pos)))).
  { apply exp_neg_le_decr.
    apply (le_mult_compat_weak N (plus N one) (inv_pos k_B k_B_pos)).
    - apply (lt_le_iff _ _). left. apply inv_pos_pos.
    - apply le_plus_nonneg_r. exact (lt_le_iff _ _ (inl one_pos)). }
  apply (le_id_l (fa56_prob_neg_entropy k_B k_B_pos (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (fa56_prob_neg_entropy k_B k_B_pos N)).
  - exact (uabt2b_g04_fluctuation_discharge (plus N one)).
  - apply (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                   (exp_neg (mult N (inv_pos k_B k_B_pos)))
                   (fa56_prob_neg_entropy k_B k_B_pos N)).
    + exact (id_sym (uabt2b_g04_fluctuation_discharge N)).
    + exact Hcore.
Defined.

End UabT2bG04Fluct.

(* ============ Zone 4: Landauer bound, interface half ====================== *)

Section UabT2bG04Landauer.

Context {RI : RealInterfaceEnhanced}.

Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let log  := @log RI.
Let le   := @le RI.
Let lt   := @lt RI.

Variable k_B : R.
Variable T_landauer : R.
Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
Variable log_two_pos : lt zero (log (plus one one)).

(* Discharge form: the fa56c mounting of E_min. *)
Theorem uabt2b_g04_landauer_discharge :
  Id (fa56c_E_min k_B T_landauer)
     (mult k_B (mult T_landauer (log (plus one one)))).
Proof.
  exact (@id_refl _ (mult k_B (mult T_landauer (log (plus one one))))).
Defined.

(* Export form: landauer_bound_pos re-proved after pruning. *)
Theorem uabt2b_g04_landauer_pos_wo :
  lt zero (fa56c_E_min k_B T_landauer).
Proof.
  assert (Hinner : lt zero (mult T_landauer (log (plus one one))))
    by exact (mult_positive T_landauer (log (plus one one)) T_pos log_two_pos).
  assert (Houter : lt zero (mult k_B (mult T_landauer (log (plus one one)))))
    by exact (mult_positive k_B (mult T_landauer (log (plus one one)))
                              k_B_pos Hinner).
  apply (lt_id_r zero _ (fa56c_E_min k_B T_landauer)
                 (id_sym uabt2b_g04_landauer_discharge) Houter).
Defined.

End UabT2bG04Landauer.

(* ============ Zone 3: cross-domain scaling, existence witness ============= *)

Section UabT2bCrossDomain.

Context {RI : RealInterfaceEnhanced}.

Let R    := @R RI.
Let mult := @mult RI.

Theorem uabt2b_cross_domain_sigT :
  forall (power : R -> R -> R) (of_nat_R : nat -> R) (f_N : nat -> R),
    sigT (fun alpha : R => forall N : nat,
            Id (fa56b_loss_drop power of_nat_R f_N alpha N)
               (mult (power (of_nat_R N) alpha) (f_N N))).
Proof.
  intros power of_nat_R f_N.
  exact (existT _ one (fun N : nat => @id_refl R _)).
Defined.

End UabT2bCrossDomain.

(* ============ Zone 5: loss structure, interface half ====================== *)

Section UabT2bG04LM.

Context {RI : RealInterfaceEnhanced}.

Let R  := @R RI.
Let le := @le RI.
Let lt := @lt RI.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> R.
Variable c : R.
Variable c_pos : lt zero c.

(* Discharge form: the fa56c mounting of total_loss with the explicit
   positive scale c. *)
Theorem uabt2b_g04_lm_discharge :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (fa56c_total_loss Token grammar_error c (model epoch))
       (fa56c_total_loss Token grammar_error c (model (Nat.succ epoch))).
Proof.
  intros epoch H.
  exact (le_id_l (mult c (grammar_error (model epoch)))
                 (mult (grammar_error (model epoch)) c)
                 (mult c (grammar_error (model (Nat.succ epoch))))
           (mult_comm c (grammar_error (model epoch)))
           (le_id_r (mult (grammar_error (model epoch)) c)
                    (mult (grammar_error (model (Nat.succ epoch))) c)
                    (mult c (grammar_error (model (Nat.succ epoch))))
              (mult_comm (grammar_error (model (Nat.succ epoch))) c)
              (le_mult_compat (grammar_error (model epoch))
                 (grammar_error (model (Nat.succ epoch))) c c_pos H))).
Defined.

(* Export form: total_loss_multi_epoch_decreasing re-proved after pruning
   (nat induction, term-level reshaping along Stdlib equality). *)
Theorem uabt2b_g04_lm_loss_decreasing_wo : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k))
                     (grammar_error (model (Nat.succ k)))) ->
  le (fa56c_total_loss Token grammar_error c (model start))
     (fa56c_total_loss Token grammar_error c (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - exact (eq_rect start
                  (fun m => le (fa56c_total_loss Token grammar_error c (model start))
                               (fa56c_total_loss Token grammar_error c (model m)))
                  (le_refl (fa56c_total_loss Token grammar_error c (model start)))
                  (start + 0) (eq_sym (Nat.add_0_r start))).
  - exact (eq_rect (Nat.succ (start + n))
                  (fun m => le (fa56c_total_loss Token grammar_error c (model start))
                               (fa56c_total_loss Token grammar_error c (model m)))
                  (le_trans (fa56c_total_loss Token grammar_error c (model start))
                            (fa56c_total_loss Token grammar_error c (model (start + n)))
                            (fa56c_total_loss Token grammar_error c
                               (model (Nat.succ (start + n))))
                            IH
                            (uabt2b_g04_lm_discharge (start + n) (Hg (start + n))))
                  (start + Nat.succ n) (eq_sym (Nat.add_succ_r start n))).
Defined.

End UabT2bG04LM.

(* ==== Req carrier half, re-anchored to the fixed global Real layer ======== *)
(* This tree's Setoid interface class is zero-argument at the global Real    *)
(* carrier, so the four req stations mount their carriers as the definitional*)
(* formulas they unpack to (the same conversion discharge as the interface   *)
(* half) and re-run the monotonicity chains on the real_* twins.             *)

Import RealInterfaceEnhancedMod.

Section UabT2bReqHeat.

Let zero := real_zero.
Let mult := real_mult.
Let exp_neg := real_exp_neg.
Let le := real_le.

Variable gamma : Real.
Variable of_nat_R : nat -> Real.
Variable temperature_difference0 : Real.
Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat_R t) (of_nat_R (Nat.succ t)).

(* Req mounting: temperature_difference as the definitional formula. *)
Let temp_difference (t : nat) : Real :=
  mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0.

Theorem uabt2b_req_heat_discharge :
  forall t : nat,
    real_eq (temp_difference t)
            (mult (exp_neg (mult gamma (of_nat_R t))) temperature_difference0).
Proof.
  intro t.
  exact (real_eq_refl _).
Defined.

Theorem uabt2b_req_heat_decreasing_wo : forall t : nat,
  le (temp_difference (Nat.succ t)) (temp_difference t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat_R t))
                  (mult gamma (of_nat_R (Nat.succ t)))).
  { exact (le_id_l (mult gamma (of_nat_R t))
                   (mult (of_nat_R t) gamma)
                   (mult gamma (of_nat_R (Nat.succ t)))
                   (mult_comm gamma (of_nat_R t))
                   (le_id_r (mult (of_nat_R t) gamma)
                            (mult (of_nat_R (Nat.succ t)) gamma)
                            (mult gamma (of_nat_R (Nat.succ t)))
                            (mult_comm (of_nat_R (Nat.succ t)) gamma)
                            (le_mult_compat_weak (of_nat_R t)
                                                 (of_nat_R (Nat.succ t))
                                                 gamma
                                                 gamma_nonneg
                                                 (of_nat_mono t)))). }
  assert (He : le (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat_R t))))
    by exact (exp_neg_le_decr _ _ Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                        temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat_R t)))
                        temperature_difference0))
    by exact (le_mult_compat_weak _ _ temperature_difference0
              temperature_difference0_nonneg He).
  exact (le_id_l (temp_difference (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                       temperature_difference0)
                 (temp_difference t)
                 (uabt2b_req_heat_discharge (Nat.succ t))
                 (le_id_r (mult (exp_neg (mult gamma (of_nat_R (Nat.succ t))))
                                temperature_difference0)
                          (mult (exp_neg (mult gamma (of_nat_R t)))
                                temperature_difference0)
                          (temp_difference t)
                          (real_eq_sym _ _ (uabt2b_req_heat_discharge t))
                          Hm)).
Defined.

End UabT2bReqHeat.

Section UabT2bReqFluct.

Let zero := real_zero.
Let one := real_one.
Let plus := real_plus.
Let mult := real_mult.
Let exp_neg := real_exp_neg.
Let inv_pos := real_inv_pos.
Let le := real_le.
Let lt := real_lt.

Variable k_B : Real.
Variable k_B_pos : lt zero k_B.

(* Req mounting: prob_negative_entropy as the definitional formula. *)
Let prob_neg_entropy (N : Real) : Real :=
  exp_neg (mult N (inv_pos k_B k_B_pos)).

Theorem uabt2b_req_fluctuation_discharge :
  forall N : Real,
    real_eq (prob_neg_entropy N)
            (exp_neg (mult N (inv_pos k_B k_B_pos))).
Proof.
  intro N.
  exact (real_eq_refl _).
Defined.

Theorem uabt2b_req_fluctuation_decreasing_wo : forall N : Real,
  le (prob_neg_entropy (plus N one)) (prob_neg_entropy N).
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
  exact (le_id_l (prob_neg_entropy (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (prob_neg_entropy N)
                 (uabt2b_req_fluctuation_discharge (plus N one))
                 (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                          (exp_neg (mult N (inv_pos k_B k_B_pos)))
                          (prob_neg_entropy N)
                          (real_eq_sym _ _
                             (uabt2b_req_fluctuation_discharge N))
                          Hcore)).
Defined.

End UabT2bReqFluct.

Section UabT2bReqLandauer.

Let zero := real_zero.
Let one := real_one.
Let plus := real_plus.
Let mult := real_mult.
Let log := real_log.
Let le := real_le.
Let lt := real_lt.

Variable k_B : Real.
Variable T_landauer : Real.
Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
(* The req-world log carries its positivity premise explicitly; the 2 > 0
   witness is inlined via plus_positive one one one_pos one_pos. *)
Variable log_two_pos :
  lt zero (log (plus one one) (plus_positive one one one_pos one_pos)).

(* Req mounting: E_min as the definitional formula. *)
Let e_min : Real :=
  mult k_B (mult T_landauer
              (log (plus one one) (plus_positive one one one_pos one_pos))).

Theorem uabt2b_req_landauer_discharge :
  real_eq e_min
          (mult k_B (mult T_landauer
             (log (plus one one) (plus_positive one one one_pos one_pos)))).
Proof.
  exact (real_eq_refl _).
Defined.

Theorem uabt2b_req_landauer_pos_wo : lt zero e_min.
Proof.
  exact (mult_positive k_B
          (mult T_landauer
             (log (plus one one) (plus_positive one one one_pos one_pos)))
          k_B_pos
          (mult_positive T_landauer
             (log (plus one one) (plus_positive one one one_pos one_pos))
             T_pos log_two_pos)).
Defined.

End UabT2bReqLandauer.

Section UabT2bReqLM.

Let le := real_le.
Let lt := real_lt.
Let zero := real_zero.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> Real.
Variable c : Real.
Variable c_pos : lt zero c.

(* Req mounting: total_loss as the definitional formula with the explicit
   positive scale c. *)
Let total_lossf (l : list Token) : Real := mult c (grammar_error l).

Theorem uabt2b_req_lm_discharge :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_lossf (model epoch)) (total_lossf (model (Nat.succ epoch))).
Proof.
  intros epoch H.
  exact (le_id_l (mult c (grammar_error (model epoch)))
                 (mult (grammar_error (model epoch)) c)
                 (mult c (grammar_error (model (Nat.succ epoch))))
           (mult_comm c (grammar_error (model epoch)))
           (le_id_r (mult (grammar_error (model epoch)) c)
                    (mult (grammar_error (model (Nat.succ epoch))) c)
                    (mult c (grammar_error (model (Nat.succ epoch))))
              (mult_comm (grammar_error (model (Nat.succ epoch))) c)
              (le_mult_compat (grammar_error (model epoch))
                 (grammar_error (model (Nat.succ epoch))) c c_pos H))).
Defined.

Theorem uabt2b_req_lm_loss_decreasing_wo : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k))
                     (grammar_error (model (Nat.succ k)))) ->
  le (total_lossf (model start)) (total_lossf (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - exact (eq_rect start
                  (fun m => le (total_lossf (model start))
                               (total_lossf (model m)))
                  (le_refl (total_lossf (model start)))
                  (start + 0) (eq_sym (Nat.add_0_r start))).
  - exact (eq_rect (Nat.succ (start + n))
                  (fun m => le (total_lossf (model start))
                               (total_lossf (model m)))
                  (le_trans (total_lossf (model start))
                            (total_lossf (model (start + n)))
                            (total_lossf (model (Nat.succ (start + n))))
                            IH
                            (uabt2b_req_lm_discharge (start + n)
                               (Hg (start + n))))
                  (start + Nat.succ n) (eq_sym (Nat.add_succ_r start n))).
Defined.

End UabT2bReqLM.

(* ============ Tail: assumption audit, one line per theorem ================ *)

Print Assumptions uabt2b_g04_heat_discharge.
Print Assumptions uabt2b_g04_heat_decreasing_wo.
Print Assumptions uabt2b_g04_fluctuation_discharge.
Print Assumptions uabt2b_g04_fluctuation_decreasing_wo.
Print Assumptions uabt2b_g04_landauer_discharge.
Print Assumptions uabt2b_g04_landauer_pos_wo.
Print Assumptions uabt2b_cross_domain_sigT.
Print Assumptions uabt2b_g04_lm_discharge.
Print Assumptions uabt2b_g04_lm_loss_decreasing_wo.
Print Assumptions uabt2b_req_heat_discharge.
Print Assumptions uabt2b_req_heat_decreasing_wo.
Print Assumptions uabt2b_req_fluctuation_discharge.
Print Assumptions uabt2b_req_fluctuation_decreasing_wo.
Print Assumptions uabt2b_req_landauer_discharge.
Print Assumptions uabt2b_req_landauer_pos_wo.
Print Assumptions uabt2b_req_lm_discharge.
Print Assumptions uabt2b_req_lm_loss_decreasing_wo.
