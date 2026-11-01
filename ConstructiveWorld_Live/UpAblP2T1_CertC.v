(* ===================================================================== *)
(*  UpAblP2T1_CertC.v - statement-family compendium and instantiation      *)
(*  carrier for the conclusions 9(e)/(f) supply family, parts b and c.     *)
(*                                                                         *)
(*  Mission. Part b restates four named supply theorems by direct          *)
(*  citation of UpRealLeB2 (abs-le-quad, quad-t-le-h, abs-h-square,        *)
(*  db-breaking-bound) and adds the Q-layer extraction witness             *)
(*  p2t1b_g3_pick; part c independently rebuilds three of the four bounds  *)
(*  from the pointwise eps-form lemmas through the Bishop completion       *)
(*  real_le_closure_b_one, restates the db-breaking bound as a type-level  *)
(*  registration checked against the part-b theorem, cross-checks the      *)
(*  four part-b faces by type assembly, and adds the second Q-layer        *)
(*  witness p2t1c_g3_pick.                                                 *)
(*                                                                         *)
(*  Dependencies. S01_BaseRing through S15_TailFEPUp (the fifteen tree     *)
(*  modules; S08 carries real_abs_le_quad_eps and real_quad_t_le_h_eps,    *)
(*  S09 carries real_abs_h_sq_le_eps), UpRealLeB (real_le_closure_b_one),  *)
(*  UpRealLeB2 (the four _B bounds); Stdlib List, QArith.QArith,           *)
(*  Extraction.                                                            *)
(*  References. UpRealLeB2.v:405/426/449/490 (the four _B lemmas);         *)
(*  UpRealLeB.v:435 real_le_closure_b_one; S08_RealMainlineDPO.v:4931/4998 *)
(*  (eps-form abs-le-quad / quad-t-le-h); S09_EntropyReal.v:1110           *)
(*  (eps-form abs-h-square).                                               *)
(*  Constructivity. All seven theorems close under Qed; the tail audit     *)
(*  runs Print Assumptions on twelve faces, each closed under the global   *)
(*  context; statements ride the Set-layer Or/Not/Id of S01 and the        *)
(*  Bishop bound real_le_b; both extraction witnesses are Q-layer pure.    *)
(*  Build. rocq c -native-compiler no -q -Q . "" (guard-wrapped).          *)
(* ===================================================================== *)

From Stdlib Require Import List.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
From Stdlib Require Import Extraction.

(* ================= Section 1: the p2t1b family ================= *)
From Stdlib Require Import QArith.QArith.

(* ######## The four named supply theorems of conclusions 9(e)/(f) ######## *)

(* p2t1b_T2_abs_le_quad_supply: premises X <= eps1, -X <= 2t^2+eps2,        *)
(* 0 < eps1, 0 < eps2; conclusion |X| <=_B 2t^2+(eps1+eps2). The proof      *)
(* cites real_abs_le_quad_B of UpRealLeB2.                                  *)
Theorem p2t1b_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB HA Htwo.
  exact (real_abs_le_quad_B X t eps1 eps2 HXA HXB HA Htwo).
Qed.

(* p2t1b_T2_quad_t_le_h_supply: premises 0 < x, |h| < eps*x^2/4, 0 < eps;   *)
(* conclusion 2*(h/x)^2 <=_B eps*|h|/2; the proof cites real_quad_t_le_h_B  *)
(* of UpRealLeB2.                                                           *)
Theorem p2t1b_T2_quad_t_le_h_supply : forall (x h eps : Real)
    (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  exact (real_quad_t_le_h_B x h eps Hx Hh Heps).
Qed.

(* p2t1b_T2_abs_h_sq_supply: premises 0 < A, |h| < eps3; conclusion         *)
(* A*|h|^2 <=_B (A*eps3)*|h|; the proof cites real_abs_h_sq_le_B of         *)
(* UpRealLeB2.                                                              *)
Theorem p2t1b_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  exact (real_abs_h_sq_le_B A h eps3 HA Hh3).
Qed.

(* p2t1b_T2_db_breaking_bound_supply: composite-coefficient form of the db  *)
(* breaking bound - the 16 section arguments are threaded explicitly        *)
(* (nonnegativity and symmetry of the transition kernel, the energy         *)
(* Lipschitz bound and the energy lower bound, positivity of the evicted    *)
(* partition, and the rest), with eps and eps' absorbed into explicit       *)
(* premises; the composite coefficient C := invZ*T*(exp+1) carries only     *)
(* nonnegativity; the proof cites real_db_breaking_bound_B of UpRealLeB2.   *)
Theorem p2t1b_T2_db_breaking_bound_supply :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s'))))))).
Proof.
  intros S0 keep keep_dec real_transition real_transition_nonneg
         real_transition_sym real_energy D D_pos L E_max real_metric
         real_energy_lipschitz real_energy_lower real_sum_over_S
         real_evicted_partition_pos s s' Hs Hs'.
  exact (real_db_breaking_bound_B S0 keep keep_dec real_transition
           real_transition_nonneg real_transition_sym real_energy D D_pos
           L E_max real_metric real_energy_lipschitz real_energy_lower
           real_sum_over_S real_evicted_partition_pos s s' Hs Hs').
Qed.

(* ############ Extraction check: the witness face is a Q-layer pure function ############ *)
(* The four supply theorems are real-layer interface statements and stay    *)
(* out of the extraction set; the extraction witness face is the separate   *)
(* Q-layer pure function p2t1b_g3_pick.                                     *)
Definition p2t1b_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1b_g3out".
Extraction "p2t1b_G3_Cert.ml" p2t1b_g3_pick.

(* ############ Assumption audit: Print Assumptions on the four supply theorems ############ *)
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
(* ================= Section 2: the p2t1c family ================= *)
From Stdlib Require Import QArith.QArith.

(* ######## I. Independent rebuild of the three conclusions 9(e) bounds #### *)

(* p2t1c_T2_abs_le_quad_supply: |X| <=_B 2t^2+(eps1+eps2). Premises         *)
(* X <= eps1, -X <= 2t^2+eps2, 0 < eps1, 0 < eps2. Proof: from the tree     *)
(* lemma real_abs_le_quad_eps via real_le_closure_b_one, quantifying the    *)
(* remainder eps universally.                                               *)
Theorem p2t1c_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB Heps1 Heps2.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_abs_le_quad_eps X t eps1 eps2 eps HXA HXB Heps1 Heps2 Heps).
Qed.

(* p2t1c_T2_quad_t_le_h_supply: 2(h/x)^2 <=_B (1/2)*eps*|h|; premises       *)
(* 0 < x, |h| < eps*x^2/4, 0 < eps; derived from real_quad_t_le_h_eps       *)
(* via real_le_closure_b_one.                                               *)
Theorem p2t1c_T2_quad_t_le_h_supply : forall (x h eps : Real)
    (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_quad_t_le_h_eps x h eps eps' Hx Hh Heps Heps').
Qed.

(* p2t1c_T2_abs_h_sq_supply: A|h|^2 <=_B (A*eps3)*|h|; premises 0 < A,      *)
(* |h| < eps3; one step from real_abs_h_sq_le_eps via                       *)
(* real_le_closure_b_one.                                                   *)
Theorem p2t1c_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_abs_h_sq_le_eps A h eps3 eps' HA Hh3 Heps').
Qed.

(* ######## II. Restatement face of conclusion 9(f) and type-level mutual check ####### *)

(* p2t1c_T2_db_breaking_bound_reg: restatement (as a Definition) of the db  *)
(* breaking bound in composite-coefficient form, the composite coefficient  *)
(* having the inv(partition)*T*(exp*...) shape. The type of this Definition *)
(* is an independent restatement of the statement face; the value term is   *)
(* p2t1b_T2_db_breaking_bound_supply - if the two agree verbatim the type   *)
(* assembles, otherwise compilation fails (the mutual check is carried out  *)
(* by type checking).                                                       *)
Definition p2t1c_T2_db_breaking_bound_reg :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s'))))))) :=
  p2t1b_T2_db_breaking_bound_supply.

(* #### III. Cross-check: type assembly of the four named part-b faces against the restated statements #### *)
(* Each Check takes the independently restated statement of this file as    *)
(* the type and the part-b named face as the term: type assembly succeeds   *)
(* iff the two statement faces agree verbatim (the mutual check is carried  *)
(* out by type checking).                                                   *)

Check (p2t1b_T2_abs_le_quad_supply :
  forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2))).

Check (p2t1b_T2_quad_t_le_h_supply :
  forall (x h eps : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h))).

Check (p2t1b_T2_abs_h_sq_supply :
  forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h))).

Check (p2t1b_T2_db_breaking_bound_supply :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s')))))))).

(* ############ Extraction check: the witness face is a Q-layer pure function ############ *)
(* The real-layer interface statements stay out of the extraction set; the  *)
(* extraction witness face is a separate Q-layer pure function, matched in  *)
(* topic to the pointwise positive-eps supply family 1/(n+2) of the         *)
(* multi-eps combination.                                                   *)
Definition p2t1c_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1c_g3out".
Extraction "p2t1c_G3_Cert.ml" p2t1c_g3_pick.

(* ############ Assumption audit: Print Assumptions on all eight conclusions at end of file ############ *)
Print Assumptions p2t1c_T2_abs_le_quad_supply.
Print Assumptions p2t1c_T2_quad_t_le_h_supply.
Print Assumptions p2t1c_T2_abs_h_sq_supply.
Print Assumptions p2t1c_T2_db_breaking_bound_reg.
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
