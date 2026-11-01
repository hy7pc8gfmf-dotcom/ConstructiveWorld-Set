(* ==========================================================================
   UpAblT9_UpReqSampling.v - materialization piece for the UpReqSampling
   jurisdiction: two Context-bundle stations and two TV-face stations.
   Mission.
     Materialize four theorems: aux_delta_plus_omd, rsq_bs_list_const_sum,
     the concrete delta_star instance face, and the cross-module
     minorization (tvd_minorization fully specialized).
   Dependencies.
     CW_ConstructiveWorld_219; UpReqAlgebra; UpReqDist; UpReqSumD;
     UpTVDoeblin; UpReqSampling; Stdlib List; S01-S15 chain per Require face.
   References.
     The instance layer of the minorization condition for total-variation
     convergence.
   Constructivity.
     Every station Qed-closed; the interface projection predicates (req, lt,
     le at the RealEnhancedReal instance) are canonically stated at their
     definitional raw-layer forms real_eq, real_lt, real_le, discharged
     verbatim by exact; read-only dependencies, origin tree untouched.
   Build.
     Rocq 9.1 direct rocq c -Q . "" -native-compiler no (vo shadow tree
     in-place recompile), cpu_guard thermal wrapper for load control.
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSumD.
Require Import UpTVDoeblin.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* Station 1 <- :99 (rep@:153; materialization at the R/RIS instance position) *)
Theorem uabT9_usamp_ctx_delta_plus_omd :
  forall delta : Real, real_eq (plus delta (req_minus one delta)) one.
Proof.
  intro delta.
  (* bridge: the current tree carries aux_delta_plus_omd already at the
     fixed Real-instance layer (no R/RI prefix), per this-seat sigprobe *)
  exact (aux_delta_plus_omd delta).
Qed.

(* Station 2 <- :701 (rep@:790; materialization at the R/RIS instance position,
   zero interface premises) *)
Theorem uabT9_bsoft_ctx_list_const_sum :
  forall (S : Set) (c : Real) (l : list S),
    real_eq (rsq_bs_list_sum S (fun _ : S => c) l)
       (mult (reqd_nat_to_R (length l)) c).
Proof.
  intros S c l.
  (* bridge r1: rsq_bs_list_const_sum is at the fixed Real-instance layer *)
  exact (rsq_bs_list_const_sum S c l).
Qed.

(* Station 3 <- :126 (rep@:935; concrete delta_star instance materialization,
   TV face) *)
Theorem uabT9_usamp_delta_star_lt_one :
  forall (temp : Real) (temp_pos : real_lt zero temp)
         (Delta : Real) (Delta_pos : real_lt zero Delta),
    real_lt (mult (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))
             (rsq_exp_pos_fn (mult (inv_pos temp temp_pos) (opp Delta)))) one.
Proof.
  intros temp temp_pos Delta Delta_pos.
  (* bridge r1: rsq_bs_delta_star_lt_one is at the fixed Real-instance layer *)
  exact (rsq_bs_delta_star_lt_one temp temp_pos Delta Delta_pos).
Qed.

(* Station 4 <- :131 (rep=UpTVDoeblin:1933 instance face; TV face) *)
Theorem uabT9_usamp_minorization_tvd :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
         (z : list Real -> list Real -> Real),
    (forall i j : list Real, real_le (real_opp gamma) (z i j)) ->
    (forall i j : list Real, real_le (z i j) gamma) ->
    forall i j : list Real,
      real_le (mult (tvd_dstar Ttemp Ttemp_pos gamma) (tvd_u states n_pos j))
         (tvd_K states n_pos Ttemp Ttemp_pos z i j).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j.
  exact (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j).
Qed.

(* ---- PA closing ---- *)
Print Assumptions uabT9_usamp_ctx_delta_plus_omd.
Print Assumptions uabT9_bsoft_ctx_list_const_sum.
Print Assumptions uabT9_usamp_delta_star_lt_one.
Print Assumptions uabT9_usamp_minorization_tvd.
