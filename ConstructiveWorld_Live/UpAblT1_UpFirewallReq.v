(* ==========================================================================
   UpAblT1_UpFirewallReq.v - discharge piece for the FirewallReq req-sum
   interface stations, at the enumerated finite-sum instance sumd_sumf
   of UpReqSumD (Section FirewallReq sumf premise slots discharged).
   Mission.
     Discharge five req-sum stations at sumd_sumf S enum: extensionality
     uabT1_fw_ssum_ext, additivity uabT1_fw_ssum_add, linearity
     uabT1_fw_ssum_linear, monotonicity uabT1_fw_ssum_le, positivity
     uabT1_fw_ssum_pos (datum Not (enum = nil), sumd_sum_pos shape).
     Interface assumption slots eliminated; premises reduce to data.
   Dependencies.
     S01-S15 per Require face; UpReqSumD (transitively UpReqAlgebra and
     UpReqDist); Stdlib List; RealInterfaceEnhancedMod per Import face.
   References.
     Station faces follow the FirewallReq sumf interface face verbatim,
     sumf instantiated to sumd_sumf S enum; discharged content is the
     UpReqSumD sumd_sum_* list-induction chain.
   Constructivity.
     Every station Qed-closed; faces name the concrete Set-valued
     carriers real_eq/real_le/real_lt (the S02 Real-layer carriers,
     definitionally the interface req/le/lt at the RealEnhancedReal
     instance) so statement and body share one extracted carrier face.
     Heads are materialized at the Real-instance position per the
     sigprobe-measured tree signature (machine at the fixed Real
     layer, former R/RIS head absorbed by the global instance, carrier
     reads (S : Set)); the bare list premise Not (enum = nil) keeps
     its premise position, the sumd_sum_pos lawful shape.
   Build.
     Rocq 9.1 rocq c -Q . "" -native-compiler no, cpu_guard wrapper.
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Station 1 <- FirewallReq ssum_ext (sumf interface face); discharge at
   sumd_sumf S enum via the UpReqSumD list-induction chain, direct link *)
Theorem uabT1_fw_ssum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* Station 2 <- FirewallReq ssum_add; sumd_sum_add direct link *)
Theorem uabT1_fw_ssum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* Station 3 <- FirewallReq ssum_linear; sumd_sum_linear direct link *)
Theorem uabT1_fw_ssum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* Station 4 <- FirewallReq ssum_le; sumd_sum_le direct link *)
Theorem uabT1_fw_ssum_le :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* Station 5 <- FirewallReq ssum_pos; the non-emptiness datum stays in the
   source premise position (lawful premise-face identity, sumd_sum_pos
   same shape); sumd_sum_pos direct link *)
Theorem uabT1_fw_ssum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ---- PA closing (per-station Closed readout) ---- *)
Print Assumptions uabT1_fw_ssum_ext.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_pos.
