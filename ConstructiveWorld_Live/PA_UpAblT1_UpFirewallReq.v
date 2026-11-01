(* ===================================================================== *)
(*  PA_UpAblT1_UpFirewallReq.v - ablation discharge of the five req-sum   *)
(*  assumption slots of the FirewallReq section at the concrete           *)
(*  enumerated finite-sum operator.                                       *)
(*  Mission. Each FirewallReq section assumption slot over an abstract    *)
(*  sum operator (ssum_ext/ssum_add/ssum_linear/ssum_le/ssum_pos, one     *)
(*  per source interface field) holds unconditionally at the concrete     *)
(*  operator sumf := sumd_sumf S enum (the enumerated list sum of         *)
(*  UpReqSumD): the assumption slots collapse into pure data slots (the   *)
(*  enumeration list). Five discharge theorems, prefix uabT1_, one per    *)
(*  slot, each direct-connecting to its in-tree discharge lemma           *)
(*  sumd_sum_* (no thin forwarders); G5 keeps the nonempty data slot      *)
(*  Not (enum = nil), same shape and order as sumd_sum_pos.               *)
(*  Dependencies. S01_BaseRing through S15_TailFEPUp plus UpReqSumD       *)
(*  (transitively UpReqAlgebra/UpReqDist), read-only -Q reference into    *)
(*  the prebuilt world tree; Stdlib List and the                          *)
(*  RealInterfaceEnhancedMod import, 1:1 with the source Require face.    *)
(*  References. UpFirewallReq.v Section FirewallReq req-sum slots         *)
(*  (ssum_ext L79/ssum_add L81/ssum_linear L84/ssum_le L87/ssum_pos L89); *)
(*  discharge lemmas sumd_sum_ext/add/linear/le/pos of UpReqSumD.         *)
(*  Constructivity. Whole file Qed-closed, zero acknowledgement faces;    *)
(*  statement faces all Set level (real_eq/real_le/real_lt are           *)
(*  Set-valued per-eps faces; the G5 nonempty slot Not is a Prop-face     *)
(*  premise, recorded as-is); proof bodies are direct exact terms; tail   *)
(*  bay prints Print Assumptions per theorem.                             *)
(*  Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;   *)
(*  rocq c -native-compiler no -q -Q <world-dir> ""                       *)
(*  PA_UpAblT1_UpFirewallReq.v (single -Q pool, certified world).         *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(*  Jurisdiction: the req-sum interface slots of the FirewallReq section  *)
(*  of UpFirewallReq.v (five faces over an arbitrary sum operator).       *)
(*  Instantiated discharge source: sumd_* of UpReqSumD (the concrete      *)
(*  enumerated finite-sum machinery).                                     *)
(*                                                                        *)
(*  Purpose: discharge the req-sum assumption slots of the FirewallReq    *)
(*  section one by one as ablation theorems: each assumption slot (the    *)
(*  interface field assumed over an arbitrary sumf operator) holds        *)
(*  unconditionally at the concrete finite-sum instance                   *)
(*  sumf := sumd_sumf S enum - the premise thins down to a pure data      *)
(*  slot (the enumeration list), the assumption slot eliminated. The      *)
(*  zero/plus/mult/lt/le family of the source section are projection      *)
(*  aliases (source section top); this piece uses real_eq/real_le/        *)
(*  real_lt directly, denotation identical.                               *)
(*                                                                        *)
(*  Main piece list (5 pieces, prefix uabT1_, each annotated with the     *)
(*  ablated slot coordinate and the instantiated discharge piece):        *)
(*   G1 uabT1_fw_ssum_ext     <- L79 ssum_ext     discharge sumd_sum_ext   *)
(*   G2 uabT1_fw_ssum_add     <- L81 ssum_add     discharge sumd_sum_add   *)
(*   G3 uabT1_fw_ssum_linear  <- L84 ssum_linear  discharge sumd_sum_linear *)
(*   G4 uabT1_fw_ssum_le      <- L87 ssum_le      discharge sumd_sum_le    *)
(*   G5 uabT1_fw_ssum_pos     <- L89 ssum_pos     discharge sumd_sum_pos   *)
(*       (explicit nonempty data slot: Not (enum = nil); same shape and   *)
(*        order as the sumd body; the source slot has no such argument)   *)
(*                                                                        *)
(*  Grading: all 5 pieces N1 (in-tree instantiated discharge direct       *)
(*  connect: the ablated assumption already has an unconditional form     *)
(*  in-tree; zero construction-register coordinates = the discharge       *)
(*  pieces listed above; the nontrivial proof content lives in the        *)
(*  discharge bodies - the list induction chain sumd_list_sum_*; this     *)
(*  piece direct-connects, no padding).                                   *)
(*                                                                        *)
(*  Dependencies (all read-only, source tree zero-touch):                 *)
(*  CW_ConstructiveWorld_219, UpReqSumD (transitively                     *)
(*  UpReqAlgebra/UpReqDist). Statement faces extracted 1:1 from the       *)
(*  current-archive UpFirewallReq.v (Section FirewallReq), with only      *)
(*  the sumf -> sumd_sumf S enum instantiation slot swapped.              *)
(*                                                                        *)
(*  Note: statement faces all Set level (req/le/lt are Set-valued         *)
(*  predicates; the nonempty premise Not slot is same shape and order     *)
(*  as UpReqSumD); no new assumption-face additions; the tail closes    *)
(*  with per-theorem Print Assumptions.                                   *)
(* ===================================================================== *)

(* G1 <- UpFirewallReq.v L79 ssum_ext (slot: pointwise real_eq gives real_eq of sums) *)
Theorem uabT1_fw_ssum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* G2 <- L81 ssum_add *)
Theorem uabT1_fw_ssum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* G3 <- L84 ssum_linear *)
Theorem uabT1_fw_ssum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* G4 <- L87 ssum_le *)
Theorem uabT1_fw_ssum_le :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* G5 <- L89 ssum_pos (explicit nonempty data slot, same shape as sumd_sum_pos) *)
Theorem uabT1_fw_ssum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ PA closing bay (per-theorem Closed audit) ============ *)
Print Assumptions uabT1_fw_ssum_ext.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_pos.

Print Assumptions uabT1_fw_ssum_pos.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_ext.
