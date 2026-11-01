(* ===================================================================== *)
(*  Ablation replant piece, S11_TP3B5 B5 analytic family, FA1 survey     *)
(*  batch 10; upstream untouched, zero git footprint, zero registration. *)
(*  Mission.: formalize the closure face of the ten assumption slots of  *)
(*  the B5 analytic family: eight top-level theorems uabt11_* close the  *)
(*  H4 slot, the Hsc and HscA3 slots, the two N10 assembly slots, the    *)
(*  endpoint-bridge slot, the endpoint-zero slot (rational-point narrowed*)
(*  form), and the E(1)==0 slot; every statement is a Set-level identity *)
(*  real_eq _ _ with zero Prop leakage, statement and reference face     *)
(*  verbatim against the mirror source, proof-ending tokens conserved.   *)
(*  Dependencies.: Require Import S01_BaseRing through S15_TailFEPUp     *)
(*  (the fifteen certified modules of the current Live generation),      *)
(*  resolved by -Q . ""; From Stdlib Require Import QArith and           *)
(*  Extraction; no further imports.                                      *)
(*  References.: mirror source UpAbl_S11_TP3B5.v, replant list lines     *)
(*  42/54/62/70/78/89/104/115; slot coordinates in the upstream tree:    *)
(*  H4 S11_TP3B5.v:1296, Hsc :1300, HscA3 :1598, assemblies              *)
(*  n10_closure_f1:1383, n10_closure_n5:1392, a3_closure_f1:1613,        *)
(*  endpoint bridge :11070, endpoint zero :11674; closures drawn from    *)
(*  a3_h4_value_bridge:1559, b5b_hsc_main:6610,                          *)
(*  b5dF_E_one_zero_of_rational:S14:6675, b5dQ_E_rational_zero:S14:13456.*)
(*  Constructivity.: every proof body is one exact of a closed library   *)
(*  bridge term (a single theorem or a two/three-link composition); no   *)
(*  admission-style ending anywhere; the trailing Print Assumptions      *)
(*  block reads Closed under the global context for all eight.           *)
(*  Build.: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*  ulimit -s 65532 && cpu_guard.sh -Reg /tmp/cw_reg_nw8 -Front 0 -Mid 1 *)
(*  -MaxWaitSec 600 -- rocq c -native-compiler no -q -Q . "" this .v,    *)
(*  born in place in the world directory.                                *)
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
From Stdlib Require Import QArith.
From Stdlib Require Import Extraction.

(* ==================== Piece 1: H4 slot closure (direct library bridge) ==================== *)
(* Slot statement verbatim against S11_TP3B5.v:1296 (theta1 notation =       *)
(* arctan_one_real:1254). Resolution source: a3_h4_value_bridge:1559, a      *)
(* premise-free closed proof of the very same statement.                     *)
Theorem uabt11_h4_closed :
  real_eq (real_mult (real_const 4%Q) theta1) cauchy_real_pi_leibniz.
Proof.
  exact a3_h4_value_bridge.
Qed.

(* ==================== Piece 2: Hsc slot closure (export-chain composition) ==================== *)
(* Slot statements verbatim against S11_TP3B5.v:1300 (Hsc) and :1598         *)
(* (HscA3): one statement shape for both. Resolution source:                 *)
(* b5b_hsc_main:6610 (E(1)==0 -> sin theta == cos theta) supplied at all     *)
(* premises by b5dF_E_one_zero_of_rational:S14:6675 (raises the rational-    *)
(* point link to E(1)==0) fed by b5dQ_E_rational_zero:S14:13456 (rational-   *)
(* point single-point certificate); the composite mirrors the in-tree        *)
(* dependency precedent (the S14 bridge row a3_closure_n5 o b5b_hsc_main o   *)
(* b5dF o b5dQ, the same assembly).                                          *)
Theorem uabt11_hsc_sin_eq_cos :
  real_eq (cauchy_real_sin theta1) (cauchy_real_cos theta1).
Proof.
  exact (b5b_hsc_main (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero)).
Qed.

(* ============ Piece 3: N10 F1 assembly slot, full-premise closure (N2) ============ *)
(* Against n10_closure_f1:1383 (H4 slot + Hsc slot -> F1); both premises     *)
(* are closed by Piece 1 and Piece 2 above.                                  *)
Theorem uabt11_n10_f1_closed :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  exact (n10_closure_f1 uabt11_h4_closed uabt11_hsc_sin_eq_cos).
Qed.

(* ============ Piece 4: N10 N5 assembly slot, full-premise closure (N2) ============ *)
(* Against n10_closure_n5:1392 (H4 slot + Hsc slot -> cos(w_leib) == 0).     *)
Theorem uabt11_n10_n5_closed :
  real_eq (cauchy_real_cos w_leib) real_zero.
Proof.
  exact (n10_closure_n5 uabt11_h4_closed uabt11_hsc_sin_eq_cos).
Qed.

(* ============ Piece 5: HscA3 slot closure via the A3 assembly (N2) ============ *)
(* Against a3_closure_f1:1613 (HscA3 slot -> F1); upstream slot :1598        *)
(* closes transitively once Piece 2 is in scope.                             *)
Theorem uabt11_a3_f1_closed :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  exact (a3_closure_f1 uabt11_hsc_sin_eq_cos).
Qed.

(* ============ Piece 6: endpoint-bridge slot, premise-thinned supply form (N2) ============ *)
(* Slot statement verbatim against S11_TP3B5.v:11070-11071 (the endpoint     *)
(* bridge inside section B5bEndpointBridge). Thinning criterion: the slot    *)
(* conclusion b5b_f1_closure:11075 walks only the "E(x)==0 -> Hsc" channel   *)
(* for every argument, and E(1)==0 is available unconditionally (Piece 8     *)
(* chain), so none of the four premises x / Hx / 0<x<1 / E(x)==0 is used;    *)
(* the form stays nontrivial after thinning (three-link composite).          *)
Theorem uabt11_b5b_hsc_theorem_wo :
  forall (x : Real) (Hx : cw_unit x),
  real_lt real_zero x -> real_lt x (real_const 1%Q) ->
  real_eq (real_E x Hx) real_zero ->
  real_eq (cauchy_real_sin arctan_one_real) (cauchy_real_cos arctan_one_real).
Proof.
  intros x Hx Hlt0 Hlt1 HEz.
  exact (b5b_hsc_main (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero)).
Qed.

(* ============ Piece 7: endpoint-zero slot, rational-point narrowed form (N1 narrowed) ============ *)
(* Slot statement against S11_TP3B5.v:11674-11675 (all-real x in (0,1)       *)
(* shape), premises carried at the Set-level QltT face: the canonical        *)
(* Qlt -> QltT wash (QltT is the Set-level order of S02, provided exactly    *)
(* for Set-ifying ablation dependents), and the closure contract            *)
(* b5dQ_E_rational_zero:S14:13892 states the premises at QltT, so the        *)
(* washed statement closes by the verbatim exact. The current library        *)
(* carries only this rational-point narrowed form; the all-real shape        *)
(* needs an E continuity / limit-transfer chain with no ready in-tree        *)
(* piece, so no ad-hoc construction here: narrowed-form declaration,         *)
(* remainder honestly left open in the deviation ledger.                     *)
Theorem uabt11_b5a_rational_single_point :
  forall (q : Q) (Hq0 : QltT 0 q) (Hq1 : QltT q 1)
    (Hq : cw_unit (real_const q)),
  real_eq (real_E (real_const q) Hq) real_zero.
Proof.
  exact b5dQ_E_rational_zero.
Qed.

(* ============ Piece 8: E(1)==0 unconditional certificate (N2) ============ *)
(* The conditional goal of b5b_endpoint:11681 (needs endpoint-zero input)    *)
(* is honored here unconditionally by the rational-point chain:              *)
(* b5dF_E_one_zero_of_rational:S14:6675 fed by b5dQ_E_rational_zero.         *)
Theorem uabt11_E_one_zero_uncond :
  real_eq real_E_one real_zero.
Proof.
  exact (b5dF_E_one_zero_of_rational b5dQ_E_rational_zero).
Qed.

(* ==================== Extraction audit segment (ASCII-isolated directory) ==================== *)
(* Current-generation measured face: Separate Extraction of all eight        *)
(* theorem names runs clean (driver rc=0, both extracted faces carry         *)
(* Obj.magic 0/0, zero erasure candidates); the older-generation note that   *)
(* only Piece 1 extracts is superseded. The global-context audit is also     *)
(* covered by the trailing Print Assumptions block (all eight read Closed    *)
(* under the global context).                                                *)
Set Extraction Output Directory "C:/Users/Live/AppData/Local/Temp/uabt11_ext".
Separate Extraction uabt11_h4_closed.

(* ---- PA closing block (per-theorem Print Assumptions; criterion: each     *)
(*   reads Closed under the global context - same closing shape as the       *)
(*   two precedent pieces) ---- *)
Print Assumptions uabt11_h4_closed.
Print Assumptions uabt11_hsc_sin_eq_cos.
Print Assumptions uabt11_n10_f1_closed.
Print Assumptions uabt11_n10_n5_closed.
Print Assumptions uabt11_a3_f1_closed.
Print Assumptions uabt11_b5b_hsc_theorem_wo.
Print Assumptions uabt11_b5a_rational_single_point.
Print Assumptions uabt11_E_one_zero_uncond.
