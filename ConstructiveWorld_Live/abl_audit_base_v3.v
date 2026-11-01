(* ===================================================================== *)
(*  abl_audit_base_v3.v - audit-carrier expansion v3: closure of the      *)
(*  remaining direct-audit seats of the S02 base (form-A piece).          *)
(*  Mission. Closes the remaining seats of the BX-ledger all-8-TC direct  *)
(*  audit account of the S02 base: S02_CauchyComplete carries exactly 8   *)
(*  top-level Theorems; v1 already collected real_cauchy_complete (1/8);  *)
(*  this piece closes the remaining 7 one by one - the four main seats    *)
(*  real_lim_unique / real_lim_plus / real_lim_scal / real_lim_mult each  *)
(*  emit one Set-level light true-use carrier theorem, while the three    *)
(*  negative-type seats real_square_not_negative / step_not_unif_pointwise *)
(*  / step_not_lim_zero carry Not (Prop-face) statement forms, so per the *)
(*  zero-Prop-carrier red line no use face is emitted for them: they are  *)
(*  closed by tail-bay qualified direct audit (recorded as-is, not a gap). *)
(*  The tail bay runs 11 Print Assumptions: direct audit of the remaining *)
(*  7 seats (the 8/8 total account closed together with v1) plus the      *)
(*  self-audit of this piece's four carriers.                             *)
(*  Dependencies. S01_BaseRing S02_CauchyComplete (read-only -Q reference *)
(*  into the prebuilt world tree) plus Stdlib QArith (the 2%Q notation    *)
(*  face).                                                                *)
(*  References. abl_audit_base_v1, same-family in-tree precedent (its     *)
(*  1/8 seat); v4/v6 same-family carrier shapes; S02:399 real_eq as a     *)
(*  Set-type per-eps sigT face (unique-carrier conclusion at Set level).  *)
(*  Constructivity. Whole file Qed-closed, zero acknowledgement faces, no *)
(*  classical logic; statement faces all Set level (real_lim / real_eq /  *)
(*  real_lt are S02 : Set definitions, sigT-carried), zero Prop leakage;  *)
(*  proof bodies are all explicit exact terms, no tactic search face.     *)
(*  Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;   *)
(*  rocq c -native-compiler no -q -Q <world-dir> "" abl_audit_base_v3.v   *)
(*  (single -Q pool; world supplied by the certified generation).         *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith.

(* ============================================================ *)
(* Section 1 - carrier statement bay: four main seats, light      *)
(*   true use (one per TC, all Set level). Every carrier is a    *)
(*   fresh statement: it exercises the main theorem body via a   *)
(*   concrete instantiation / a two-theorem chain, not a         *)
(*   forwarding shell.                                           *)
(* ============================================================ *)

(* Main seat plus: the doubled sequence converges. real_lim_plus  *)
(*   is instantiated at u := v := u, l1 := l2 := l, so the        *)
(*   doubled sequence (fun n => u n + u n) converges to l + l -   *)
(*   a concrete doubling instance, not a generic forward.         *)
Theorem abc_lim_square_via_plus :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n))
      (S02_CauchyComplete.real_plus l l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_plus u u l l H H).
Qed.

(* Main seat scal: the twice-scaled sequence converges.           *)
(*   real_lim_scal is instantiated at the concrete c := 2%Q, so   *)
(*   the scalar-multiplied sequence converges to 2 * l - the      *)
(*   eps/(2(|c|+1)) machinery inside _scal is exercised at a      *)
(*   concrete scale.                                              *)
Theorem abc_lim_twice_via_scal :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat =>
         S02_CauchyComplete.real_mult (S02_CauchyComplete.real_const 2%Q) (u n))
      (S02_CauchyComplete.real_mult (S02_CauchyComplete.real_const 2%Q) l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_scal u l 2%Q H).
Qed.

(* Main seat mult: the squared sequence converges. real_lim_mult  *)
(*   is instantiated at u := v := u, l1 := l2 := l, so the        *)
(*   squared sequence converges to l * l - a concrete squaring    *)
(*   instance.                                                    *)
Theorem abc_lim_square_via_mult :
  forall (u : nat -> S02_CauchyComplete.Real) (l : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim u l ->
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_mult (u n) (u n))
      (S02_CauchyComplete.real_mult l l).
Proof.
  intros u l H.
  exact (S02_CauchyComplete.real_lim_mult u u l l H H).
Qed.

(* Main seat unique: a two-theorem-chain carrier. The doubled     *)
(*   sequence has a unique limit, equal to the double of the      *)
(*   original limit - real_lim_plus first supplies the canonical  *)
(*   limit of the doubled sequence, then real_lim_unique judges   *)
(*   the agreement; the two main seats are chained in true use    *)
(*   within one theorem, the real_eq conclusion landing at Set    *)
(*   level.                                                       *)
Theorem abc_lim_unique_double :
  forall (u : nat -> S02_CauchyComplete.Real)
         (l1 l2 : S02_CauchyComplete.Real),
    S02_CauchyComplete.real_lim
      (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n)) l1 ->
    S02_CauchyComplete.real_lim u l2 ->
    S02_CauchyComplete.real_eq l1 (S02_CauchyComplete.real_plus l2 l2).
Proof.
  intros u l1 l2 Hd H.
  exact (S02_CauchyComplete.real_lim_unique
           (fun n : nat => S02_CauchyComplete.real_plus (u n) (u n))
           l1 (S02_CauchyComplete.real_plus l2 l2) Hd
           (S02_CauchyComplete.real_lim_plus u u l2 l2 H H)).
Qed.

(* ============================================================ *)
(* Section 2 - tail bay: assumption audit (direct audit of the    *)
(*   remaining 7 seats cross-file and qualified, plus the self-   *)
(*   audit of this piece's four carriers). Reading rule: all 11   *)
(*   outputs below must be Closed under the global context. The   *)
(*   first seven are direct audits of the remaining 7 S02 seats   *)
(*   (one-to-one with the header total account: the four main     *)
(*   seats first, the three negative-type seats after; the 8/8    *)
(*   total account closes together with v1 real_cauchy_complete); *)
(*   the last four are the self-audits of this piece's carriers   *)
(*   (above the PA >= 1 floor).                                   *)
(* ============================================================ *)

Print Assumptions S02_CauchyComplete.real_lim_unique.
Print Assumptions S02_CauchyComplete.real_lim_plus.
Print Assumptions S02_CauchyComplete.real_lim_scal.
Print Assumptions S02_CauchyComplete.real_lim_mult.
Print Assumptions S02_CauchyComplete.real_square_not_negative.
Print Assumptions S02_CauchyComplete.step_not_unif_pointwise.
Print Assumptions S02_CauchyComplete.step_not_lim_zero.
Print Assumptions abc_lim_square_via_plus.
Print Assumptions abc_lim_twice_via_scal.
Print Assumptions abc_lim_square_via_mult.
Print Assumptions abc_lim_unique_double.

(* ============================================================ *)
(* Section 3 - exit bay: the carriers double as extraction ports  *)
(*   (G3: zero magic numbers on the extraction face; the literal  *)
(*   criterion is recorded in the audit account).                 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abc_lim_square_via_plus abc_lim_twice_via_scal
                    abc_lim_square_via_mult abc_lim_unique_double.
