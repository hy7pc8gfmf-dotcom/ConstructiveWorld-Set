(* ===================================================================== *)
(*  PA_UpAblD1S4_UpReqStepKLEtaInst.v - PA re-verification twin piece of  *)
(*  UpAblD1S4_UpReqStepKLEtaInst (PA_-prefixed distinct file; MAIN        *)
(*  dual-piece coexistence with the nw9-selected original).               *)
(*  Mission. Supplies the full 12-slot data bundle of Section SkeInst of  *)
(*  UpReqStepKLEtaInst.v (slots k:176 beta:179 Hbeta:180 r:181 eta:182    *)
(*  Heta:183 Hetale:184 pit:185 Hpit:186 Hpitn:187 piref:188 Hpref:189;   *)
(*  slot n inlines delta-wise as Datatypes.S k per the Let n := S k) as   *)
(*  one closed packaging-record carrier fed by a two-point uniform       *)
(*  half-function instance (k:=1 states 0/1; beta:=eta:=real_one;        *)
(*  r:=zero fn; pit:=piref:=half fn; Hetale:=reflexivity; positive       *)
(*  slots by one-line direct matches; Hpitn by the half+half==one chain,  *)
(*  the longest limb: five-segment real_eq_trans chain, non-trivial       *)
(*  statement form, zero logical wall; all 12 slots honestly graded T     *)
(*  data-supply, one merged declaration pack12_supplied).                 *)
(*  Dependencies. Stdlib List; S01..S15 chain S01_BaseRing through        *)
(*  S15_TailFEPUp (read-only -Q deps; zero git, zero registration        *)
(*  growth); no Require of the anchor source file (anti P3S1 pit-1       *)
(*  mixed-generation .vo mine).                                           *)
(*  References. Main anchor real_step_kl_eta_bound_eps@UpStepKL.v:682     *)
(*  (census D1-7): instance face only, anchor body untouched; packaging-  *)
(*  record precedent UpAblP2_UpMinP_tokens_pack.v + fa57 two-point        *)
(*  instance feed (fa57_ext.v:193), here in its Real-carrier version.     *)
(*  Constructivity. Whole file Qed-closed, zero acknowledgement faces;    *)
(*  statement faces Set-carried canonical real_lt/real_le/real_eq (no     *)
(*  Qlt/Qle/==/bare =/nat<= leaves); tail keeps the original Print        *)
(*  Assumptions face plus the PA re-print segment: 10/10 Closed.          *)
(*  Build. source toolchain env; unset COQLIB ROCQLIB; ulimit -s 65532;   *)
(*  rocq c -native-compiler no -q -Q <world-dir> "" <this-file>          *)
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

(* ===== Supply base module: two-point uniform half function (Real-carrier fa57 two-point device) ===== *)

Definition uabd1s4_two : Real := real_plus real_one real_one.

Lemma uabd1s4_two_pos : real_lt real_zero uabd1s4_two.
Proof.
  exact real_two_pos.
Qed.

Definition uabd1s4_half : Real := real_inv_pos uabd1s4_two uabd1s4_two_pos.

Lemma uabd1s4_half_pos : real_lt real_zero uabd1s4_half.
Proof.
  exact (real_inv_pos_pos uabd1s4_two uabd1s4_two_pos).
Qed.

(* Normalization-chain core limb: half + half == one (Real-carrier copy of fa57_half_plus_half) *)
Lemma uabd1s4_half_plus_half : real_eq (real_plus uabd1s4_half uabd1s4_half) real_one.
Proof.
  exact (real_eq_trans           (real_plus uabd1s4_half uabd1s4_half)           (real_mult uabd1s4_half uabd1s4_two)           real_one           (real_eq_trans              (real_plus uabd1s4_half uabd1s4_half)              (real_plus (real_mult uabd1s4_half real_one)                         (real_mult uabd1s4_half real_one))              (real_mult uabd1s4_half uabd1s4_two)              (RealSetoid.real_eq_plus_compat uabd1s4_half uabd1s4_half                                   (real_mult uabd1s4_half real_one)                                   (real_mult uabd1s4_half real_one)                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half))                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half)))              (real_eq_sym                 (real_mult uabd1s4_half uabd1s4_two)                 (real_plus (real_mult uabd1s4_half real_one)                            (real_mult uabd1s4_half real_one))                 (real_distrib uabd1s4_half real_one real_one)))           (real_eq_trans              (real_mult uabd1s4_half uabd1s4_two)              (real_mult uabd1s4_two uabd1s4_half)              real_one              (real_mult_comm uabd1s4_half uabd1s4_two)              (real_inv_pos_correct uabd1s4_two uabd1s4_two_pos))).
Qed.

(* Hpitn supply limb: two-state normalization at k:=1, pit := half function (list sum folds by cons, delta/iota expansion) *)
Lemma uabd1s4_half_sum_two :
  real_eq (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2)) real_one.
Proof.
  exact (real_eq_trans           (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2))           (real_plus uabd1s4_half uabd1s4_half)           real_one           (RealSetoid.real_eq_plus_compat uabd1s4_half (real_plus uabd1s4_half real_zero)                                uabd1s4_half uabd1s4_half                                (real_eq_refl uabd1s4_half)                                (real_plus_zero uabd1s4_half))           uabd1s4_half_plus_half).
Qed.

(* ===== Packaging-record form: the 12 slot statements verbatim into the pack (against source file L176-189) ===== *)

Inductive uabd1s4_ske_pack12 : Set :=
| uabd1s4_ske_pack12_intro :
    forall k : nat,
      forall beta : Real,
        real_lt real_zero beta ->
        forall r : nat -> Real,
          forall eta : Real,
            real_lt real_zero eta ->
            real_le eta real_one ->
            forall pit : nat -> Real,
              (forall i : nat, real_lt real_zero (pit i)) ->
              real_eq (real_list_sum nat pit (List.seq 0 (Datatypes.S k))) real_one ->
              forall piref : nat -> Real,
                (forall i : nat, real_lt real_zero (piref i)) ->
                uabd1s4_ske_pack12.

(* ===== Dependency module: two-point uniform instance feeds all 12 slots in one exact application ===== *)

Theorem uabd1s4_ske_pack12_supplied : uabd1s4_ske_pack12.
Proof.
  exact (uabd1s4_ske_pack12_intro 1%nat           real_one real_lt_zero_one           (fun _ : nat => real_zero)           real_one real_lt_zero_one (real_le_refl real_one)           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)           uabd1s4_half_sum_two           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)).
Qed.

(* ===== Assumption-face closure declaration ===== *)

Print Assumptions uabd1s4_two_pos.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_ske_pack12_supplied.

(* PA re-print segment (verification twin piece) *)
Print Assumptions uabd1s4_ske_pack12_supplied.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_two_pos.
