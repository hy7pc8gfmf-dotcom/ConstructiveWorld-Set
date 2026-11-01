(* UpAblD1S4_UpReqStepKLEtaInst.v - FA-D1S4 data-supply pack piece (standalone
    auxiliary module; zero tree edits). Mission.  Formalization of the
    properties stated by this piece's theorem and lemma declaration faces.  ToyR
    replacement piece: the original text is kept verbatim; only the listed proof
    bodies carry the replacement; declaration and reference faces untouched;
    zero added Require; purely constructive closure with the tail Print
    Assumptions census retained. Identity-conservation audit verdict: the listed
    proof bodies are byte-identical to the Main originals (knife body = original
    body): 0 true replacements, 5 identity-conserved slots - uabd1s4_two_pos
    (orig L41), uabd1s4_half_pos (orig L48), uabd1s4_half_plus_half (orig L54),
    uabd1s4_half_sum_two (orig L84), uabd1s4_ske_pack12_supplied (orig L118).
    Jurisdiction: upstream UpReqStepKLEtaInst.v Section SkeInst, all 12 slots at
    archive coords L176-189 (slot anchors k:176 through Hpref:189; L177-178 is
    the Let n := S k, not an interface argument); main anchor = instance face of
    real_step_kl_eta_bound_eps (UpStepKL.v:682); instance-face data supply only,
    zero source-file Require (guards against mixed-generation .vo hazards);
    pack-record shape, the fa57 two-point instance feeding the whole domain.
    Instance supply: k := 1 (two states 0/1); beta := eta := real_one; r := the
    zero map; pit := piref := the half map; Hetale := reflexivity;
    Hbeta/Heta/Hpit/Hpref := one-line positivity matches; Hpitn := the
    half+half==one chain (five-step real_eq_trans chain, zero logical wall);
    grading: all 12 slots data-supply grade, merged as one declared piece.
    Dependencies.  The in-file Require declaration faces: Stdlib List plus
    S01_BaseRing through S15_TailFEPUp (S02 ring laws, S03 inverse device, S07
    order and zero device, S08 list-sum device; all read-only); zero git, zero
    registry-face increment. References.  Upstream anchors above; verification
    trail Live_X/attn/logs/g{1..4}-UpAblD1S4_*.{log,exit}. Constructivity.
    axiom-free, zero acknowledgment statements (mechanically verified), Set-tier
    constructive content only. Build.  rocq c -native-compiler no -q -Q . ""
 *)

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

(* ============ Supply-base module: the two-point uniform half function (Real-carrier version of the fa57 two-point device) ============ *)

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

(* Normalization-chain core limb: half+half == one (Real-carrier copy of fa57_half_plus_half) *)
Lemma uabd1s4_half_plus_half : real_eq (real_plus uabd1s4_half uabd1s4_half) real_one.
Proof.
  exact (real_eq_trans           (real_plus uabd1s4_half uabd1s4_half)           (real_mult uabd1s4_half uabd1s4_two)           real_one           (real_eq_trans              (real_plus uabd1s4_half uabd1s4_half)              (real_plus (real_mult uabd1s4_half real_one)                         (real_mult uabd1s4_half real_one))              (real_mult uabd1s4_half uabd1s4_two)              (RealSetoid.real_eq_plus_compat uabd1s4_half uabd1s4_half                                   (real_mult uabd1s4_half real_one)                                   (real_mult uabd1s4_half real_one)                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half))                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half)))              (real_eq_sym                 (real_mult uabd1s4_half uabd1s4_two)                 (real_plus (real_mult uabd1s4_half real_one)                            (real_mult uabd1s4_half real_one))                 (real_distrib uabd1s4_half real_one real_one)))           (real_eq_trans              (real_mult uabd1s4_half uabd1s4_two)              (real_mult uabd1s4_two uabd1s4_half)              real_one              (real_mult_comm uabd1s4_half uabd1s4_two)              (real_inv_pos_correct uabd1s4_two uabd1s4_two_pos))).
Qed.

(* Hpitn supply limb: the two-state normalization for k := 1, pit := the half map (the list sum folded by cons, delta/iota expansion) *)
Lemma uabd1s4_half_sum_two :
  real_eq (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2)) real_one.
Proof.
  exact (real_eq_trans           (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2))           (real_plus uabd1s4_half uabd1s4_half)           real_one           (RealSetoid.real_eq_plus_compat uabd1s4_half (real_plus uabd1s4_half real_zero)                                uabd1s4_half uabd1s4_half                                (real_eq_refl uabd1s4_half)                                (real_plus_zero uabd1s4_half))           uabd1s4_half_plus_half).
Qed.

(* ============ Pack-record type: the 12 slot statements enter the pack verbatim (against the upstream source lines L176-189) ============ *)

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

(* ============ Dependent module: the two-point uniform instance feeds all 12 slots in one shot ============ *)

Theorem uabd1s4_ske_pack12_supplied : uabd1s4_ske_pack12.
Proof.
  exact (uabd1s4_ske_pack12_intro 1%nat           real_one real_lt_zero_one           (fun _ : nat => real_zero)           real_one real_lt_zero_one (real_le_refl real_one)           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)           uabd1s4_half_sum_two           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)).
Qed.

(* ============ Assumption-face closure declaration ============ *)

Print Assumptions uabd1s4_two_pos.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_ske_pack12_supplied.
