(* Mission . Formalization of the properties stated by the declaration faces
   of this file's theorems/lemmas: a concrete-witness closure of the DPO
   pair-loss bounds and the reward-recovery identity over a boolean state
   space.
   Dependencies . The library modules listed by the in-file Require
   declaration faces: S02_CauchyComplete, S07_RealSetoidExpLog,
   S08_RealMainlineDPO.
   References . Ablation drop: the original file text is kept verbatim except
   that the proof bodies of the listed statements are replaced by toy proofs
   (substantive non-triviality via controlled definitional unfolding /
   explicit witness extraction / structural replay, with the engine position
   surveyed directly); declaration faces and reference faces unchanged, zero
   new Require, proof-end markers conserved item by item, purely constructive
   closure, and the original Print Assumptions block retained at the end.
   List:
     fa52_dpo_reward_recovery_concrete (original L75, 2-sentence toy proof)
     fa52_dpo_bounded_both_concrete (original L51, 1-sentence toy proof)
     fa52_dpo_reward_spread (original L42, 3-sentence toy proof) *)
(* Constructivity . Statement faces carry no assumption-style declarations
   (mechanically checked).
   Build . coqc -native-compiler no -q -Q . "" *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ===== fa52_dpo_witness.v ===== *)
(* Ablation target: all eight Variable premise slots of the section
   DpoPairMain in S08_RealMainlineDPO (S08_RealMainlineDPO.v:1104-1111:
     S / reward / beta / beta_pos / pi_ref / pi_ref_pos / Z_align /
     Z_align_pos).
   Witness (fully explicit construction, zero residual premises):
     S := bool; reward := if s then 2 else 1; beta := 1;
     pi_ref := constant 1; Z_align := 1.
   All three positivity slots are discharged by real_lt_zero_one
   (S07_RealSetoidExpLog.v:7090); the reward tiering 1 < 1 + 1 is composed
   from 0 < 1 via real_lt_plus_compat_lt_le (S07_RealSetoidExpLog.v:6259).
   Base pieces used: after End, the main theorems
   real_dpo_loss_pi_star_bounded_both (S08_RealMainlineDPO.v:1525) and
   real_dpo_reward_recovers_up_to_baseline (S08_RealMainlineDPO.v:1571),
   specialized with all arguments supplied - the section's DPO theorems
   close as closed statements under the concrete witness.
   Red line: purely constructive, zero assumption-style pieces; non-trivial
   (premise instantiation plus post-End full-argument specialization).
   Tail note: the closed form log 1 == 0 inside the recovery statement
   needs a real_log_one bridge, kept as a follow-up candidate. *)

(* ---------- Concrete witness ---------- *)
Definition fa52_dpo_S : Type := bool.
Definition fa52_dpo_reward : bool -> Real :=
  fun s : bool => if s then real_plus real_one real_one else real_one.
Definition fa52_dpo_pi_ref : bool -> Real := fun _ : bool => real_one.
Definition fa52_dpo_pi_ref_pos : forall s : bool, real_lt real_zero (fa52_dpo_pi_ref s) :=
  fun _ : bool => real_lt_zero_one.

(* ---------- 1 < 2 (composed from 0 < 1 plus algebraic normalization) ---------- *)
Lemma fa52_one_two_lt : real_lt real_one (real_plus real_one real_one).
Proof.
  assert (HL : real_eq (real_plus real_zero real_one) real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (real_plus_comm real_zero real_one).
    - apply (real_plus_zero real_one). }
  assert (Hstep : real_lt (real_plus real_zero real_one)
                          (real_plus real_one real_one)).
  { exact (real_lt_plus_compat_lt_le real_zero real_one real_one real_one
             real_lt_zero_one (real_le_refl real_one)). }
  exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ HL) Hstep).
Qed.

Lemma fa52_dpo_reward_spread :
  real_lt (fa52_dpo_reward false) (fa52_dpo_reward true).
Proof.
  unfold fa52_dpo_reward.
  simpl.
  exact fa52_one_two_lt.
Qed.

(* ---------- Main piece 1: DPO loss at pi* bounded in (0, ln 2) - witness-specialized closed statement ---------- *)
Theorem fa52_dpo_bounded_both_concrete :
  S01_BaseRing.And
    (real_lt real_zero
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false))
    (real_lt
       (real_dpo_loss_pair bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
          (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref real_one real_lt_zero_one)
          (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
             fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
          true false)
       (real_log (real_plus real_one real_one) real_two_pos)).
Proof.
  exact (real_dpo_loss_pi_star_bounded_both bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one true false fa52_dpo_reward_spread).
Qed.

(* ---------- Main piece 2: closed-form reward reuse - witness specialization (beta := 1, Z := 1 factor out the log 1 correction term) ---------- *)
Theorem fa52_dpo_reward_recovery_concrete : forall s : bool,
  real_eq
    (real_dpo_reward_explicit bool real_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos
       (real_pi_star bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref real_one real_lt_zero_one)
       (real_pi_star_pos bool fa52_dpo_reward real_one real_lt_zero_one
          fa52_dpo_pi_ref fa52_dpo_pi_ref_pos real_one real_lt_zero_one)
       s)
    (real_plus (fa52_dpo_reward s)
                (real_opp (real_mult real_one
                            (real_log real_one real_lt_zero_one)))).
Proof.
  intro s.
  exact (real_dpo_reward_recovers_up_to_baseline bool fa52_dpo_reward real_one           real_lt_zero_one fa52_dpo_pi_ref fa52_dpo_pi_ref_pos           real_one real_lt_zero_one s).
Qed.

Print Assumptions fa52_dpo_bounded_both_concrete.
Print Assumptions fa52_dpo_reward_recovery_concrete.
