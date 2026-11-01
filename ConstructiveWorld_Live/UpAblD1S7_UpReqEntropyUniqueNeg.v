(* UpAblD1S7_UpReqEntropyUniqueNeg.v -- data-supply pack, entropy           *)
(* unique-negation section.                                                 *)
(* Mission. Carry verbatim the statement face of the RealEntropyUniqueNeg   *)
(*   section (nine slots, source lines 177-192: S, real_sum_over_S,         *)
(*   real_sum_pos_preserved, real_sum_over_S_ext, real_sum_over_S_linear,   *)
(*   real_sum_over_S_add, T, T_pos, energy) as one carrier-parameterized    *)
(*   record-style inductive bundle (real_sum_over_S a pointwise summation   *)
(*   functor): positivity of  *)
(*   the sum under pointwise positivity; extensionality up to pointwise     *)
(*   real_eq; homogeneity over real_mult; additivity over real_plus; a      *)
(*   temperature T with real_lt real_zero T; an energy function. One supply *)
(*   theorem instantiates every component on the single-point carrier:      *)
(*   S := unit, sum := fun f => f tt, T := real_one, zero energy. Positivity*)
(*   and extensionality reduce to evaluation at tt (H tt); homogeneity and  *)
(*   additivity close by real_eq_refl; T_pos is real_lt_zero_one at         *)
(*   T = real_one, in one line.                                             *)
(* Dependencies. Stdlib List; the declared Require face S01_BaseRing        *)
(*   through S15_TailFEPUp, all in-tree (the proof term consumes S02        *)
(*   real_eq/real_lt/real_zero/real_one/real_plus/real_mult/real_eq_refl    *)
(*   and S07 real_lt_zero_one); zero Require of any source file, so no      *)
(*   cross-generation vo hazard.                                            *)
(* References. The read-only source section RealEntropyUniqueNeg (the       *)
(*   entropy unique-negation interface); the record-type data-supply pack   *)
(*   interface (slot statements carried verbatim into the bundle).          *)
(* Constructivity. Set-layer statements (real_eq/real_lt exit faces); zero  *)
(*   assumption slots; the single theorem is an explicit term ending in     *)
(*   Qed; the tail Print Assumptions reports Closed under the global        *)
(*   context; no classical reasoning anywhere.                              *)
(* Build. rocq c -native-compiler no -q -Q . "" (every compile wrapped by   *)
(*   the thermal-guard protocol of the CI).                                 *)

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

(* ============ Pack record form: the 9-slot statement face carried verbatim (source file lines 177-192) ============ *)

Inductive uabd1s7_eun_pack9 (S : Type) : Type :=
| uabd1s7_eun_pack9_intro :
      forall real_sum_over_S : (S -> Real) -> Real,
        (forall (f : S -> Real),
            (forall s : S, real_lt real_zero (f s)) ->
            real_lt real_zero (real_sum_over_S f)) ->
        (forall (f g : S -> Real),
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        (forall (f g : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        forall T : Real,
          forall T_pos : real_lt real_zero T,
          forall energy : S -> Real,
            uabd1s7_eun_pack9 S.

(* ============ Supply theorem: one single-point instance feeds all 9 slots ============ *)

Theorem uabd1s7_eun_pack9_supplied : uabd1s7_eun_pack9 unit.
Proof.
  exact (uabd1s7_eun_pack9_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_lt real_zero (f s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* ============ Assumption audit ============ *)

Print Assumptions uabd1s7_eun_pack9_supplied.
