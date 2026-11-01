(* UpAblD1S4_UpReqTopKTVChain.v -- data-supply pack, RealTopKTV chain.      *)
(*                                                                          *)
(* Mission. Carry verbatim the statement face of a finite-carrier partition *)
(*   chain over the Cauchy Real layer as two S-parameterized record-style   *)
(*   inductive bundles (real_sum_over_S a pointwise summation functor):     *)
(*   extensionality up to pointwise real_eq; additivity over real_plus;     *)
(*   monotonicity over pointwise real_le (pack 1) or homogeneity            *)
(*   real_eq (real_sum_over_S (fun s => real_mult a (f s)))                 *)
(*   (real_mult a (real_sum_over_S f)) (pack 2); a temperature D with       *)
(*   real_lt real_zero D; an energy function; and positivity of the         *)
(*   Boltzmann partition function (the sum of exp_neg (real_mult            *)
(*   (real_inv_pos D D_pos) (energy s))); one supply theorem per bundle     *)
(*   instantiates every component on the single-point carrier.              *)
(* Dependencies. Stdlib List; the declared Require face S01_BaseRing        *)
(*   through S15_TailFEPUp, all in-tree; the proof terms consume S02        *)
(*   real_eq/real_le/real_lt/real_zero/real_one, S03 real_inv_pos, S07      *)
(*   real_lt_zero_one/real_exp_neg/real_exp_neg_pos.                        *)
(* References. The canonical ensemble of finite-temperature statistical     *)
(*   mechanics: the partition function Z = sum_s exp(-energy(s)/D) is       *)
(*   strictly positive whenever D is, since exp_neg is everywhere positive; *)
(*   the interface mirrors the standard finite-sum package.                 *)
(* Constructivity. All statements ride Set-level exit faces (real_eq/       *)
(*   real_le/real_lt); no classical reasoning. The instance is S := unit,   *)
(*   sum (fun f => f tt), D := real_one, zero energy: extensionality and    *)
(*   monotonicity reduce to evaluation at tt; additivity and homogeneity    *)
(*   close by real_eq_refl; the Z component is real_exp_neg_pos at          *)
(*   exp(-(1 * 0)); both theorems are explicit terms ending in Qed and      *)
(*   Print Assumptions reports Closed under the global context.             *)
(* Build. rocq c -native-compiler no -q -Q . "" UpAblD1S4_UpReqTopKTVChain.v*)
(*   (every compile wrapped by the thermal-guard protocol of the CI).       *)

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

(* ============ Pack 1 (record-style): statement face of section one ============ *)
(* The Z component inlines the Boltzmann factor                            *)
(*   exp_neg (real_mult (real_inv_pos D D_pos) (energy s)) and its sum     *)
(*   real_sum_over_S of that factor as one statement, as in pack 2 below.  *)
Inductive uabd1s4_rtk1_pack9 (S : Type) : Type :=
| uabd1s4_rtk1_pack9_intro :
      forall real_sum_over_S : (S -> Real) -> Real,
        (forall (f g : S -> Real),
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (f g : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        (forall (f g : S -> Real),
            (forall s : S, real_le (f s) (g s)) ->
            real_le (real_sum_over_S f) (real_sum_over_S g)) ->
        forall D : Real,
          forall D_pos : real_lt real_zero D,
          forall energy : S -> Real,
            real_lt real_zero
              (real_sum_over_S
                 (fun s : S =>
                    real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))) ->
            uabd1s4_rtk1_pack9 S.

(* ============ Pack 2 (record-style): statement face of section two ============ *)
(* The Z component has the same inline form as in pack 1 (the sum of the   *)
(*   Boltzmann factor above); the homogeneity component -- sum of a * f    *)
(*   equals a * sum f -- is unique to pack 2.                              *)

Inductive uabd1s4_rtk2_pack9 (S : Type) : Type :=
| uabd1s4_rtk2_pack9_intro :
      forall real_sum_over_S : (S -> Real) -> Real,
        (forall (f g : S -> Real),
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (f g : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        forall D : Real,
          forall D_pos : real_lt real_zero D,
          forall energy : S -> Real,
            real_lt real_zero
              (real_sum_over_S
                 (fun s : S =>
                    real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))) ->
            uabd1s4_rtk2_pack9 S.

(* ============ Supply theorems: one single-point instance for both packs ============ *)

Theorem uabd1s4_rtk1_pack9_supplied : uabd1s4_rtk1_pack9 unit.
Proof.
  exact (uabd1s4_rtk1_pack9_intro unit
           (fun (f : unit -> Real) => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           real_one real_lt_zero_one
           (fun _ : unit => real_zero)
           (real_exp_neg_pos
              (real_mult (real_inv_pos real_one real_lt_zero_one) real_zero))).
Qed.

Theorem uabd1s4_rtk2_pack9_supplied : uabd1s4_rtk2_pack9 unit.
Proof.
  exact (uabd1s4_rtk2_pack9_intro unit
           (fun (f : unit -> Real) => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))
           real_one real_lt_zero_one
           (fun _ : unit => real_zero)
           (real_exp_neg_pos
              (real_mult (real_inv_pos real_one real_lt_zero_one) real_zero))).
Qed.

(* ============ Assumption audit ============ *)

Print Assumptions uabd1s4_rtk1_pack9_supplied.
Print Assumptions uabd1s4_rtk2_pack9_supplied.
