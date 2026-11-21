(* ConstructiveWorld-Set — Real-layer sum carrier slots, witness-passed form. *)

(** * UpAblT4_SumCarrier: finite-list sum carrier and partition-function
      positivity discharges.

    Mission.  [uabt4_sum_carrier4_realized] packs the finite-list fold
      [real_list_sum] as one [sigT] witness with three slot components:
      strict positivity of the sum under pointwise positivity on a
      nonempty enumeration, congruence under pointwise [real_eq], and
      linearity [sum (a * f) == a * (sum f)].  Three one-line bridges
      restate the in-tree fold lemmas ([uabt4_rsum_le], [uabt4_rsum_add],
      [uabt4_rsum_ext_brid]); three discharges feed the carrier witness
      into partition-function positivity ([uabt4_g02_partition_scaled_pos_realized],
      [uabt4_g02_gibbst_partition_pos_realized],
      [uabt4_s08_partition_pos_realized]).
    Dependencies.  Stdlib [Extraction], [Lists.List]; [S01_BaseRing]
      through [S15_TailFEPUp] and [G02_Debt] of this development.
    References.  The ConstructiveWorld-Main baseline module of the same
      name (statement names carried over verbatim); in-tree roots
      [real_list_sum] and [real_list_sum_pos/ext/linear/le/add]
      ([S08_RealMainlineDPO]); [real_partition_function_scaled_pos] and
      [gibbst_real_partition_function_temp_pos] ([G02_Debt]).
    Constructivity.  Set-carried throughout: [Real], [real_lt],
      [real_eq], [real_le] are Set-valued; [Not], [Id], [And] are the
      [S01] Set-layer definitions; the nonemptiness premise is the
      Set-level witness [Not (Id enum nil)], converted to the in-tree
      list-level form only inside proofs; no admission vocabulary; no
      classical axioms; statements extract with [Obj.magic] = 0.
    Build.  [coqc -native-compiler no -q -Q <development root> "" UpAblT4_SumCarrier.v]
      compiles cleanly (exit 0); artifact bytes [436f7121 000160bc]. *)

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
Require Import G02_Debt.
From Stdlib Require Import Extraction.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* ==== Carrier pack: positivity, congruence, linearity in one witness. ==== *)
(* The three components are the in-tree fold lemmas, passed through at      *)
(* fully applied faces; the nonempty-enumeration premise is converted       *)
(* from the Set-level witness [Not (Id enum nil)] to the in-tree            *)
(* list-level form inside the proof.                                        *)
Theorem uabt4_sum_carrier4_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    sigT (fun sumf : (X -> Real) -> Real =>
            And (forall f : X -> Real,
                   (forall w : X, real_lt real_zero (f w)) -> real_lt real_zero (sumf f))
                (And (forall f g : X -> Real,
                        (forall w : X, real_eq (f w) (g w)) -> real_eq (sumf f) (sumf g))
                     (forall (a : Real) (f : X -> Real),
                        real_eq (sumf (fun w => real_mult a (f w)))
                                (real_mult a (sumf f))))).
Proof.
  intros X enum Hne.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (existT _
                (fun f => real_list_sum X f enum)
                ((fun f Hf => real_list_sum_pos X f enum Hf Hne'),
                 ((fun f g Hpt => real_list_sum_ext X f g enum Hpt),
                  (fun a f => real_list_sum_linear X a f enum)))).
Defined.

(* ==== Monotone fold bridge. ==== *)
Theorem uabt4_rsum_le :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    (forall w : X, real_le (f w) (g w)) ->
    real_le (real_list_sum X f enum) (real_list_sum X g enum).
Proof. exact (fun X f g enum Hle => real_list_sum_le X f g enum Hle). Defined.

(* ==== Fold of a pointwise sum. ==== *)
Corollary uabt4_rsum_add :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    real_eq (real_list_sum X (fun w => real_plus (f w) (g w)) enum)
            (real_plus (real_list_sum X f enum) (real_list_sum X g enum)).
Proof. exact (fun X f g enum => real_list_sum_add X f g enum). Defined.

(* ==== Congruence bridge. ==== *)
Corollary uabt4_rsum_ext_brid :
  forall (X : Set) (f g : X -> Real) (enum : list X),
    (forall w : X, real_eq (f w) (g w)) ->
    real_eq (real_list_sum X f enum) (real_list_sum X g enum).
Proof. exact (fun X f g enum Hpt => real_list_sum_ext X f g enum Hpt). Defined.

(* ==== Discharge: scaled partition-function positivity. ==== *)
(* The carrier witness supplies the positivity premise of the in-tree       *)
(* theorem; the enumeration and carrier are fully applied.                  *)
Theorem uabt4_g02_partition_scaled_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (c : Real) (z : X -> Real),
      real_lt real_zero
        (real_partition_function_scaled X (fun f => real_list_sum X f enum) c z).
Proof.
  intros X enum Hne c z.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (real_partition_function_scaled_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') c z).
Defined.

(* ==== Discharge: temperature-form partition-function positivity. ==== *)
Theorem uabt4_g02_gibbst_partition_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (T : Real) (T_pos : real_lt real_zero T) (z_logits : X -> Real),
      real_lt real_zero
        (gibbst_real_partition_function_temp X (fun f => real_list_sum X f enum)
           T T_pos z_logits).
Proof.
  intros X enum Hne T T_pos z_logits.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (gibbst_real_partition_function_temp_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') T T_pos z_logits).
Defined.

(* ==== Discharge: attention partition-function positivity. ==== *)
Theorem uabt4_s08_partition_pos_realized :
  forall (X : Set) (enum : list X),
    Not (Id enum nil) ->
    forall (z : X -> Real),
      real_lt real_zero
        (real_partition_function X (fun f => real_list_sum X f enum) z).
Proof.
  intros X enum Hne z.
  assert (Hne' : enum <> nil).
  { intro Hc. assert (Hid : Id enum nil). { rewrite <- Hc. apply id_refl. } destruct (Hne Hid). }
  exact (real_partition_function_pos X (fun f => real_list_sum X f enum)
           (fun f Hf => real_list_sum_pos X f enum Hf Hne') z).
Defined.

(* ==== Assumption audit. ==== *)
Print Assumptions uabt4_sum_carrier4_realized.
Print Assumptions uabt4_rsum_le.
Print Assumptions uabt4_rsum_add.
Print Assumptions uabt4_rsum_ext_brid.
Print Assumptions uabt4_g02_partition_scaled_pos_realized.
Print Assumptions uabt4_g02_gibbst_partition_pos_realized.
Print Assumptions uabt4_s08_partition_pos_realized.

(* ==== Extraction probe. ==== *)
(* One single-command pass over all seven names: a multi-command driver     *)
(* would silently keep only the last command's output.  The delivery-face   *)
(* extraction runs through a Separate Extraction driver against the built   *)
(* artifact.                                                                *)
Set Extraction Output Directory "_log/extraction".
Recursive Extraction uabt4_sum_carrier4_realized
  uabt4_rsum_le uabt4_rsum_add uabt4_rsum_ext_brid
  uabt4_g02_partition_scaled_pos_realized
  uabt4_g02_gibbst_partition_pos_realized
  uabt4_s08_partition_pos_realized.
