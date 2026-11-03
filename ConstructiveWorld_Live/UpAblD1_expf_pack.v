(* ========================================================================== *)
(*  UpAblD1_expf_pack.v - combinatorial instantiation of the uabd1x expf      *)
(*  six-slot mini-interface.                                                  *)
(* ========================================================================== *)
(*  Mission. Unpack the expf five-field sigT package real_expf_realizable    *)
(*  (AttnDoeblin) through its projections slot by slot, and export the        *)
(*  carrier function uabd1x_expf together with the five field-slot theorems  *)
(*  (pos / zero / plus / mono_lt / mono_le) with zero reproofs.              *)
(*  Dependencies. The in-file Require surface: S01_BaseRing through           *)
(*  S15_TailFEPUp, plus AttnDoeblin; no more Require.                        *)
(*  References. Realizability of the exponential five-field interface        *)
(*  (isomorphic to the library P1 precedent).                                *)
(*  Constructivity. The canonical Real carrier req-face instantiation comes  *)
(*  from the imported RealEnhancedReal field mapping; no new assumption      *)
(*  surface; end-of-file Print Assumptions for every statement.              *)
(*  Build. Rocq 9.1 direct call: rocq c -Q . "" -native-compiler no.         *)
(* ========================================================================== *)

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
Require Import AttnDoeblin.

(* ---- Slot 1 (expf : R -> R): the package signature projection is the     ---- *)
(* ---- inhabited form of the carrier-function slot                        ---- *)
Definition uabd1x_expf : Real -> Real := projT1 real_expf_realizable.

(* ---- One-shot decomposition of the package field bundle (five named      ---- *)
(* ---- fields, shared by the per-slot references below)                   ---- *)
Lemma uabd1x_pack_fields :
  And (forall x : Real, real_lt real_zero (uabd1x_expf x))
    (And (real_eq (uabd1x_expf real_zero) real_one)
    (And (forall a b : Real,
          real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)))
    (And (forall a b : Real, real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b))
         (forall a b : Real, real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b))))).
Proof.
  unfold uabd1x_expf.
  exact (projT2 real_expf_realizable).
Qed.

(* Note. And is the Set-face product (S01_BaseRing: And (A B : Set) := A*B,  *)
(*   i.e. Stdlib prod); its projections are fst/snd. proj1/proj2 are the     *)
(*   Prop-face and projections in this tree - the two faces must not be      *)
(*   mixed, so every slot reference goes through fst/snd.                    *)

(* ---- Slot 2 (expf_pos), verbatim-reference form ---- *)
Theorem uabd1x_expf_pos : forall x : Real, real_lt real_zero (uabd1x_expf x).
Proof. intros x. exact (fst uabd1x_pack_fields x). Qed.

(* ---- Slot 3 (expf_zero; the Id-face slot reads as the req form under the ---- *)
(* ---- canonical carrier's unit equality), verbatim-reference form        ---- *)
Theorem uabd1x_expf_zero : real_eq (uabd1x_expf real_zero) real_one.
Proof. exact (fst (snd uabd1x_pack_fields)). Qed.

(* ---- Slot 4 (expf_plus), verbatim-reference form ---- *)
Theorem uabd1x_expf_plus : forall a b : Real,
  real_eq (uabd1x_expf (real_plus a b)) (real_mult (uabd1x_expf a) (uabd1x_expf b)).
Proof. exact (fst (snd (snd uabd1x_pack_fields))). Qed.

(* ---- Slot 5 (expf_mono_lt), verbatim-reference form ---- *)
Theorem uabd1x_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (fst (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ---- Slot 6 (expf_mono_le; the Or branches are discharged branch by      ---- *)
(* ---- branch inside the package - inl -> cauchy_real_exp_mono /          ---- *)
(* ---- inr -> cauchy_real_exp_wd; this piece consumes the whole slot      ---- *)
Theorem uabd1x_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (snd (snd (snd (snd uabd1x_pack_fields)))). Qed.

(* ---- End-of-file audit print (per-statement Closed) ---- *)
Print Assumptions uabd1x_expf.
Print Assumptions uabd1x_pack_fields.
Print Assumptions uabd1x_expf_pos.
Print Assumptions uabd1x_expf_zero.
Print Assumptions uabd1x_expf_plus.
Print Assumptions uabd1x_expf_mono_lt.
Print Assumptions uabd1x_expf_mono_le.
