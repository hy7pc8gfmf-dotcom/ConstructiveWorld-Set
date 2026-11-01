(* ============================================================ *)
(* UpAblD1S8_UpReqTempDefs.v -- data-supply pack of Section     *)
(*   RealTempDefs of UpReqTempDefs (module FA-D1S8, census      *)
(*   batch D1-7, per-module aggregate of nine slots).           *)
(* Mission . One inductive record uabd1s8_tpd_pack9 carries the *)
(*   nine definition faces of Section RealTempDefs: a summation *)
(*   carrier over a finite type S with positivity, extension-   *)
(*   ality, linearity and additivity, plus temperature T, its   *)
(*   positivity T_pos and an energy function; the point         *)
(*   instance S := unit realizes all nine faces at once.        *)
(* Dependencies . Stdlib List; the tree-registered face         *)
(*   S01_BaseRing through S15_TailFEPUp, carried verbatim       *)
(*   (read-only; zero Require-face additions).                  *)
(* References . UpReqTempDefs.v, Section RealTempDefs: the nine *)
(*   slots transcribed verbatim; single-point pack skeleton of  *)
(*   the same family (eut_pack9 shape, prefix adapted).         *)
(* Constructivity . The only theorem is a single explicit       *)
(*   witness term: positivity and extensionality faces          *)
(*   discharge by direct projection (H tt), linearity and       *)
(*   additivity by reflexivity at the Real level; the closing   *)
(*   Print Assumptions attests closure under the global         *)
(*   context. The point type S is hoisted to the inductive's    *)
(*   leading type argument so extraction keeps it as an OCaml   *)
(*   type argument instead of erasing it, which keeps the       *)
(*   witness terms cast-free.                                   *)
(* Build . rocq c -native-compiler no -q -Q <world dir> ""      *)
(*   UpAblD1S8_UpReqTempDefs.v                                  *)
(* ============================================================ *)

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

(* ---- Pack record: the nine statement faces, carried verbatim ---- *)

Inductive uabd1s8_tpd_pack9 (S : Type) : Type :=
| uabd1s8_tpd_pack9_intro :
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
            uabd1s8_tpd_pack9 S.

(* ---- Point instance: one witness term discharges all nine faces ---- *)

Theorem uabd1s8_tpd_pack9_supplied : uabd1s8_tpd_pack9 unit.
Proof.
  exact (uabd1s8_tpd_pack9_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_lt real_zero (f s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* ---- Closure check ---- *)

Print Assumptions uabd1s8_tpd_pack9_supplied.
