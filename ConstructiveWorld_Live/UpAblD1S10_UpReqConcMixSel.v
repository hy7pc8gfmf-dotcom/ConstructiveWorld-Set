(* ==========================================================================
   UpAblD1S10_UpReqConcMixSel.v - the CmkMixSelect / CmkRPowBridge
   interface slots and the CmkMixTime remainder family, discharged as a
   one-point instance package.
   Mission. 使命: two named instance declarations (the mix-select and
     r-pow-bridge interface slots, supplied by the world's canonical
     instance), one record-type package uabd1s10_cmk_pack17 restating the
     seventeen CmkMixTime remainder slots in declaration order, one
     enumeration-nonemptiness certificate, and one discharge theorem
     assembling the one-point witness (S := unit, sumf := fun f => f tt,
     temp := Delta := one, z := the zero function).
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp of the -Set lineage
     world; the interface is the argument-less Class
     RealInterfaceEnhancedSetoid; notation rebind Notation R := Real;
     predicate faces converged to real_eq / real_le / real_lt - the
     constant names the world's own statements carry.
   References. 对标: the concentration mix-select requirement family
     (single-point sum instance at the world's discharged signatures).
     Statement names carried over verbatim; adaptation = binder-pair
     removal + notation rebinding + predicate-face convergence + bare
     field consumption through the global instance.
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; zero new machinery (each supply arm
     is a one-step direct match, a definitional collapse, or a field
     consumption); the tail Print Assumptions probes report the closure
     face; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> ""
     UpAblD1S10_UpReqConcMixSel.v (cpu_guard thermal wrapper,
     ulimit -s 65532).
   ========================================================================== *)

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
Import RealInterfaceEnhancedMod.
Import ListNotations.
Notation R := Real.

(* ============ interface slots: named instance declarations ============ *)

Definition uabd1s10_cmk_mixselect_RIS : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

Definition uabd1s10_cmk_rpowbridge_RIS : RealInterfaceEnhancedSetoid :=
  RealInterfaceEnhancedMod.RealEnhancedReal.

(* ============ package record (the CmkMixTime remainder slots), in the
   source declaration order: ext / linear / add / le / abs_sum_le_h /
   enum / enum_nonempty / temp / temp_pos / Delta / Delta_pos / z / z_lb /
   z_ub; the bs_swap / bs_abs / bs_lpc / sum_eq_list slots are carried by
   their own pieces and are not restated here. The space slot is
   monomorphised to the one-point space unit (the instance the discharge
   theorem supplies; the D1S17 record-form precedent narrows the abstract
   Set slot the same way so the extracted payload stays real data), and
   the nonemptiness face rides the Set-level equality Id - the same face
   the world's own enumeration slots carry. ============ *)

Inductive uabd1s10_cmk_pack17 : Type :=
| uabd1s10_cmk_pack17_intro :
    forall (sumf : (unit -> R) -> R),
      (forall f g : unit -> R,
          (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
      (forall (a : R) (f : unit -> R),
          real_eq (sumf (fun s : unit => mult a (f s))) (mult a (sumf f))) ->
      (forall f g : unit -> R,
          real_eq (sumf (fun s : unit => plus (f s) (g s)))
              (plus (sumf f) (sumf g))) ->
      (forall f g : unit -> R,
          (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
      (forall f : unit -> R,
          real_le (abs (sumf f)) (sumf (fun s : unit => abs (f s)))) ->
      forall (enum : list unit),
        Not (Id enum nil) ->
        forall (temp : R),
          real_lt zero temp ->
          forall (Delta : R),
            real_lt zero Delta ->
            forall (z : unit -> unit -> R),
              (forall s s' : unit, real_le (opp Delta) (z s s')) ->
              (forall s s' : unit, real_le (z s s') Delta) ->
              uabd1s10_cmk_pack17.

(* ---- enumeration nonemptiness arm (independent certificate) ---- *)

Lemma uabd1s10_cmk_enum_ne : Not (Id (tt :: nil) nil).
Proof. intro H. inversion H. Qed.

(* ============ discharge: the one-point witness, assembled once ============ *)

Theorem uabd1s10_cmk_pack17_supplied : uabd1s10_cmk_pack17.
Proof.
  exact (uabd1s10_cmk_pack17_intro
           (fun f : unit -> R => f tt)
           (fun (f g : unit -> R)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (a : R) (f : unit -> R) =>
              req_refl (mult a (f tt)))
           (fun f g : unit -> R => req_refl (plus (f tt) (g tt)))
           (fun (f g : unit -> R)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun f : unit -> R =>
              le_refl (abs (f tt)))
           (tt :: nil)
           uabd1s10_cmk_enum_ne
           one
           one_pos
           one
           one_pos
           (fun _ _ : unit => zero)
           (fun (_ _ : unit) => inl (real_lt_zero_opp one real_lt_zero_one))
           (fun (_ _ : unit) => inl real_lt_zero_one)).
Qed.

(* ============ closure face ============ *)

Print Assumptions uabd1s10_cmk_pack17_supplied.
Print Assumptions uabd1s10_cmk_mixselect_RIS.
Print Assumptions uabd1s10_cmk_rpowbridge_RIS.
