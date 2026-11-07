(* ConstructiveWorld-Set — four-slot re-feed, zero new mathematics. *)
(** * LowRefFeed4: three forwarder theorems; one inventoried slot open.
    Mission.  Three forwarder theorems [lf4_lt_plus_compat_lt_le_h],
      [lf4_inv_pos_lt_contra], and [lf4_sum_swap_i], each discharging an
      inventoried interface-slot statement by one [exact] step from an
      in-register supply lemma; a fourth inventoried slot (the setoid-face
      strict-order extension) is disclosed as not discharged: the two worlds
      carry no bridging instance, so the slot stays honestly open.
    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqAlgebra], [UpReqSumD], [fa53_compat_abs]
      ([fa53_lt_plus_compat_lt_le_dec], [fa53_abs_ge_zero_id_dec]),
      [InvPosLtCompat] ([ipl_upfirewall_102_shape]) of this development;
      both the S01 interface face ([RealInterfaceEnhanced],
      [DecidableOrder]) and the argument-less [Class]
      [RealInterfaceEnhancedSetoid] (module [RealInterfaceEnhancedMod]).
    References.  This development and the ConstructiveWorld-Main baseline
      module of the same name: the [lt_plus_compat_lt_le_h] slot (strict-plus
      compatibility with one weak side), the [inv_pos_lt_contra] slot
      (strict-inverse antitonicity), the [sum_swap_i] slot (double-sum
      exchange at the enumerated finite-sum instance); statement names
      verbatim; adaptation = argument-less-face rebinding: [R := Real] by
      notation, predicate faces [real_eq]/[real_lt] on the setoid face,
      [sumd_sumf]/[sumd_list_sum_swap] at the argument-less export face.
    Constructivity.  All statements live on the [Set] layer; every station
      closes with [Qed], zero admitted items; pure term mode ([exact]
      supplies, zero rewrite tactics); assumption slots inherited from the
      supplies; no new axioms.
    Build.  [rocq c -native-compiler no -q -Q ConstructiveWorld_Live ""
      LowRefFeed4.v] compiles cleanly (exit 0) under the [cpu_guard]
      thermal wrapper with [ulimit -s 65532]. *)

Require Import fa53_compat_abs.
Require Import InvPosLtCompat.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* ============ S01 interface face: slots 2 / 4 ============ *)

Section LF4RIFace.

Context {RI : RealInterfaceEnhanced}.
Context {DO : DecidableOrder RI}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let plus := @S01_BaseRing.plus RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.
Let lt := @S01_BaseRing.lt RI.
Let le := @S01_BaseRing.le RI.

(* ---- slot 2: forwarder of lt_plus_compat_lt_le_h ---- *)
Theorem lf4_lt_plus_compat_lt_le_h :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO).
Qed.

(* ---- slot 4: forwarder of inv_pos_lt_contra ---- *)
Theorem lf4_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  exact (@ipl_upfirewall_102_shape RI).
Qed.

End LF4RIFace.

(* ============ setoid face: slot 3 (the argument-less Class world) ==== *)

Section LF4SumSwap.

Variable S : Set.
Variable enum : list S.

(* ---- slot 3: forwarder of sum_swap_i at the concrete enumerated-key
   carrier ---- *)
Theorem lf4_sum_swap_i :
  forall f : S -> S -> R,
    real_eq (@sumd_sumf S enum
           (fun s : S => @sumd_sumf S enum (fun s' : S => f s s')))
        (@sumd_sumf S enum
           (fun s' : S => @sumd_sumf S enum (fun s : S => f s s'))).
Proof.
  intro f.
  exact (@sumd_list_sum_swap S f enum enum).
Qed.

End LF4SumSwap.

(* ============ assumption audit ============ *)

Print Assumptions lf4_lt_plus_compat_lt_le_h.
Print Assumptions lf4_inv_pos_lt_contra.
Print Assumptions lf4_sum_swap_i.
