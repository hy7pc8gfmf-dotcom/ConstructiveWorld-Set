(* ConstructiveWorld-Set — single-point instance record and supply theorem for the attention-Gibbs section interface. *)

(** * UpAblD1S17_UpReqAttnGibbs: the nineteen fields of the
      [UpReqAttnGibbs] section interface assembled into one single-point
      instance record with its supply theorem.

    Mission.  Constructive single-point witnesses for the thermal
      partition-sum positivity, the evicted-partition positivity and the
      exponential geometric decay premises, assembled into the record
      [uabd1s17_gib_pack18] with its supply theorem; the source module
      itself is not Required.

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpReqCauchy], [G07_KLWall] of this development; interface = the
      argument-less Class [RealInterfaceEnhancedSetoid] (module
      [RealInterfaceEnhancedMod]).

    References.  This development, UpAblD1S17_UpReqAttnGibbs.v, the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier
      completion).  Adaptation = binder-shell removal + notation
      rebinding + supply-face convergence on this development's own
      precedent (the source argumented Class applications raised
      "Illegal application (Non-functional construction)"): the binder
      pair [(R : Set)] [(RIS : RealInterfaceEnhancedSetoid R)] is
      removed, [R := Real] by notation (UpReqSumD.v L58), law fields
      resolve as bare names through the global instance
      [RealEnhancedReal] (UpReqSumD.v L68-72), the predicate faces are
      [real_eq]/[real_lt]/[real_le] (UpReqSumD.v L113-114), and
      [uabd1s17_gib_geobreak] carries the same global constants as the
      consumed supply theorem [klcx_exp_neg_geo_break_iface]
      ([G07_KLWall]).

    Constructivity.  All Set-layer statements; every station closed by
      [Qed], zero admitted items; no classical logic; the [keep_dec]
      premise carries the explicit witness [inl tt] at the Set-carried
      [Or]/[Not] face ([S01_BaseRing]); tail [Print Assumptions] report
      the closure face.

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblD1S17_UpReqAttnGibbs.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqCauchy.
Require Import G07_KLWall.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v L58 precedent). *)
Notation R := Real.

(* ============ canonical carrier instance, named ============ *)

Definition uabd1s17_ren : RealInterfaceEnhancedSetoid :=
  RealEnhancedReal.

(* ============ interface packaging record: the in-section declarations of
   the source module Section ReqAttnGibbs ============ *)
(* Field order = source declaration order; sum_pos,
   req_lt_plus_compat_lt_le_h and detailed_balance_r are not part of this
   record (their supply is carried by the dedicated pieces). *)
(* Z_thermo_r / evicted_partition_r are in-section Definitions of the source
   module; the corresponding record slots expand their bodies verbatim after
   delta reduction (interchangeable with the source definitions). *)

(* The type slots (S) of the source record are monomorphised to the supplied
   unit instance, and the keep slot is monomorphised with it (single-point
   kept-everything instance: keep s reduces to unit): type slots and the
   keep-dependent keep_dec type are erased/cast at extraction and would
   raise Obj.magic at slot values; the record's slot values below are
   carried by that single instance. *)

Inductive uabd1s17_gib_pack18 : Type :=
| uabd1s17_gib_pack18_intro :
    forall (sumf : (unit -> R) -> R)
           (sum_ext : forall f g : unit -> R,
                      (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
           (sum_linear : forall (a : R) (f : unit -> R),
                         real_eq (sumf (fun s : unit => mult a (f s))) (mult a (sumf f)))
           (sum_add : forall f g : unit -> R,
                      real_eq (sumf (fun s : unit => plus (f s) (g s)))
                          (plus (sumf f) (sumf g)))
           (T : R) (T_pos : real_lt zero T)
           (D : R) (D_pos : real_lt zero D) (energy : unit -> R)
           (Z_thermo_r_pos :
              real_lt zero (sumf (fun s : unit =>
                        exp_neg (mult (inv_pos D D_pos) (energy s)))))
           (transition : unit -> unit -> R)
           (keep_dec : forall s : unit, Or unit (Not unit))
           (sum_le : forall f g : unit -> R,
                     (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g))
           (abs_sum_le_r : forall f : unit -> R,
                           real_le (abs (sumf f)) (sumf (fun s : unit => abs (f s))))
           (evicted_partition_r_pos :
              real_lt zero (sumf (fun s : unit =>
                        if keep_dec s
                        then exp_neg (mult (inv_pos D D_pos) (energy s))
                        else zero)))
           (exp_neg_geo_break :
              forall d : R, real_lt real_zero d ->
                forall eps : R, real_lt real_zero eps ->
                  sigT (fun N : nat =>
                    real_le (real_exp_neg (real_mult (klcx_r_pow (real_plus real_one real_one) N) d)) eps)),
      uabd1s17_gib_pack18.

(* ============ supply of exp_neg_geo_break (transitive citation of the
   library theorem) ============ *)
(* The global-face constants of the slot statement are exactly the constant
   names of the consumed supply theorem klcx_exp_neg_geo_break_iface
   (G07_KLWall); the slot's req_r_pow position of the source is carried by
   klcx_r_pow, the supply's own name. *)

Theorem uabd1s17_gib_geobreak :
  forall d : Real, real_lt real_zero d ->
    forall eps : Real, real_lt real_zero eps ->
      sigT (fun N : nat =>
        real_le (real_exp_neg (real_mult (klcx_r_pow (real_plus real_one real_one) N) d)) eps).
Proof.
  intros d Hd eps Heps.
  exact (klcx_exp_neg_geo_break_iface d eps Hd Heps).
Qed.

(* ============ supply theorem: all record slots given by a single-point
   instance ============ *)

Theorem uabd1s17_gib_pack18_supplied : uabd1s17_gib_pack18.
Proof.
  exact (uabd1s17_gib_pack18_intro
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (a : Real) (f : unit -> Real) =>
              req_refl (mult a (f tt)))
           (fun (f g : unit -> Real) =>
              req_refl (plus (f tt) (g tt)))
           one one_pos
           one one_pos
           (fun _ : unit => zero)
           (exp_neg_pos
              (mult (inv_pos one one_pos) zero))
           (fun (_ _ : unit) => zero)
           (fun _ : unit => @inl unit (Not unit) tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun f : unit -> Real =>
              le_refl (abs (f tt)))
           (exp_neg_pos
              (mult (inv_pos one one_pos) zero))
           uabd1s17_gib_geobreak).
Qed.

(* ============ assumption audit ============ *)

Print Assumptions uabd1s17_gib_geobreak.
Print Assumptions uabd1s17_gib_pack18_supplied.
