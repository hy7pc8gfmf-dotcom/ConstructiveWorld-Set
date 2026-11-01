(* ==========================================================================
   UpAblT6_UpReqAlign2.v - assumption-ablation batch T6 a (T3a handover, 4 of
   <=25 same-root residue stations).
   Cure note.
     Cure-seat copy of the seat_nw10 red piece. The former binders
     forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} were a Main-tree
     section face (ConstructiveWorld-Main S07 L7945, parameterized Class)
     transplanted verbatim into the nw10 (-Set lineage) world, where
     RealInterfaceEnhancedSetoid is the zero-parameter Class (S07
     L8075, fields carried by the global Real) -> "Illegal application
     (Non-functional construction) ... of type Type". Fix = pure binder
     removal + notation rebinding on the world's own precedent; no Obj.magic,
     no Prop-cast shim, no Prop-ification.
   Mission.
     Materialize the four interface-face ablation theorems of the Req2AlignCore sumf face (UpReqAlign2.v L66-79): on the concrete finite-sum instance sumf := sumd_sumf S enum the four assumption slots (sum_ext / sum_add / sum_linear / sum_pos) hold unconditionally - premises thin down to the pure data slot (the enumeration list).
   Dependencies.
     nw10 world (-Set lineage, compiled read-only against /tmp/nw10world); UpReqSumD (sumd_sumf + sumd_in_to_In, sumd_list_sum_add, sumd_list_sum_ext, sumd_list_sum_le, sumd_list_sum_linear, sumd_list_sum_nonneg, sumd_list_sum_opp, sumd_list_sum_pos, sumd_list_sum_pos_cons, sumd_list_sum_swap, sumd_list_sum_zero, sumd_list_sum_zero_nonneg_head, sumd_list_sum_zero_nonneg_in, sumd_list_sum_zero_nonneg_tail, sumd_lt_le, sumd_sum_add, sumd_sum_const, sumd_sum_eq_list, sumd_sum_ext, sumd_sum_le, sumd_sum_linear, sumd_sum_opp, sumd_sum_pos, sumd_sum_swap, sumd_sum_zero_nonneg_in, sumd_sum_zero_nonneg_surj, sumd_sumf_const); S01_BaseRing..S15 chain + UpReqSumD + Stdlib List; all read-only use, origin trees untouched.
   References.
     Statement face aligned to the world's unparameterized interface class per S10_KVQuantTrig.v L12417-12419 precedent (the parameterized section-binder form is an alien-piece misplant -> Notation passthrough of the global form): the class binders are dropped; R is bound to the global Real carrier by notation (UpReqSumD.v L58 precedent); predicates follow the dependency face real_eq / real_lt (UpReqSumD.v L113-114 / L304-305); zero / plus / mult stay as bare names projected through the global instance (UpReqSumD.v L68-72 style). A1 sum_ext <- UpReqAlign2.v L71 (sumd_sum_ext); A2 sum_add <- L73 (sumd_sum_add); A3 sum_linear <- L76 (sumd_sum_linear); A4 sum_pos <- L79 (sumd_sum_pos; nonemptiness slot explicit premise Not (enum = nil), same shape as UpReqSumD; the original assumption slot had no such argument). Grading N1 x4: in-register direct discharge, no padding; no zero_nonneg face, no W face in this jurisdiction.
   Constructivity.
     Statement face all Set-layer (real_eq / real_lt are the Set-valued interface predicates resolved through the global instance of the unparameterized class, as in UpReqSumD); zero new axioms; every station Qed-closed + tail Print Assumptions; the one bare equality Not (enum = nil) is a premise-slot lawful keep (red-line 2).
   Build.
     rocq c -native-compiler no -q -Q /tmp/nw10world "" (-Set lineage world; cpu_guard thermal wrapper, ulimit -s 65532). Build only against a -Set lineage world: world_main carries the parameterized Class and is not this piece's world.
   ========================================================================== *)

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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: this world's RealInterfaceEnhancedSetoid is the
   zero-parameter Class, its fields resolve through the global instance
   (UpReqSumD.v L58 precedent; S10_KVQuantTrig.v L12417-12419 ruling). *)
Notation R := Real.

(* ============ Req2AlignCore (UpReqAlign2.v L66-79) ============ *)
(* Original section Context {R}{RIS} + S + sumf; the section binders are
   externalized on the world's unparameterized interface: R := Real by
   notation, no class-instance binder; sumf replaced by the sumd_sumf S enum
   instance; Import RealInterfaceEnhancedMod kept. *)

(* A1 <- L71 sum_ext (UpReqAlign2.v original face: forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)) *)
Theorem uabT6_req2align_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* A2 <- L73 sum_add (UpReqAlign2.v original face: forall f g : S -> R, req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g))) *)
Theorem uabT6_req2align_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* A3 <- L76 sum_linear (UpReqAlign2.v original face: forall (a : R) (f : S -> R), req (sumf (fun s => mult a (f s))) (mult a (sumf f))) *)
Theorem uabT6_req2align_sum_linear :
  forall (S : Set) (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s => mult a (f s)))
        (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* A4 <- L79 sum_pos (nonemptiness data slot explicit premise, sumd_sum_pos same shape; UpReqAlign2.v original face: forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f)) *)
Theorem uabT6_req2align_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ PA closing (Closed verdict per station) ============ *)
Print Assumptions uabT6_req2align_sum_ext.
Print Assumptions uabT6_req2align_sum_add.
Print Assumptions uabT6_req2align_sum_linear.
Print Assumptions uabT6_req2align_sum_pos.
