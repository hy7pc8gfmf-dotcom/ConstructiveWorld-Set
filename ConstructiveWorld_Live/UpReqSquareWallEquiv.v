(* ==========================================================================
   UpReqSquareWallEquiv.v - fourth-wall theorematization (the "B-form
   lifter" gap of the square-nonneg plain wall, closed).
   Mission.
     snw_square_wall_lpo: the two-way reduction four-slot account among
     the plain wall, the B-form lifter and the restricted LPO; plus the
     wall iff lifter isomorphism account, the twin definitional wall
     bridges, and the interface slot resolution station.
   Dependencies.
     CW_ConstructiveWorld_219; UpReqLpoEquiv (SqWall, rLPO, lpn_forward,
     lpn_backward); UpRealLeB (real_le_b, real_square_nonneg_B); S01-S15
     chain per Require face; Stdlib Extraction; Import
     RealInterfaceEnhancedMod.
   References.
     G09_MiscSmall.v:328/:357: the plain wall constructively unprovable
     (a zero-separation decision), Cauchy and Real layer alike; the B
     side reachable (UpRealLeB real_square_nonneg_B, universally
     provable), the Or side the wall (CW219 L3521); the one-way bridge
     is Or implies B only; lineage AA15 -> AA22 -> AA23.
   Constructivity.
     Zero axioms, zero assumption load; statement face all Set with the
     custom And/Or, zero Prop leakage; classical logic free. The
     interface slot station is stated at the canonical raw face real_le
     real_zero (real_mult t t), the instance-delta expansion of the
     RealEnhancedReal slot fields; the projection spelling is
     ML-extraction-inexpressible (extractor casts, probe-located), so it
     stays off the extraction face per the SqWallCorrMark precedent.
   Build.
     Rocq 9.1 rocq c -Q . "" -native-compiler no, cpu_guard wrapped.
   ========================================================================== *)
From Stdlib Require Import Extraction.
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
Require Import UpReqLpoEquiv.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 1. The two statement faces (all Set, zero Prop)          *)
(* ============================================================ *)

(* The plain wall: the universal square-nonneg face (Or-encoded exact
   order; definitionally same-faced as the UpReqLpoEquiv SqWall
   (UpReqLpoEquiv:224), independently stated here with twin bridges -
   the wall body of the fourth wall) *)
Definition snw_wall : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

(* The B-form lifter: for every t, lifts the Bishop margin certificate
   to an exact Or order branch. The B-side certificate is universally
   free (real_square_nonneg_B on file), the Or side is not supplyable -
   this form is the visible shape of the B-reachable / Or-unprovable
   gap. *)
Definition snw_b_lift : Set :=
  forall t : Real,
    real_le_b real_zero (real_mult t t) ->
    real_le real_zero (real_mult t t).

(* Twin bridges: the plain wall and SqWall (UpReqLpoEquiv:224) are
   definitionally same-faced *)
Theorem snw_wall_sq_wall : snw_wall -> SqWall.
Proof.
  exact (fun H => H).
Qed.

Theorem snw_sq_wall_wall : SqWall -> snw_wall.
Proof.
  exact (fun H => H).
Qed.

(* ============================================================ *)
(* Part 2. Forward: the lifter implies the restricted LPO (gap   *)
(*   thickness = decider).                                       *)
(*   Proof shape: a three-piece composite - the on-file universal *)
(*   B certificate (real_square_nonneg_B) composed with the      *)
(*   lifter gives the plain wall, then lpn_forward (the AA15     *)
(*   forward branch) gives the rLPO.                             *)
(*   Non-trivial account: the B side is free and the lifter      *)
(*   supplies exactly the remaining gap, so the lifter's supply  *)
(*   power is equivalent to a pointwise sign decider for the     *)
(*   reals - the gap-thickness measure theorem.                  *)
(* ============================================================ *)

Theorem snw_b_lift_to_rlpo : snw_b_lift -> rLPO.
Proof.
  intros Hlift.
  apply lpn_forward.
  intros t.
  apply Hlift.
  apply real_square_nonneg_B.
Qed.

(* ============================================================ *)
(* Part 3. Reverse: the restricted LPO implies the lifter (the   *)
(*   reachability theorem, the key new fact of this piece).      *)
(*   Proof shape: the rLPO (via the AA15 reverse branch          *)
(*   lpn_backward) gives the exact Or branch pointwise; the      *)
(*   lifter's B certificate argument is wholly redundant -       *)
(*   dropped. Machine expression of "the lifter is the decider   *)
(*   under another signature": the gap is not an independent     *)
(*   obstacle, only another signature of the decider.            *)
(*   Contrast AA23: a pinned wall hitting the reverse obstacle   *)
(*   must downgrade; this wall is reverse reachable - the        *)
(*   structural divide between the two wall kinds (the interface *)
(*   unsatisfiable kind versus the encoding margin kind) shows   *)
(*   here.                                                       *)
(* ============================================================ *)

Theorem snw_rlpo_to_b_lift : rLPO -> snw_b_lift.
Proof.
  intros Hdec t _HB.
  exact (lpn_backward Hdec t).
Qed.

(* ============================================================ *)
(* Part 4. The main closure: the four-slot account (the wall,    *)
(*   the lifter and the rLPO in one equivalence cycle)           *)
(* ============================================================ *)

Definition snw_square_wall_lpo :
  And (snw_wall -> rLPO)
      (And (rLPO -> snw_wall)
           (And (snw_b_lift -> rLPO) (rLPO -> snw_b_lift))) :=
  ((fun H => lpn_forward (snw_wall_sq_wall H)),
   ((fun H => snw_sq_wall_wall (lpn_backward H)),
    ((fun H => snw_b_lift_to_rlpo H),
     (fun H => snw_rlpo_to_b_lift H)))).

(* ============================================================ *)
(* Part 5. The isomorphism account: wall iff lifter (zero        *)
(*   thickness difference between the gap and the wall).         *)
(*   Forward: the wall gives the branch pointwise, the B         *)
(*   certificate dropped as redundant;                           *)
(*   reverse: the lifter plus the free universal B certificate   *)
(*   give the wall - the B-side reachability compresses the gap  *)
(*   surface to zero lifters, the wall is the lifter under       *)
(*   another signature.                                          *)
(* ============================================================ *)

Theorem snw_wall_to_b_lift : snw_wall -> snw_b_lift.
Proof.
  intros Hwall t _HB.
  exact (Hwall t).
Qed.

Theorem snw_b_lift_to_wall : snw_b_lift -> snw_wall.
Proof.
  intros Hlift t.
  apply Hlift.
  apply real_square_nonneg_B.
Qed.

Definition snw_wall_iff_lift :
  And (snw_wall -> snw_b_lift) (snw_b_lift -> snw_wall) :=
  (snw_wall_to_b_lift, snw_b_lift_to_wall).

(* ============================================================ *)
(* Part 6 (the G3 generic slot part): the interface slot         *)
(*   resolution station - the UpReqAlign:1122 slot-1 pointer.    *)
(*   The generic interface slot req_square_nonneg (the delta     *)
(*   shape of the RealEnhancedReal instance fields               *)
(*   le:=real_le / zero:=real_zero / mult:=real_mult) resolved   *)
(*   under an rLPO certificate: the Hsq argument slot of the     *)
(*   raised form G09:490 sqp_fisher_zero_implies_pointwise_real  *)
(*   (this station's conclusion face is that slot) supplied from *)
(*   the decider in one step.                                    *)
(*   Canonical face note (this-seat probe, first-hand): the      *)
(*   current tree's RealInterfaceEnhancedSetoid carries no       *)
(*   carrier argument, so the original projection spelling no    *)
(*   longer parses; and the projection face is                   *)
(*   ML-extraction-inexpressible - the extractor inserts a cast  *)
(*   artifact at exactly this station's type face (single-point  *)
(*   located). The statement is therefore stated at the          *)
(*   definitional raw face, the instance-delta expansion of the  *)
(*   slot fields - same treatment as the SqWallCorrMark          *)
(*   companion: interface conversion stations stay off the       *)
(*   extraction face, correctness carried by Print Assumptions   *)
(*   Closed plus coqchk.                                         *)
(* ============================================================ *)

Theorem snw_iface_slot_resolve :
  rLPO ->
  (forall t : Real, real_le real_zero (real_mult t t)).
Proof.
  exact (fun Hdec => lpn_backward Hdec).
Qed.

(* ============================================================ *)
(* Extraction check and assumption audit face                    *)
(* ============================================================ *)

(* Extraction check: the main four faces extracted in full. All four
   proof bodies are pure combinator compositions (the lpn family is pure
   S01/S02/Q layer; the B certificate is a pure real_* top-level function
   chain), evidencing an Obj.magic count of 0.
   Extraction-face exclusion account: snw_iface_slot_resolve stays off
   the extraction face - its slot projection face is
   ML-extraction-inexpressible (the extractor inserts a cast artifact;
   single-point located at that station's type face, not at
   computational content). Same treatment as SqWallCorrMark: interface
   conversion pieces stay off the extraction face; their correctness is
   carried by Print Assumptions Closed plus coqchk. *)
Extraction "_thv3twall1.ml" snw_square_wall_lpo
  snw_b_lift_to_rlpo snw_rlpo_to_b_lift snw_wall_iff_lift.

Print Assumptions snw_wall_sq_wall.
Print Assumptions snw_sq_wall_wall.
Print Assumptions snw_b_lift_to_rlpo.
Print Assumptions snw_rlpo_to_b_lift.
Print Assumptions snw_square_wall_lpo.
Print Assumptions snw_wall_iff_lift.
Print Assumptions snw_iface_slot_resolve.
