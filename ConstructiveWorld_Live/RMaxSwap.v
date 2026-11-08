(* ConstructiveWorld-Set -- symmetric swap bridges over the plain-form r_max bounds and a clip specialization in the req world. *)

(** * RMaxSwap: symmetric exchange for the plain-form r_max bounds in the req world.

    Mission.  Symmetric exchange for the plain-form r_max bounds in the req world: given the
      swap witness [rms_r_max_comm] as an explicit section premise, the one-way bridges
      [rms_le_r_of_ge] and [rms_ge_of_le_r] transport a left-slot bound to the right-slot
      form and back, the composite [rms_ge_roundtrip] returns the left-slot bound unchanged,
      and the clip [rms_clip] yields the lower bound [rms_rpl_clip_lower] on [req_minus one
      epsilon] from the left slot [r_max_ge_plain] alone.

    Dependencies.  No direct Stdlib Requires; requires of this development
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqAlgebra], [UpReqRDF].

    References.  This development, RMaxSwap.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" RMaxSwap.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

(* Carrier pinning (the [UpReqRDF] pattern): [RealInterfaceEnhancedSetoid] is  *)
(* a zero-argument Class in this tree ([S07_RealSetoidExpLog]); the global    *)
(* instance [RealEnhancedReal] resolves the fields and the carrier R is       *)
(* pinned to the global Real by the Notations below.  The generation binders  *)
(* {R : Set} / {RIS : RealInterfaceEnhancedSetoid R} of the Main baseline     *)
(* were removed; the relation fields req/le are bound by Notation to the      *)
(* concrete S02_CauchyComplete shapes [real_eq]/[real_le] -- exactly the      *)
(* global instance's field values, the same terms the statement face          *)
(* elaborates to (bound forms extract as true data; boxed class field         *)
(* projections are erasure faces when mixed with the concrete carrier).       *)
Notation R := Real.
Notation req := real_eq.
Notation le := real_le.

Section RMaxSwap.

Context {RDP : ReqDiffPlain}.
Variable epsilon : R.

(* ---- symmetric swap slot, held as an explicit section premise ----
   instantiation note: the plain form req (r_max a b) (r_max b a) holds in a
   concrete model whose r_max is symmetric coordinatewise (as for Qmax);
   supplying that witness unlocks every bridge of this section at once. *)
Hypothesis rms_r_max_comm : forall a b : R, req (r_max a b) (r_max b a).

(* ---- bridge B (return direction): left-slot plain bound implies the right-slot plain form ----
   le b (r_max b a), the left-slot instance Hge b a, transports along req
   through the swap in the second argument, giving le b (r_max a b). *)
Lemma rms_le_r_of_ge :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le b (r_max a b).
Proof.
  intros Hge a b.
  exact (req_le_compat b b (r_max b a) (r_max a b)
                        (req_refl b) (rms_r_max_comm b a) (Hge b a)).
Qed.

(* ---- bridge A (slot-elimination direction): right-slot plain bound implies the left-slot plain form ----
   le a (r_max b a), the right-slot instance Hler b a, transports by the
   same swap step, giving le a (r_max a b). *)
Lemma rms_ge_of_le_r :
  forall (Hler : forall a b : R, le b (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hler a b.
  exact (req_le_compat a a (r_max b a) (r_max a b)
                        (req_refl a) (rms_r_max_comm b a) (Hler b a)).
Qed.

(* ---- composite: bridge A applied after bridge B restores the left-slot bound itself ---- *)
Lemma rms_ge_roundtrip :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hge a b.
  exact (rms_ge_of_le_r (rms_le_r_of_ge Hge) a b).
Qed.

(* ---- definition of the same shape as rpl_clip in UpReqPPOPlain ----
   the minus position is req_minus, transparently plus a (opp b) in
   general, and the statement face follows that shape. *)
Definition rms_clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).

(* ---- specialization of rpl_clip_lower ----
   the conclusion has the same shape, verbatim, as rpl_clip_lower in
   UpReqPPOPlain.v; the slot source is the RDP left-slot bound
   (r_max_ge_plain) together with bridge B, with no use of the
   self-standing right-slot bound. *)
Lemma rms_rpl_clip_lower :
  forall r : R, le (req_minus one epsilon) (rms_clip r).
Proof.
  intro r. unfold rms_clip.
  exact (rms_le_r_of_ge (@r_max_ge_plain RDP)
                        (min r (plus one epsilon)) (req_minus one epsilon)).
Qed.

End RMaxSwap.

Print Assumptions rms_rpl_clip_lower.
