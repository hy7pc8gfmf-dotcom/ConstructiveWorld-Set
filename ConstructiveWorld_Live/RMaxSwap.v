(* ConstructiveWorld-Set -- symmetric r_max swap bridge in plain form. *)

(** * RMaxSwap: plain-form symmetric swap bridge for r_max.

    Mission.  The symmetric swap slot [rms_r_max_comm] (T2① explicit
      argument, not an axiom; one instantiation unlocks the whole
      bridge); the one-way bridges [rms_le_r_of_ge] and [rms_ge_of_le_r]
      ([req_le_compat] transport: either side's plain slot + swap gives
      the other side's plain form); the roundtrip check [rms_ge_roundtrip];
      and the feedback piece [rms_rpl_clip_lower], conclusion verbatim
      [rpl_clip_lower] of UpReqPPOPlain.v, fed from the RDP left slot + bridge B.

    Dependencies.  The libraries listed by the in-file Require statement
      face: [S01_BaseRing] through [S15_TailFEPUp], [UpReqAlgebra], [UpReqRDF].

    References.  UpReqRDF.v [ReqDiffPlain] class [r_max_ge_plain] (left
      plain slot); UpReqPPOPlain.v §1 [r_max_le_r_plain] (right plain
      slot); the interface [RealInterfaceEnhancedSetoid] gives only
      per-eps forms ([r_max_le_l]/[r_max_le_r]), leaving the plain form
      without interface support (the UpReqAlign3 verdict); Id
      [r_max_le_l]/[r_max_le_r]; UpReqPPOPlain.v [rpl_clip_lower] (Id L19518).

    Constructivity.  Purely constructive; Set-layer statements, zero Prop
      leakage ([req] and [le] Set-valued); pure term mode, no Ltac rewrite
      layer; the assumption slot is an explicit Section argument (T2①),
      not an axiom; zero admission-style statements; extracts.

    Build.  [coqc -native-compiler no -q -Q . "" RMaxSwap.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
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

(* ---- T2① symmetric swap slot (the gap position recorded on the
     precedent card; an explicit Section argument per T2①) ----
   instantiation source note: the plain form req (r_max a b) (r_max b a)
   unlocks the whole bridge of this section in one step once a concrete
   model on the abstract-interface side supplies an r_max symmetry witness
   (coordinatewise Qmax symmetry). *)
Hypothesis rms_r_max_comm : forall a b : R, req (r_max a b) (r_max b a).

(* ---- bridge B (feedback direction): the left plain slot gives the
     right plain form ----
   le b (r_max b a) (the left-slot instance Hge b a), transported along
   the y leg of req (the swap), gives le b (r_max a b). *)
Lemma rms_le_r_of_ge :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le b (r_max a b).
Proof.
  intros Hge a b.
  exact (req_le_compat b b (r_max b a) (r_max a b)
                        (req_refl b) (rms_r_max_comm b a) (Hge b a)).
Qed.

(* ---- bridge A (slot-elimination direction): the right plain slot gives
     the left plain form ----
   le a (r_max b a) (the right-slot instance Hler b a), transported along
   the same req leg, gives le a (r_max a b). *)
Lemma rms_ge_of_le_r :
  forall (Hler : forall a b : R, le b (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hler a b.
  exact (req_le_compat a a (r_max b a) (r_max a b)
                        (req_refl a) (rms_r_max_comm b a) (Hler b a)).
Qed.

(* ---- roundtrip piece: bridge A ∘ bridge B restores the left plain slot
     itself (drift check of the bridge system) ---- *)
Lemma rms_ge_roundtrip :
  forall (Hge : forall a b : R, le a (r_max a b)) (a b : R),
    le a (r_max a b).
Proof.
  intros Hge a b.
  exact (rms_ge_of_le_r (rms_le_r_of_ge Hge) a b).
Qed.

(* ---- same-shape definition of Id ppo_clip L19506 / UpReqPPOPlain
     rpl_clip ----
   (the minus position req_minus δ is transparently plus a (opp b), and
   the statement face follows suit) *)
Definition rms_clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).

(* ---- feedback specialization of rpl_clip_lower ----
   the conclusion is verbatim same-shape as UpReqPPOPlain.v rpl_clip_lower
   (the req position of Id L19518); the slot source is the RDP left plain
   slot (r_max_ge_plain) + bridge B, with zero demand on the self-standing
   right plain slot. *)
Lemma rms_rpl_clip_lower :
  forall r : R, le (req_minus one epsilon) (rms_clip r).
Proof.
  intro r. unfold rms_clip.
  exact (rms_le_r_of_ge (@r_max_ge_plain RDP)
                        (min r (plus one epsilon)) (req_minus one epsilon)).
Qed.

End RMaxSwap.

Print Assumptions rms_rpl_clip_lower.
