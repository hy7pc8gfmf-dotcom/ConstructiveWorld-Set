(* ConstructiveWorld-Set — the AbsLeId interface slots, concrete and abstract carriers. *)

(** * UpAblD2_AbsLeId_RI_DO: the AbsLeId slots at concrete and abstract carriers.

    Mission.  Five theorems: [uabd2_ali_abs_ge_zero_id_pair] (the slot
      statement in the interface-context section), its explicit form
      [uabd2_ali_abs_ge_zero_id_explicit], the concrete Real-carrier
      forms [uabd2_ri_real_abs_ge_zero_id] and [uabd2_ri_reqface_abs_ge_zero_id],
      and the field-five decidable-order form [uabd2_do_ltle_iffdec_real].

    Dependencies.  [S01_BaseRing] ([RealInterfaceEnhanced] /
      [DecidableOrder] / Set-layer [Or]), [fa53_compat_abs]
      ([fa53_abs_ge_zero_id_dec]), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [AbsLeId] ([ali_real_abs_ge_zero_id]).

    References.  This development, AbsLeId.v; statement names carried
      over verbatim from the same-name ConstructiveWorld-Main baseline
      module.  Adaptation: the interface-context section is verbatim
      (the S01 face is already argument-less in this tree); the
      concrete req-face form carries the supply lemma's direct faces
      ([real_le]/[real_eq] — one constant chain in this world).

    Constructivity.  All statements are Set-layer; every proof is
      [Qed]-closed with zero admitted items; each proof consumes one
      in-scope supply item by [exact] (the field-five form is a
      transparent unfold); no new axioms.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      UpAblD2_AbsLeId_RI_DO.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* The interface-context section: same context shape as the abstract
   AbsLeId section; after the section closes the context binders become
   explicit leading arguments (verified by the Check below). *)
Section UabD2PairWorld.

Context {RI0 : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO0 : DecidableOrder RI0}.

(* Slot statement verbatim: the main item's shape, discharged by the
   fa53 supply at the (RI0, DO0) pair. *)
Theorem uabd2_ali_abs_ge_zero_id_pair :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

End UabD2PairWorld.

(* Closed form after the section: the [Check] below witnesses that the
   section parameters [RI0]/[DO0] vanish from the exported statement. *)
Check uabd2_ali_abs_ge_zero_id_pair.

(* The explicit fully-applied form: any (RI1, DO1) pair feeds it. *)
Theorem uabd2_ali_abs_ge_zero_id_explicit :
  forall (RI1 : RealInterfaceEnhanced) (DO1 : DecidableOrder RI1)
         (a : @S01_BaseRing.R RI1),
    @S01_BaseRing.le RI1 (@S01_BaseRing.zero RI1) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI1) (@S01_BaseRing.abs RI1 a) a.
Proof.
  intros RI1 DO1 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI1 DO1 a Ha).
Qed.

(* The concrete Real-carrier forms (the concrete-layer Requires are
   placed after the abstract section, per the AbsLeId precedent). *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import AbsLeId.

(* The direct face: verbatim reference to the in-register concrete
   supply item. *)
Theorem uabd2_ri_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* The projection face: in the argument-less world the interface fields
   and the real_* direct faces form one constant chain, so this form
   carries the same direct face as the supply lemma. *)
Theorem uabd2_ri_reqface_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* The decidable-order field-five form: real_le unfolds transparently to
   the Set-layer Or - one transparent step, disclosed as T-grade. *)
Theorem uabd2_do_ltle_iffdec_real :
  forall a b : Real,
    S01_BaseRing.Or (real_lt a b) (real_eq a b) -> real_le a b.
Proof.
  intros a b H.
  exact H.
Qed.

(* The decidable-order fields 1-4 (total-order trichotomy /
   non-degeneracy decision family) are not instantiated here. *)

(* ============ assumption audit ============ *)
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_do_ltle_iffdec_real.
