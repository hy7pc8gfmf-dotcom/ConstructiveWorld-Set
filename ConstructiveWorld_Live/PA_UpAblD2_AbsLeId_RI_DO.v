(* ==========================================================================
   PA_UpAblD2_AbsLeId_RI_DO.v - the two interface slots of the abstract
   AbsLeId section, supplied at concrete and abstract carriers.
   Mission. 使命: five theorems - uabd2_ali_abs_ge_zero_id_pair (the slot
     statement inside the interface-context section), its explicit
     fully-applied form uabd2_ali_abs_ge_zero_id_explicit, the concrete
     Real-carrier forms uabd2_ri_real_abs_ge_zero_id and
     uabd2_ri_reqface_abs_ge_zero_id, and the decidable-order field-five
     form uabd2_do_ltle_iffdec_real.
   Dependencies. 依赖清单: S01_BaseRing (RealInterfaceEnhanced /
     DecidableOrder / the Set-layer Or), fa53_compat_abs
     (fa53_abs_ge_zero_id_dec), S02_CauchyComplete, S03_QExp, AbsLeId
     (ali_real_abs_ge_zero_id) of the -Set lineage world.
   References. 对标: the AbsLeId abstract section's two context slots (the
     interface bundle and the decidable-order extension). Statement names
     carried over verbatim; adaptation = face convergence on this world's
     own precedent: the interface-context section is verbatim (the S01
     face is already argument-less in both trees), and the concrete
     req-face statement carries the supply lemma's own direct faces
     (real_le / real_eq) - in the argument-less world the projection
     face and the direct face are the same constant chain, so the two
     concrete forms carry one face.
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; each proof consumes one in-register
     supply by exact (the field-five form is a transparent unfold, T-grade
     by disclosure); no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> ""
     PA_UpAblD2_AbsLeId_RI_DO.v (cpu_guard thermal wrapper,
     ulimit -s 65532).
   ========================================================================== *)

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

(* 出节形实证（FA3 纪律6：节参消失不对称 Check 实证） *)
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

Print Assumptions uabd2_do_ltle_iffdec_real.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
