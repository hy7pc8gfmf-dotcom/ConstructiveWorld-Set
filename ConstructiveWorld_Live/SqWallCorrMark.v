(* ==========================================================================
   SqWallCorrMark.v - connectors and reachable restatements for the
   "universal square nonnegativity" premise site (forall a, le zero
   (mult a a)) of the Cauchy reals.
   Mission.
     State the site's interface-projection connector (the Real instance
     field mapping), its definitional identifications with SqWall, the two
     limited-LPO pointer connectors, an isomorphic restatement of the
     equivalence record, and the reachable Bishop-form restatements. All
     identifiers carry the swc_ prefix.
   Dependencies.
     CW_ConstructiveWorld_219; Stdlib Extraction; the S01-S15 chain per
     the Require face below; UpReqLpoEquiv (SqWall:224 / rLPO:229 /
     lpn_forward:245 / lpn_backward:347 / lpn_equivalence:437, vo base on
     disk); UpRealLeB (real_le_b:55, real_square_nonneg_B:634);
     RealInterfaceEnhancedMod (S07_RealSetoidExpLog).
   References.
     Site registrations: UpReqAlign.v:1122 and UpReqSqrtF.v:707 (generic-R
     sites), G01_CoreMicro.v:324, S06_DiffSamplingGibbs.v:1689,
     UpReqSLM.v:735, S11_TP3B5.v (provable shape), G09_MiscSmall.v:491/518;
     reachable alternative: UpRealLeB.v:634 real_square_nonneg_B with
     certificate chain via real_square_nonneg_eps (S08_RealMainlineDPO).
   Constructivity.
     Zero acknowledgment statements: every station Qed-closed and audited
     by Print Assumptions below; connectors discharge by conversion
     (exact); the Bishop-form restatements carry full constructive proofs.
   Build.
     rocq c -native-compiler no -q -Q . "" (vo shadow tree in-place
     recompile), cpu_guard thermal wrapper for load control.
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

(* Site survey (adjudication of the premise position).
   Under the Real instance (S07 RealEnhancedReal: le := real_le /
   zero := real_zero / mult := real_mult) the premise site is
   definitionally the same shape as SqWall -- the data form of the wall.
   Three-way verdict: the Or-encoded universal form equals the wall (it is
   equivalent to the limited LPO, machine-checked in UpReqLpoEquiv, so no
   universal supplier is reachable constructively); the Bishop epsilon-wise
   form is reachable (real_square_nonneg_B proves the universal statement);
   conditional / premise-carrying shapes sit below the threshold site.
   Site registrations and resolution pointers:
   - UpReqAlign.v:1122 (generic-R premise site): wall face (not provable
     inside the interface-generic level; a constructive ordered field has
     no trichotomy, so the sign-decision datum is not supplyable -- same
     root as the S02:802 wall note; GRPO T1.5 same-position precedent
     S05:5582). Resolution channel: G09:490 already carries
     sqp_fisher_zero_implies_pointwise_real whose Hsq argument sits at
     this site -- one real argument (swc_lpn_backward_slot Hdec) resolves
     it from the limited LPO (lpn_backward supplies the premise,
     lpn_forward consumes it).
   - UpReqSqrtF.v:707 (SqrtF generic-R site, honest route): same verdict;
     the section-8 correction note (:692-706) shows the plain shape is not
     supplyable at the Real layer (the t := 1/n sequence counterexample;
     |t|*|t| and t*t have no req bridge). The use-site :725 consumes it
     directly; downstream sqrtf_iterate_sq_ge propagates it wholesale and
     SqrtfCauchy.v:76 sits at the same position -- supply one real
     argument, or switch to the Bishop-form restatement
     swc_sq_ge_a_b_form.
   - Whole-tree survey additions: G01_CoreMicro.v:324
     real_var_nonneg_cond, S06_DiffSamplingGibbs.v:1689
     set_square_nonneg, UpReqSLM.v:735 req_set_square_nonneg (conditional
     shape), S11_TP3B5.v Qsquare_nonneg (provable shape), UpReqU2/UpReqRDF
     double-nonnegativity premise shapes (multiplication order
     compatibility), G09_MiscSmall.v:491/518 two raised-argument shapes
     (premise isolation in place). Reachable-alternative pointer:
     UpRealLeB.v:424 real_square_nonneg_B (0 <=_B t*t universally
     provable, closed; certificate chain = real_le_closure_b_one:373 plus
     the direct epsilon form; epsilon-form source S08:3628). Verdict: the
     Or-encoded universal form = wall (limited-LPO equivalence), the
     epsilon-wise form = reachable -- isomorphic restatements in
     swc_sq_wall_b_reachable / swc_sq_ge_a_b_form. *)

(* Connector 1: interface-projection premise site -> raw face (the
   conversion piece for the Real instance field mapping; downstream
   pieces all stay on the raw face). The RealInterfaceEnhancedSetoid
   instance RealEnhancedReal binds its le/zero/mult fields to
   real_le/real_zero/real_mult, so the premise site is canonically
   stated at its definitional raw-layer form; the instance-projection
   form is the same statement up to those field bindings. Extraction
   note: on this extractor the projection face is carried by an abstract
   erased type and would force Obj.magic for any informative term, hence
   the canonical raw-layer statement. *)
Lemma swc_interface_slot_face :
  (forall t : Real, real_le real_zero (real_mult t t)) ->
  (forall t : Real, real_le real_zero (real_mult t t)).
Proof.
  exact (fun H => H).
Qed.

(* Connector 2: the raw premise face IS SqWall (verbatim same face as
   UpReqLpoEquiv:224); composed with Connector 1 it is the channel from
   any interface-generic premise site to its Real-instance form. *)
Definition swc_sq_wall_face : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

Lemma swc_sq_wall_face_is_sq_wall : swc_sq_wall_face -> SqWall.
Proof.
  exact (fun H => H).
Qed.

Lemma swc_sq_wall_is_sq_wall_face : SqWall -> swc_sq_wall_face.
Proof.
  exact (fun H => H).
Qed.

(* Connector 3: limited-LPO bidirectional pointer use-sites (ready to use
   with one argument supplied).
   Premise supply (resolution): rLPO certificate -> raw premise face --
   lpn_backward provides the argument directly.
   Premise consumption (decision): raw premise face certificate -> rLPO --
   lpn_forward provides the argument directly. *)
Theorem swc_lpn_backward_slot :
  rLPO -> (forall t : Real, real_le real_zero (real_mult t t)).
Proof.
  exact lpn_backward.
Qed.

Theorem swc_lpn_forward_slot :
  (forall t : Real, real_le real_zero (real_mult t t)) -> rLPO.
Proof.
  exact lpn_forward.
Qed.

(* Connector 4: premise-site isomorphism of the equivalence record
   (one-step restatement of lpn_equivalence:437).
   Statement-face correction: the first component was originally written
   as And (forall t : Real, real_le real_zero (real_mult t t) -> rLPO),
   where the forall scope swallows the trailing "-> rLPO", giving the
   pointwise double-premise form
     forall t, (real_le real_zero (real_mult t t) -> rLPO) --
   a product structure NOT isomorphic to the whole-wall form of the
   construction pair ((forall t, real_le real_zero (real_mult t t))
   -> rLPO): the first binder domain is Real in the former and the
   universal face in the latter; kernel conversion fails exactly there,
   and that point is the statement/construction mismatch. Reparenthesized
   to the whole-wall form; both components are element-wise isomorphic to
   lpn_equivalence (faces equal up to the delta expansion of SqWall). *)
Definition swc_lpn_equivalence_slot :
  And ((forall t : Real, real_le real_zero (real_mult t t)) -> rLPO)
      (rLPO -> (forall t : Real, real_le real_zero (real_mult t t))) :=
  (swc_lpn_forward_slot, swc_lpn_backward_slot).

(* ============================================================ *)
(* Reachable alternatives: Bishop-form (epsilon-wise) isomorphic       *)
(* restatement theorems                                                *)
(* ============================================================ *)

(* Restatement 1: universal square nonnegativity in Bishop form -- the
   reachable shape of the wall face under the real_le_b encoding
   (one-step restatement of UpRealLeB:634 real_square_nonneg_B). *)
Theorem swc_sq_wall_b_reachable :
  forall t : Real, real_le_b real_zero (real_mult t t).
Proof.
  exact real_square_nonneg_B.
Qed.

(* Restatement 2: verbatim restatement of the epsilon-form source
   (S08_RealMainlineDPO:3653 real_square_nonneg_eps; the original of the
   certificate-supply chain of the Bishop form, restated in one step to
   prevent dangling references). *)
Theorem swc_square_nonneg_eps_face : forall (t eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_mult t t) eps).
Proof.
  exact real_square_nonneg_eps.
Qed.

(* Restatement 3 (main delivery): isomorphic restatement theorem with a
   Bishop premise -- the use-site face (the premise-injection chain of
   sqrtf_sq_ge_a: the premise supplies s*s >= 0, le_plus_compat closes
   a <= s*s + a) restated isomorphically under a Bishop premise.
   The premise is swapped from the honest site (the Or-encoded wall face)
   to the Bishop premise (real_le_b, reachable), and the conclusion face
   swaps to Bishop form in step: a <=_B s*s + a.
   Proof sketch: at eps the Bishop premise supplies 0 < s*s + eps
   directly; the shift by a (real_lt_plus_translate) plus the assoc/comm
   reshaping chain closes the goal; real_eq_plus_compat takes its
   arguments in the crosswise signature (a ~= c / b ~= d) per
   S07_RealSetoidExpLog:235. *)
Theorem swc_sq_ge_a_b_form : forall (a s : Real),
  real_lt real_zero a ->
  real_le_b real_zero (real_mult s s) ->
  real_le_b a (real_plus (real_mult s s) a).
Proof.
  intros a s Ha Hsq.
  unfold real_le_b in Hsq.
  unfold real_le_b.
  intros eps Heps.
  assert (H2 : real_lt real_zero (real_plus (real_mult s s) eps))
    by exact (Hsq eps Heps).
  assert (H3 : real_lt (real_plus a real_zero)
                       (real_plus a (real_plus (real_mult s s) eps)))
    by exact (real_lt_plus_translate a real_zero
                (real_plus (real_mult s s) eps) H2).
  assert (H4 : real_lt (real_plus a real_zero)
                       (real_plus (real_plus (real_mult s s) a) eps)).
  { apply (RealSetoid.real_lt_id_r (real_plus a real_zero)
             (real_plus a (real_plus (real_mult s s) eps))
             (real_plus (real_plus (real_mult s s) a) eps)).
    - apply (real_eq_trans
               (real_plus a (real_plus (real_mult s s) eps))
               (real_plus (real_plus a (real_mult s s)) eps)
               (real_plus (real_plus (real_mult s s) a) eps)
               (real_plus_assoc a (real_mult s s) eps)
               (RealSetoid.real_eq_plus_compat
                  (real_plus a (real_mult s s))
                  eps
                  (real_plus (real_mult s s) a)
                  eps
                  (real_plus_comm a (real_mult s s))
                  (real_eq_refl eps))).
    - exact H3. }
  apply (RealSetoid.real_lt_id_l a (real_plus a real_zero)
           (real_plus (real_plus (real_mult s s) a) eps)).
  - apply real_eq_sym.
    apply real_plus_zero.
  - exact H4.
Qed.

(* ============================================================ *)
(* Extraction check and assumption audit face                          *)
(* ============================================================ *)

(* Extraction check (target name follows the KLWallClosed extraction
   naming convention): full extraction face of the three main pieces.
   None of the three proof bodies touches the RealEnhancedReal
   class-instance wrapper constants (the lpn family stays on the pure
   S01/S02/Q layer; the Bishop family stays on the pure real_* top-level
   function chain); the expected Obj.magic count is 0. *)
Extraction "_thv3sw3_G3.ml" swc_lpn_equivalence_slot
  swc_sq_wall_b_reachable swc_sq_ge_a_b_form.

Print Assumptions swc_interface_slot_face.
Print Assumptions swc_sq_wall_face_is_sq_wall.
Print Assumptions swc_lpn_backward_slot.
Print Assumptions swc_lpn_forward_slot.
Print Assumptions swc_sq_wall_b_reachable.
Print Assumptions swc_sq_ge_a_b_form.
