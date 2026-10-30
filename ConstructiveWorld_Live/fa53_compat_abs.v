(* ConstructiveWorld-Set -- strict/non-strict monotonicity of addition and the le-version absolute-value identity over the pure-field RealInterfaceEnhanced interface. *)
(** * fa53_compat_abs: two statement families closed constructively
    under the DecidableOrder extension class of S01_BaseRing.

    Mission.  Family 1: strict-by-nonstrict monotonicity of addition,
    lt a b -> le c d -> lt (a+c) (b+d), shared with the sites
    S13_NLiveAudit:2349 and AttnDoeblin:158 (bs_lpc form AttnDoeblin:476
    and S13:2667; further sites S04:285, UpFirewall:107, SqrtfCauchy:73,
    UpEntropyGainReq:91).  Family 2: the le-version absolute-value
    identity, le zero a -> Id (abs a) a, shared with S13:2348 and
    AttnDoeblin:157 (bs_abs form AttnDoeblin:475 and S13:2666) and with
    the gap noted at S06_DiffSamplingGibbs:4031.  Neither statement
    follows from the pure fields alone: the missing one-sided strict
    translation of addition is supplied here through the DecidableOrder
    class, by right cancellation of le, strict translation via
    not_le_lt, a trichotomy assembly, and the abs_pos route.

    Dependencies.  S01_BaseRing (interface and class fields; Set-layer
    Or/Not/Empty_set; Id, id_cong, id_trans, id_sym; le/lt lemmas).

    References.  DecidableOrder class, S01_BaseRing:329ff; abs_pos,
    S01:293; consumer sites as listed under Mission.

    Constructivity.  Statements are Set-carried, no Prop leakage;
    Axioms: none; every proof closes by Qed via cancellation,
    trichotomy and contradiction arguments.

    Build.  rocq c -native-compiler no -q -Q <source-seat world> ""
    fa53_compat_abs.v (Rocq 9.1.0) against the same-world dependency
    .vo of S01_BaseRing, under the load wrapper. *)

Require Import S01_BaseRing.

Section Fa53CompatAbs.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* Projection aliases: the class field name lt_dec is shadowed by
   Stdlib Compare_dec.lt_dec; not_le_lt is destructed alongside, per
   the S06_DiffSamplingGibbs:5157 idiom, to preclude the same shadowing. *)
Definition fa53_lt_dec : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

Definition fa53_not_le_lt : forall a b : R, Not (le a b) -> lt b a :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => nll
  end.

(* ---- Support (1): x + (c + -c) collapses onto x (ring unit
   identity; S01 associativity orientation: plus_assoc turns the
   right-associated LHS into the left-associated RHS) ---- *)
Lemma fa53_plus_assoc_opp_r :
  forall x c : R, Id (plus (plus x c) (opp c)) x.
Proof.
  intros x c.
  assert (H1 : Id (plus (plus x c) (opp c)) (plus x (plus c (opp c)))).
  { exact (id_sym (plus_assoc x c (opp c))). }
  assert (H2 : Id (plus c (opp c)) zero).
  { exact (plus_opp c). }
  assert (H3 : Id (plus x (plus c (opp c))) (plus x zero)).
  { exact (id_cong (fun w => plus x w) H2). }
  assert (H4 : Id (plus x zero) x).
  { exact (plus_zero x). }
  exact (id_trans H1 (id_trans H3 H4)).
Qed.

(* ---- Support (2): right cancellation of addition for le
   (prerequisite for the strict one-sided translation) ---- *)
Lemma fa53_le_plus_cancel_r :
  forall a b c : R, le (plus b c) (plus a c) -> le b a.
Proof.
  intros a b c H.
  apply (le_id_r b (plus (plus a c) (opp c)) a).
  - exact (fa53_plus_assoc_opp_r a c).
  - apply (le_id_l b (plus (plus b c) (opp c)) (plus (plus a c) (opp c))).
    + exact (id_sym (fa53_plus_assoc_opp_r b c)).
    + exact (le_plus_compat (plus b c) (plus a c) (opp c) (opp c) H
                            (le_refl (opp c))).
Qed.

(* ---- Support (3) (new result): one-sided strict translation
   at the interface + decidable-order layer.  lt a b implies
   ~ le (b+c) (a+c): otherwise right cancellation gives le b a,
   contradicting lt a b via le_lt_trans + lt_irrefl.  not_le_lt
   then flips this into a strict order. *)
Lemma fa53_lt_plus_translate_r :
  forall a b c : R, lt a b -> lt (plus a c) (plus b c).
Proof.
  intros a b c Hab.
  apply (fa53_not_le_lt (plus b c) (plus a c)).
  intro Hle.
  destruct (lt_irrefl b
    (le_lt_trans b a b (fa53_le_plus_cancel_r a b c Hle) Hab)).
Qed.

(* ---- Support (3'): one-sided strict translation, left-placed
   variant (from (3) by two commutativity rewrites) ---- *)
Lemma fa53_lt_plus_translate_l :
  forall a b c : R, lt a b -> lt (plus c a) (plus c b).
Proof.
  intros a b c Hab.
  apply (lt_id_r (plus c a) (plus b c) (plus c b)).
  - exact (plus_comm b c).
  - apply (lt_id_l (plus c a) (plus a c) (plus b c)).
    + exact (plus_comm c a).
    + exact (fa53_lt_plus_translate_r a b c Hab).
Qed.

(* ---- Item 1: strict x non-strict order preservation of addition
   (Family 1 main statement).  Trichotomy on c d: inl, both strict,
   goes through lt_plus_compat; inr-eq through the id_cong rewrite
   plus translation (3); inr-gt contradicts le c d by irrefl. ---- *)
Theorem fa53_lt_plus_compat_lt_le_dec :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct (fa53_lt_dec c d) as [Hcd_lt | [Hcd_eq | Hcd_gt]].
  - (* c < d: both strict, add them *)
    exact (lt_plus_compat a b c d Hab Hcd_lt).
  - (* c == d: b+d collapses to b+c; strictness supplied by the translation *)
    apply (lt_id_r (plus a c) (plus b c) (plus b d)).
    + exact (id_cong (fun x => plus b x) Hcd_eq).
    + exact (fa53_lt_plus_translate_r a b c Hab).
  - (* d < c: conflicts with le c d, giving lt d d; irrefl contradiction *)
    destruct (lt_irrefl d (lt_le_trans d c d Hcd_gt Hcd)).
Qed.

(* ---- Item 2: non-strict x strict order preservation of addition
   (Family 1 dual statement site).  Trichotomy on a b: inl both
   strict; inr-eq through the id_cong rewrite plus translation (3)
   on the b side; inr-gt contradicts le a b by irrefl.  Symmetric
   to Item 1, likewise unconditional. ---- *)
Theorem fa53_lt_plus_compat_le_lt_dec :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct (fa53_lt_dec a b) as [Hab_lt | [Hab_eq | Hab_gt]].
  - (* a < b: both strict, add them *)
    exact (lt_plus_compat a b c d Hab_lt Hcd).
  - (* a == b: a+c collapses to b+c; strictness supplied by the translation *)
    apply (lt_id_l (plus a c) (plus b c) (plus b d)).
    + exact (id_cong (fun x => plus x c) Hab_eq).
    + exact (fa53_lt_plus_translate_l c d b Hcd).
  - (* b < a: conflicts with le a b, giving lt a a; irrefl contradiction *)
    destruct (lt_irrefl a (le_lt_trans a b a Hab Hab_gt)).
Qed.

(* ---- Item 3: the le-version abs identity (Family 2 main
   statement).  Trichotomy on zero a: the lt branch goes through
   the abs_pos field (S01:293); the eq branch through the
   id_cong abs + abs_zero id chain; the opposite branch hits
   irrefl.  This is the interface-level fully discharged form of
   abs_ge_zero_id_cc across its statement sites: the library
   previously held only the lt-version abs_pos field plus
   concrete-Real-layer witnesses. ---- *)
Theorem fa53_abs_ge_zero_id_dec :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  destruct (fa53_lt_dec zero a) as [Hza | [Hza_eq | Haz]].
  - (* 0 < a: direct from the positivity field *)
    exact (abs_pos a Hza).
  - (* 0 == a: |a| == |0| == 0 == a (three-step id chain) *)
    exact (id_trans (id_cong abs (id_sym Hza_eq))
                    (id_trans abs_zero Hza_eq)).
  - (* a < 0: conflicts with le zero a, giving lt a a; irrefl contradiction *)
    destruct (lt_irrefl a (lt_le_trans a zero a Haz Ha)).
Qed.

(* ---- Item 4: direct match for the bs shape of Family 2
   (explicit application form).  The bs_abs statement sites at
   AttnDoeblin:475 / S13:2666 state verbatim the statement of
   Item 3; an explicit application form is given here (same
   coordinates as Item 3). ---- *)
Corollary fa53_bs_abs_shape :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  exact (fun a Ha => fa53_abs_ge_zero_id_dec a Ha).
Qed.

End Fa53CompatAbs.

(* ---- Self-audit: explicit Print Assumptions statements,
   in file ---- *)
Print Assumptions fa53_le_plus_cancel_r.
Print Assumptions fa53_lt_plus_translate_r.
Print Assumptions fa53_lt_plus_translate_l.
Print Assumptions fa53_lt_plus_compat_lt_le_dec.
Print Assumptions fa53_lt_plus_compat_le_lt_dec.
Print Assumptions fa53_abs_ge_zero_id_dec.
Print Assumptions fa53_bs_abs_shape.
