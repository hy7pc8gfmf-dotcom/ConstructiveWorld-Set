(* ConstructiveWorld-Set — interface-level resolution of Z_align positivity. *)

(** * UpAblZpos: positivity of the aggregated reward [Z_align] at the abstract interface level.

    Mission.  An independent resolution of the abstract assumption
      [Z_align_pos] of [S05_AlignmentGRPO] (exported form
      [lt zero (Z_align reward beta beta_pos pi_ref)]): [zab_Z_align_pos]
      derives it from the explicit premise [Hsum_pos] (strict positivity of
      [sum_over_S]); the unconditional companion [zab_Z_align_nonneg] gives
      [le zero (Z_align ...)] from [sum_over_S_nonneg] alone.

    Dependencies.  Requires [S01_BaseRing] of this development (the interface
      [RealInterfaceEnhanced] with its [sum_over_S] field family); no others.

    References.  This development, [S05_AlignmentGRPO].v (read-only
      counterpart: the [Z_align] export form is matched statement for
      statement there; the per-summand chain [zab_summand_pos] mirrors the
      [Z_rel_pos] derivation).  The premise is explicit because the interface
      carries only linear/add/ext/le/nonneg fields for [sum_over_S]; a strict
      sum-positivity field (or a Real-layer instantiation) would remove it.

    Constructivity.  Pure constructive; statement faces carried by [Set]
      through the interface order [lt]/[le]; zero admission words.  Proofs
      are short chains: pointwise positivity composed with [exp_neg_pos] via
      [mult_positive]; non-negativity via [lt_le_iff].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblZpos.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

Require Import S01_BaseRing.

Section ZabZPos.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* The section-discharged real form of the [Z_align] of the S05 main *)
(* section (the iterative section uses the same form): *)
(* [Z_align := Σ_s pi_ref(s)·exp_neg(−r(s)/β)], with [beta_pos] an *)
(* explicit argument. *)
Definition zab_Z_align (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) : R :=
  sum_over_S (fun s => mult (pi_ref s)
                            (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* Each summand is positive: [pi_ref] is pointwise positive and [exp_neg] *)
(* is everywhere positive, so the product is positive — the composition *)
(* of [mult_positive] with [exp_neg_pos]. *)
Lemma zab_summand_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    forall s : S,
      lt zero (mult (pi_ref s)
                    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos s.
  apply mult_positive.
  - exact (pi_ref_pos s).
  - apply exp_neg_pos.
Qed.

(* The main theorem in conditional form: the explicit premise [Hsum_pos] *)
(* is the real form of the [sum_over_S]-positivity assumption of the S05 *)
(* main section; under it [lt zero (Z_align ...)] is discharged — the *)
(* same interface assumption serves the S05 main and iterative sections, *)
(* with statement faces matching verbatim. *)
Theorem zab_Z_align_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hsum_pos : forall f : S -> R,
                       (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f)),
    lt zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos Hsum_pos.
  unfold zab_Z_align.
  apply Hsum_pos.
  exact (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos).
Qed.

(* The unconditional companion at the interface level (the provable part *)
(* of the interface discharged in full): without the sum-positivity *)
(* premise, using only the [sum_over_S_nonneg] interface field, each *)
(* summand's strict positivity is weakened to non-negativity by *)
(* [lt_le_iff], so the aggregate is non-negative — [le zero (Z_align ...)] *)
(* holds unconditionally. *)
Theorem zab_Z_align_nonneg :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    le zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos.
  unfold zab_Z_align.
  apply sum_over_S_nonneg.
  intro s.
  exact (lt_le_iff _ _           (inl (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos s))).
Qed.

End ZabZPos.

(* ---- assumption audit (Print Assumptions) ---- *)
Print Assumptions zab_summand_pos.
Print Assumptions zab_Z_align_pos.
Print Assumptions zab_Z_align_nonneg.
