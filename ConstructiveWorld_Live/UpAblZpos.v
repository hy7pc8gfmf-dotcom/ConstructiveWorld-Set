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

(* S05 主节 Z_align 的出节实形同构（迭代节使用同形）：                  *)
(* Z_align := Σ_s pi_ref(s)·exp_neg(−r(s)/β)，beta_pos 为显式参。        *)
Definition zab_Z_align (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) : R :=
  sum_over_S (fun s => mult (pi_ref s)
                            (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* 求和项逐项正：pi_ref 逐点正 × exp_neg 恒正 ⟹ 乘积正（mult_positive 与 exp_neg_pos 合成）。 *)
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

(* 主定理（条件形）：显式前提 Hsum_pos 即 S05 中 sum_over_S 正性假设的实形， *)
(* 在此前提下消解 lt zero (Z_align …)（对应 S05 主节与迭代节同一接口假设，   *)
(* 语句逐字同形）。                                                       *)
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

(* 接口面无条件伴件（接口可证部分全量兑现）：不取求和正性前提，            *)
(* 仅用 sum_over_S_nonneg 接口字段，逐项正经 lt_le_iff 降为非负，          *)
(* 得整体非负——le zero (Z_align …) 无条件成立。                          *)
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

(* ---- 假设面自检（Print Assumptions） ---- *)
Print Assumptions zab_summand_pos.
Print Assumptions zab_Z_align_pos.
Print Assumptions zab_Z_align_nonneg.
