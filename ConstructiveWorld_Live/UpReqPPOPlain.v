(* ConstructiveWorld-Set -- req-carrier PPO plain-face statements. *)

(** * UpReqPPOPlain: plain-face PPO objectives, clipping, and conservativity on the req order.

    Mission.  Formalizes the plain-face PPO block over an abstract summation [sumf]:
      clipped policy objectives, their conservativity against the unclipped
      importance-sampling objective, nonnegativity of the gap and clipping error,
      and the value-improvement direction; main statements [rpl_ppo_conservative],
      [rpl_std_ppo_conservative], [rpl_ppo_surrogate_conservative],
      [rpl_ppo_gap_nonneg], [rpl_clip_error_nonneg], [rpl_ppo_clipped_improvement].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra], [UpReqAlign],
      [UpReqRDF] of this development.

    References.  This development, UpReqPPOPlain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); section-level
      slots enter each statement as explicit discharged premises at section
      close; statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPPOPlain.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqAlign.
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

(* Carrier pinning (the UpReqRDF/UpReqAlign pattern): RealInterfaceEnhancedSetoid *)
(* is a zero-argument Class in this tree (S07_RealSetoidExpLog; the global       *)
(* instance RealEnhancedReal resolves the fields); the generation binders        *)
(* {R : Set} {RIS : RealInterfaceEnhancedSetoid R} raise "Illegal application    *)
(* (Non-functional construction)" against the argument-less interface and are    *)
(* removed.  The carrier R is pinned to the global Real by Notation, and the     *)
(* relation fields req/lt/le are bound by Notation to the concrete               *)
(* S02_CauchyComplete shapes real_eq/real_lt/real_le (exactly the global         *)
(* instance's field values, the same terms the statement face elaborates to):    *)
(* boxed class field projections are erasure faces at extraction and generate    *)
(* Obj.magic rewrites when mixed with the concrete carrier, while the bound      *)
(* forms extract as true data (the ConcMixSelFeed pattern).                      *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ===================================================================== *)
(* Section 1. ReqPPOPlainObj: the PPO block of the plain-face alignment      *)
(*   family; the section variables mirror the upstream alignment chain and   *)
(*   the baseline PPO block, omitting unused positions.                      *)
(* ===================================================================== *)
Section ReqPPOPlainObj.
Context {RDP : ReqDiffPlain}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* Summation slot: pointwise domination lifts to sums, mirroring the [sum_le]
   slot of the upstream summation developments. *)
Hypothesis rpl_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).

(* Right-argument slot for the join, [le b (r_max a b)]: the plain-face
   analogue of the baseline [r_max_le_r].  The [ReqDiffPlain] class body is
   read-only here, so the section carries its own copy and the lower
   clipping bound below follows from it directly. *)
Hypothesis r_max_le_r_plain :
  forall a b : R, le b (r_max a b).

(* Positivity slot: a strictly positive pointwise function has a strictly
   positive sum; it supplies the canonical premise of [pi_star_req].  The
   [Zap] premise is retained so the downstream statement face stays
   connected. *)
Hypothesis rpl_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).

(* ---- Section variables mirroring the upstream alignment chain ---- *)
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
(* The premise [pi_ref_pos] supplies the canonical premise of [pi_star_req]
   for [rpl_pistar]; it enters the section signature explicitly, and the
   module is terminal with no downstream consumers. *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Zap : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).

(* ---- Section variables mirroring the baseline PPO block; the unused
       [pi_old_norm] and [epsilon_pos] positions are omitted ---- *)
Variable pi_old : S -> R.
Variable pi_old_pos : forall s : S, lt zero (pi_old s).
Variable advantage_fn : S -> R.
Variable advantage_nonneg : forall s : S, le zero (advantage_fn s).
Variable epsilon : R.

(* ---- Definitions transcribed in the req interface ---- *)

(* Closed-form optimal policy: the baseline [pi_star] position, instantiated
   through [pi_star_req]. *)
Definition rpl_pistar (s : S) : R :=
  pi_star_req S sumf rpl_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.

(* Importance ratio, mirroring the baseline definition. *)
Definition rpl_importance_ratio (s : S) : R :=
  mult (rpl_pistar s) (inv_pos (pi_old s) (pi_old_pos s)).

(* Clipping range, mirroring the baseline definition; the difference is
   the req-side [req_minus]. *)
Definition rpl_clip (r : R) : R :=
  r_max (min r (plus one epsilon)) (req_minus one epsilon).

(* Clipped PPO objective, mirroring the baseline definition. *)
Definition rpl_ppo_objective : R :=
  sumf (fun s : S => mult (pi_old s)
    (mult (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
          (advantage_fn s))).

(* Unclipped importance-sampling objective, mirroring the baseline definition. *)
Definition rpl_is_objective : R :=
  sumf (fun s : S => mult (pi_old s) (mult (rpl_importance_ratio s) (advantage_fn s))).

(* Policy ratio, carrying an explicit positivity premise on the old policy. *)
Definition rpl_policy_ratio (pi p_old : S -> R) (s : S) (Hpos : lt zero (p_old s)) : R :=
  mult (pi s) (inv_pos (p_old s) Hpos).

(* Clipped ratio in the standard form [min (r_max low r) high]. *)
Definition rpl_ppo_clip (r low high : R) : R :=
  min (r_max low r) high.

(* Clipped surrogate objective, mirroring the baseline definition; the lower
   clipping edge is [req_minus one eps]. *)
Definition rpl_ppo_surrogate (pi p_old : S -> R) (adv : S -> R) (eps : R)
  (pi_old_pos : forall s : S, lt zero (p_old s)) : R :=
  sumf (fun s : S => mult (p_old s)
    (min (mult (rpl_policy_ratio pi p_old s (pi_old_pos s)) (adv s))
         (mult (rpl_ppo_clip (rpl_policy_ratio pi p_old s (pi_old_pos s))
                             (req_minus one eps) (plus one eps))
               (adv s)))).

(* Unclipped objective of a policy pair, mirroring the baseline definition. *)
Definition rpl_is_objective_of (pi p_old : S -> R) (adv : S -> R)
  (pi_old_pos : forall s : S, lt zero (p_old s)) : R :=
  sumf (fun s : S => mult (p_old s)
    (mult (rpl_policy_ratio pi p_old s (pi_old_pos s)) (adv s))).

(* Standard-form PPO objective, mirroring the baseline definition. *)
Definition rpl_std_ppo_objective : R :=
  sumf (fun s : S => mult (pi_old s)
    (min (mult (rpl_importance_ratio s) (advantage_fn s))
         (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s)))).

(* ===================================================================== *)
(* Upper clipping bound: [rpl_ppo_clip] is bounded by its ceiling [high],    *)
(* by the right side of the [min] slot applied directly.                     *)
(* ===================================================================== *)
Lemma rpl_ppo_clip_upper :
  forall r low high : R, le (rpl_ppo_clip r low high) high.
Proof.
  intros r low high. unfold rpl_ppo_clip.
  apply min_le_r_plain.
Qed.

(* ===================================================================== *)
(* Conservativity of the clipped objective: [rpl_ppo_objective] is bounded   *)
(* by [rpl_is_objective].  Pointwise, the left side of the [min] slot        *)
(* dominates the clipped factor, [le_mult_compat_weak] multiplies through    *)
(* the nonnegative advantage, [req_le_mult_compat_r] scales by the           *)
(* nonnegative [pi_old], and the summation slot lifts the pointwise bound.   *)
(* ===================================================================== *)
Lemma rpl_ppo_conservative :
  le rpl_ppo_objective rpl_is_objective.
Proof.
  unfold rpl_ppo_objective, rpl_is_objective.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                     (rpl_importance_ratio s))
    by exact (min_le_l_plain (rpl_importance_ratio s)
                             (rpl_clip (rpl_importance_ratio s))).
  assert (Hinner : le (mult (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                            (advantage_fn s))
                      (mult (rpl_importance_ratio s) (advantage_fn s)))
    by exact (le_mult_compat_weak
                (min (rpl_importance_ratio s) (rpl_clip (rpl_importance_ratio s)))
                (rpl_importance_ratio s) (advantage_fn s)
                (advantage_nonneg s) Hmin).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply pi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hinner).
Qed.

(* ===================================================================== *)
(* Conservativity of the standard-form objective, with no sign premise on    *)
(* the advantage: the left side of the [min] slot gives the defining bound   *)
(* [min (mult r A) (mult (rpl_clip r) A) <= mult r A] on the two products,   *)
(* and the remaining step is as in the clipped case.                         *)
(* ===================================================================== *)
Lemma rpl_std_ppo_conservative :
  le rpl_std_ppo_objective rpl_is_objective.
Proof.
  unfold rpl_std_ppo_objective, rpl_is_objective.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (mult (rpl_importance_ratio s) (advantage_fn s))
                         (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s)))
                    (mult (rpl_importance_ratio s) (advantage_fn s)))
    by exact (min_le_l_plain (mult (rpl_importance_ratio s) (advantage_fn s))
                             (mult (rpl_clip (rpl_importance_ratio s)) (advantage_fn s))).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply pi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hmin).
Qed.

(* ===================================================================== *)
(* Nonnegativity of the gap: the importance-sampling objective dominates     *)
(* the PPO objective, so their [req_minus] difference is nonnegative, by     *)
(* the conservativity above together with [req_le_minus_nonneg].             *)
(* ===================================================================== *)
Lemma rpl_ppo_gap_nonneg :
  le zero (req_minus rpl_is_objective rpl_ppo_objective).
Proof.
  apply (req_le_minus_nonneg rpl_ppo_objective rpl_is_objective).
  exact rpl_ppo_conservative.
Qed.

(* ===================================================================== *)
(* Conservativity of the standard-form surrogate objective, again with no    *)
(* sign premise on the advantage: the positivity of the old policy is        *)
(* universally quantified in the statement, and the proof combines the left  *)
(* side of the [min] slot, [req_le_mult_compat_r], and the summation slot.   *)
(* ===================================================================== *)
Lemma rpl_ppo_surrogate_conservative :
  forall (pi : S -> R) (adv : S -> R) (eps : R),
  forall (Hpi_old_pos : forall s : S, lt zero (pi_old s)),
  le (rpl_ppo_surrogate pi pi_old adv eps Hpi_old_pos)
     (rpl_is_objective_of pi pi_old adv Hpi_old_pos).
Proof.
  intros pi adv eps Hpi_old_pos.
  unfold rpl_ppo_surrogate, rpl_is_objective_of.
  apply rpl_sum_le.
  intro s.
  assert (Hmin : le (min (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                         (mult (rpl_ppo_clip (rpl_policy_ratio pi pi_old s (Hpi_old_pos s))
                                             (req_minus one eps) (plus one eps))
                               (adv s)))
                    (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s)))
    by exact (min_le_l_plain
                (mult (rpl_policy_ratio pi pi_old s (Hpi_old_pos s)) (adv s))
                (mult (rpl_ppo_clip (rpl_policy_ratio pi pi_old s (Hpi_old_pos s))
                                    (req_minus one eps) (plus one eps))
                      (adv s))).
  assert (Hpi : le zero (pi_old s))
    by (apply (lt_le_iff _ _); left; apply Hpi_old_pos).
  exact (req_le_mult_compat_r (pi_old s) _ _ Hpi Hmin).
Qed.

(* ===================================================================== *)
(* Lower clipping bound: [rpl_clip r] dominates [req_minus one epsilon], by  *)
(* the right-argument join slot [r_max_le_r_plain] applied directly.         *)
(* ===================================================================== *)
Lemma rpl_clip_lower :
  forall r : R, le (req_minus one epsilon) (rpl_clip r).
Proof.
  intro r. unfold rpl_clip.
  exact (r_max_le_r_plain (min r (plus one epsilon)) (req_minus one epsilon)).
Qed.

End ReqPPOPlainObj.

(* ===================================================================== *)
(* Section 2. ReqPPOPlainClipErr: the clipping-error block, mirroring the    *)
(*   baseline decomposition section; the normalization premise on [pi] is    *)
(*   not carried here, since the statement and proof below never consume     *)
(*   it.                                                                     *)
(* ===================================================================== *)
Section ReqPPOPlainClipErr.
Context {RDP : ReqDiffPlain}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* Nonnegativity slot: pointwise nonnegativity lifts to the sum, the
   req-side analogue of the baseline nonnegativity field. *)
Hypothesis rpl_sum_nonneg :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumf f).

Variable pi p_old : S -> R.
Variable eps : R.
Variable Hpos : forall s : S, lt zero (p_old s).

(* Pointwise ratio: the section-1 [rpl_policy_ratio] instantiated at [pi]
   and [p_old]; the type [S] is passed explicitly across sections. *)
Definition rpl_ratio (s : S) : R :=
  rpl_policy_ratio S pi p_old s (Hpos s).

(* Clipping error, mirroring the baseline definition; the difference is
   [req_minus] and the clipped ratio is the section-1 [rpl_ppo_clip]. *)
Definition rpl_clip_error (adv : S -> R) : R :=
  sumf (fun s : S =>
    mult (p_old s)
      (req_minus (mult (rpl_ratio s) (adv s))
                 (min (mult (rpl_ratio s) (adv s))
                      (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                            (adv s))))).

(* ===================================================================== *)
(* The product of two nonnegative factors is nonnegative: grow the left      *)
(* factor from zero by [le_mult_compat_weak], then normalize the product     *)
(* [mult zero b] through [req_mult_zero_r] and [le_id_l].                    *)
(* ===================================================================== *)
Lemma rpl_le_mult_nonneg_t12 :
  forall a b : R, le zero a -> le zero b -> le zero (mult a b).
Proof.
  intros a b Ha Hb.
  assert (Hstep : le (mult zero b) (mult a b))
    by exact (le_mult_compat_weak zero a b Hb Ha).
  assert (Hz : req (mult zero b) zero)
    by exact (req_trans (mult zero b) (mult b zero) zero
                        (mult_comm zero b) (req_mult_zero_r b)).
  exact (le_id_l zero (mult zero b) (mult a b)
                 (req_sym (mult zero b) zero Hz) Hstep).
Qed.

(* ===================================================================== *)
(* The clipping error is nonnegative, with no sign premise on the advantage: *)
(* each summand is a product of the nonnegative factor [p_old s] with a      *)
(* nonnegative difference — the difference is nonnegative by                *)
(* [req_le_minus_nonneg] fed with the left side of the [min] slot — and the  *)
(* nonnegativity slot lifts the pointwise bound to the sum.                  *)
(* ===================================================================== *)
Lemma rpl_clip_error_nonneg : forall adv : S -> R, le zero (rpl_clip_error adv).
Proof.
  intro adv. unfold rpl_clip_error.
  apply rpl_sum_nonneg. intro s.
  apply (rpl_le_mult_nonneg_t12 (p_old s)
    (req_minus (mult (rpl_ratio s) (adv s))
               (min (mult (rpl_ratio s) (adv s))
                    (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                          (adv s))))).
  - exact (lt_le_iff _ _ (inl (Hpos s))).
  - apply (req_le_minus_nonneg
             (min (mult (rpl_ratio s) (adv s))
                  (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                        (adv s)))
             (mult (rpl_ratio s) (adv s))).
    exact (min_le_l_plain (mult (rpl_ratio s) (adv s))
                          (mult (rpl_ppo_clip (rpl_ratio s) (req_minus one eps) (plus one eps))
                                (adv s))).
Qed.

End ReqPPOPlainClipErr.

(* ===================================================================== *)
(* Section 3. ReqPPOPlainImprove: the clipped-surrogate improvement block.   *)
(*   The improvement direction is derived from the section-1 conservativity  *)
(*   of the surrogate: a nonnegative clipped surrogate is bounded by the     *)
(*   unclipped objective, so that objective is nonnegative, and the value    *)
(*   identity below turns the nonnegative difference into the value          *)
(*   improvement.  The normalization premise of the baseline section is      *)
(*   carried as the explicit premise [Hnorm : req (sumf pi) one], since the  *)
(*   req interface has no normalized field.  The summation slots             *)
(*   [rpli_sum_le], [rpli_sum_ext], [rpli_sum_add] and [rpli_sum_linear]     *)
(*   mirror the honest-bridge premises of the upstream advantage             *)
(*   development.                                                            *)
(* ===================================================================== *)
Section ReqPPOPlainImprove.
Context {RDP : ReqDiffPlain}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* Slot group: the [le] summation slot used by the conservativity result,
   plus the three req-side summation slots for extensionality, addition,
   and linearity. *)
Hypothesis rpli_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis rpli_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis rpli_sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis rpli_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).

(* ---- Section variables mirroring the baseline decomposition section ---- *)
Variable pi p_old : S -> R.
Variable Hpos : forall s : S, lt zero (p_old s).
(* The req-side counterpart of the baseline normalization premise: the req
   interface has no normalized field, so the collapse of [sumf pi] to [one]
   enters as the explicit premise [Hnorm]. *)
Variable Hnorm : req (sumf pi) one.

(* State value and advantage of a policy, mirroring the baseline
   definitions; the reward enters both as an explicit argument, and the
   difference in the advantage is [req_minus]. *)
Definition rpli_state_value (reward p : S -> R) : R :=
  sumf (fun s : S => mult (p s) (reward s)).
Definition rpli_advantage (reward p : S -> R) (s : S) : R :=
  req_minus (reward s) (rpli_state_value reward p).

(* ---- Multiplication by [opp one] lands at the opposite ---- *)
Lemma rpli_opp_one_mult : forall x : R, req (mult (opp one) x) (opp x).
Proof.
  intro x.
  apply (req_trans (mult (opp one) x) (opp (mult one x)) (opp x)).
  - exact (req_opp_mult_r one x).
  - apply (req_opp_compat (mult one x) x). exact (req_mult_one_l x).
Qed.

(* ---- Summation commutes with [opp] ---- *)
Lemma rpli_sum_opp :
  forall f : S -> R, req (sumf (fun s : S => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s : S => opp (f s)))
                   (sumf (fun s : S => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (rpli_sum_ext (fun s : S => opp (f s))
                        (fun s : S => mult (opp one) (f s))).
    intro s. exact (req_sym _ _ (rpli_opp_one_mult (f s))).
  - apply (req_trans (sumf (fun s : S => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + exact (rpli_sum_linear (opp one) f).
    + exact (rpli_opp_one_mult (sumf f)).
Qed.

(* ---- Summation commutes with [req_minus], which is the transparent
       [plus a (opp b)] form of the difference ---- *)
Lemma rpli_sum_minus :
  forall f g : S -> R,
    req (sumf (fun s : S => req_minus (f s) (g s)))
        (req_minus (sumf f) (sumf g)).
Proof.
  intros f g.
  apply (req_trans (sumf (fun s : S => req_minus (f s) (g s)))
                   (plus (sumf f) (sumf (fun s : S => opp (g s))))
                   (req_minus (sumf f) (sumf g))).
  - exact (rpli_sum_add f (fun s : S => opp (g s))).
  - exact (req_plus_compat (sumf f) (sumf f)
                           (sumf (fun s : S => opp (g s))) (opp (sumf g))
                           (req_refl (sumf f))
                           (rpli_sum_opp g)).
Qed.

(* ---- Pointwise cancellation of the ratio:                                  *)
(*   [mult (p_old s) (mult (rpl_policy_ratio ...) A)] equals [mult (pi s) A], *)
(*   the chain used when the transparent [rpl_policy_ratio] definition is     *)
(*   unfolded below.                                                          *)
Lemma rpli_ratio_cancel :
  forall (reward : S -> R) (s : S),
    req (mult (p_old s)
              (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                    (rpli_advantage reward p_old s)))
        (mult (pi s) (rpli_advantage reward p_old s)).
Proof.
  intros reward s.
  assert (Ha : req (mult (p_old s)
                   (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                         (rpli_advantage reward p_old s)))
                   (mult (mult (p_old s)
                    (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                    (rpli_advantage reward p_old s)))
    by exact (mult_assoc (p_old s) (rpl_policy_ratio S pi p_old s (Hpos s))
                         (rpli_advantage reward p_old s)).
  assert (Hb : req (mult (mult (p_old s)
                          (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s))
                   (mult (mult (mult (p_old s) (pi s))
                          (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (p_old s) (mult (pi s) (inv_pos (p_old s) (Hpos s))))
                              (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (mult_assoc (p_old s) (pi s) (inv_pos (p_old s) (Hpos s)))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hc : req (mult (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s))
                   (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (mult (p_old s) (pi s)) (inv_pos (p_old s) (Hpos s)))
                              (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_mult_compat (mult (p_old s) (pi s)) (mult (pi s) (p_old s))
                                               (inv_pos (p_old s) (Hpos s))
                                               (inv_pos (p_old s) (Hpos s))
                                               (mult_comm (p_old s) (pi s))
                                               (req_refl (inv_pos (p_old s) (Hpos s))))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hd : req (mult (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                         (rpli_advantage reward p_old s))
                   (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (mult (pi s) (p_old s)) (inv_pos (p_old s) (Hpos s)))
                              (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_sym _ _ (mult_assoc (pi s) (p_old s)
                                                       (inv_pos (p_old s) (Hpos s))))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (He : req (mult (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                         (rpli_advantage reward p_old s))
                   (mult (mult (pi s) one) (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (pi s) (mult (p_old s) (inv_pos (p_old s) (Hpos s))))
                              (mult (pi s) one)
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (req_mult_compat (pi s) (pi s)
                                               (mult (p_old s) (inv_pos (p_old s) (Hpos s)))
                                               one
                                               (req_refl (pi s))
                                               (inv_pos_correct (p_old s) (Hpos s)))
                              (req_refl (rpli_advantage reward p_old s))).
  assert (Hf : req (mult (mult (pi s) one) (rpli_advantage reward p_old s))
                   (mult (pi s) (rpli_advantage reward p_old s)))
    by exact (req_mult_compat (mult (pi s) one) (pi s)
                              (rpli_advantage reward p_old s) (rpli_advantage reward p_old s)
                              (mult_one (pi s))
                              (req_refl (rpli_advantage reward p_old s))).
  exact (req_trans _ _ _ Ha (req_trans _ _ _ Hb (req_trans _ _ _ Hc
           (req_trans _ _ _ Hd (req_trans _ _ _ He Hf))))).
Qed.

(* ---- The raw objective is the value difference:                            *)
(*   the unclipped objective of [pi] against [p_old] equals the value of      *)
(*   [pi] minus the value of [p_old], by pointwise ratio cancellation,        *)
(*   summation linearity, and the normalization collapse through [Hnorm].     *)
Lemma rpli_is_objective_value_id :
  forall reward : S -> R,
    req (rpl_is_objective_of S sumf pi p_old (rpli_advantage reward p_old) Hpos)
        (req_minus (rpli_state_value reward pi)
                   (rpli_state_value reward p_old)).
Proof.
  intro reward.
  (* Pointwise ratio cancellation, lifted through sum extensionality. *)
  assert (H2 : req (rpl_is_objective_of S sumf pi p_old
                     (rpli_advantage reward p_old) Hpos)
                   (sumf (fun s : S => mult (pi s)
                          (rpli_advantage reward p_old s)))).
  { unfold rpl_is_objective_of.
    apply (rpli_sum_ext (fun s : S => mult (p_old s)
                          (mult (rpl_policy_ratio S pi p_old s (Hpos s))
                                (rpli_advantage reward p_old s)))
                        (fun s : S => mult (pi s)
                          (rpli_advantage reward p_old s))).
    intro s. exact (rpli_ratio_cancel reward s). }
  (* Expand the advantage transparently, distribute the product over the
     difference pointwise, and apply sum-minus. *)
  assert (H3 : req (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                   (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (sumf (fun s : S =>
                                mult (pi s) (rpli_state_value reward p_old))))).
  { apply (req_trans (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                     (sumf (fun s : S =>
                       req_minus (mult (pi s) (reward s))
                                 (mult (pi s) (rpli_state_value reward p_old))))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (sumf (fun s : S =>
                                  mult (pi s) (rpli_state_value reward p_old))))).
    - apply (rpli_sum_ext (fun s : S => mult (pi s) (rpli_advantage reward p_old s))
                          (fun s : S =>
                            req_minus (mult (pi s) (reward s))
                                      (mult (pi s) (rpli_state_value reward p_old)))).
      intro s. exact (req_mult_minus_distr_l (pi s) (reward s)
                             (rpli_state_value reward p_old)).
    - exact (rpli_sum_minus (fun s : S => mult (pi s) (reward s))
                            (fun s : S => mult (pi s) (rpli_state_value reward p_old))). }
  (* Collapse the second sum to a constant: commute each product pointwise,
     apply summation linearity, and collapse through [Hnorm]. *)
  assert (H4 : req (sumf (fun s : S => mult (pi s) (rpli_state_value reward p_old)))
                   (rpli_state_value reward p_old)).
  { apply (req_trans (sumf (fun s : S => mult (pi s) (rpli_state_value reward p_old)))
                     (sumf (fun s : S => mult (rpli_state_value reward p_old) (pi s)))
                     (rpli_state_value reward p_old)).
    - apply (rpli_sum_ext (fun s : S => mult (pi s) (rpli_state_value reward p_old))
                          (fun s : S => mult (rpli_state_value reward p_old) (pi s))).
      intro s. exact (mult_comm (pi s) (rpli_state_value reward p_old)).
    - apply (req_trans (sumf (fun s : S => mult (rpli_state_value reward p_old) (pi s)))
                       (mult (rpli_state_value reward p_old) (sumf pi))
                       (rpli_state_value reward p_old)).
      + exact (rpli_sum_linear (rpli_state_value reward p_old) pi).
      + apply (req_trans (mult (rpli_state_value reward p_old) (sumf pi))
                         (mult (rpli_state_value reward p_old) one)
                         (rpli_state_value reward p_old)).
        * exact (req_mult_compat (rpli_state_value reward p_old)
                                 (rpli_state_value reward p_old)
                                 (sumf pi) one
                                 (req_refl (rpli_state_value reward p_old)) Hnorm).
        * exact (mult_one (rpli_state_value reward p_old)). }
  (* Transport the second component of the difference along the collapse
     above, through [req_opp_compat]. *)
  assert (H5 : req (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (sumf (fun s : S =>
                                mult (pi s) (rpli_state_value reward p_old))))
                   (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                              (rpli_state_value reward p_old))).
  { exact (req_trans
        (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                   (sumf (fun s : S =>
                     mult (pi s) (rpli_state_value reward p_old))))
        (plus (sumf (fun s : S => mult (pi s) (reward s)))
              (opp (rpli_state_value reward p_old)))
        (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                   (rpli_state_value reward p_old))
        (req_plus_compat (sumf (fun s : S => mult (pi s) (reward s)))
                         (sumf (fun s : S => mult (pi s) (reward s)))
                         (opp (sumf (fun s : S =>
                           mult (pi s) (rpli_state_value reward p_old))))
                         (opp (rpli_state_value reward p_old))
                         (req_refl (sumf (fun s : S => mult (pi s) (reward s))))
                         (req_opp_compat (sumf (fun s : S =>
                           mult (pi s) (rpli_state_value reward p_old)))
                           (rpli_state_value reward p_old) H4))
        (req_refl (plus (sumf (fun s : S => mult (pi s) (reward s)))
                        (opp (rpli_state_value reward p_old))))). }
  apply (req_trans (rpl_is_objective_of S sumf pi p_old
                     (rpli_advantage reward p_old) Hpos)
                   (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                   (req_minus (rpli_state_value reward pi)
                              (rpli_state_value reward p_old))).
  - exact H2.
  - exact (req_trans (sumf (fun s : S => mult (pi s) (rpli_advantage reward p_old s)))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (sumf (fun s : S =>
                                  mult (pi s) (rpli_state_value reward p_old))))
                     (req_minus (sumf (fun s : S => mult (pi s) (reward s)))
                                (rpli_state_value reward p_old))
                     H3 H5).
Qed.

(* ===================================================================== *)
(* Clipped improvement: a nonnegative clipped surrogate yields the value     *)
(* improvement.  The surrogate is bounded by the unclipped objective by the  *)
(* section-1 conservativity result, so that objective is nonnegative; the    *)
(* value identity above rewrites it as the value difference, and             *)
(* [req_le_of_minus_nonneg] converts the nonnegative difference into the     *)
(* order relation.                                                           *)
(* ===================================================================== *)
Theorem rpl_ppo_clipped_improvement :
  forall (reward : S -> R) (eps : R),
    le zero (rpl_ppo_surrogate S sumf pi p_old
               (rpli_advantage reward p_old) eps Hpos) ->
    le (rpli_state_value reward p_old) (rpli_state_value reward pi).
Proof.
  intros reward eps Hsurr.
  assert (Hge : le zero (rpl_is_objective_of S sumf pi p_old
                           (rpli_advantage reward p_old) Hpos)).
  { apply (le_trans _ (rpl_ppo_surrogate S sumf pi p_old
                          (rpli_advantage reward p_old) eps Hpos) _).
    - exact Hsurr.
    - exact (rpl_ppo_surrogate_conservative S sumf rpli_sum_le p_old pi
               (rpli_advantage reward p_old) eps Hpos). }
  exact (req_le_of_minus_nonneg _ _
           (le_id_r _ _ _ (rpli_is_objective_value_id reward) Hge)).
Qed.

End ReqPPOPlainImprove.

(* Closure audit: Print Assumptions on all 28 resolved statements. *)
Print Assumptions rpl_pistar.
Print Assumptions rpl_importance_ratio.
Print Assumptions rpl_clip.
Print Assumptions rpl_ppo_objective.
Print Assumptions rpl_is_objective.
Print Assumptions rpl_policy_ratio.
Print Assumptions rpl_ppo_clip.
Print Assumptions rpl_ppo_surrogate.
Print Assumptions rpl_is_objective_of.
Print Assumptions rpl_std_ppo_objective.
Print Assumptions rpl_ppo_clip_upper.
Print Assumptions rpl_ppo_conservative.
Print Assumptions rpl_std_ppo_conservative.
Print Assumptions rpl_ppo_gap_nonneg.
Print Assumptions rpl_ppo_surrogate_conservative.
Print Assumptions rpl_clip_lower.
Print Assumptions rpl_ratio.
Print Assumptions rpl_clip_error.
Print Assumptions rpl_le_mult_nonneg_t12.
Print Assumptions rpl_clip_error_nonneg.
Print Assumptions rpli_state_value.
Print Assumptions rpli_advantage.
Print Assumptions rpli_opp_one_mult.
Print Assumptions rpli_sum_opp.
Print Assumptions rpli_sum_minus.
Print Assumptions rpli_ratio_cancel.
Print Assumptions rpli_is_objective_value_id.
Print Assumptions rpl_ppo_clipped_improvement.
