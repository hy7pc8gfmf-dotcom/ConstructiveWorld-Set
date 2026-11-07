(* ConstructiveWorld-Set — strict finite-sum monotonicity in positivity-premise form. *)

(** * abl_sumd_strict: strict finite-sum monotonicity with a positivity
      premise.

    Mission.  [dsu_list_sum_lt_cons] (head-witness strict sum monotonicity,
      cons form) and [dsu_sum_lt_pos] (nonempty-enum slot form): for a
      nonempty list, pointwise strict positivity of [f] plus pointwise
      strict [f < g] imply [sum f < sum g].

    Dependencies.  [UpReqSumD] (finite-sum machine [sumd_list_sum] /
      [sumd_sumf]), [S02_CauchyComplete], [S07_RealSetoidExpLog]; the
      interface is the argument-less Class [RealInterfaceEnhancedSetoid]
      of module [RealInterfaceEnhancedMod].

    References.  This development, [UpReqSumD].v; statement names carried
      over verbatim from the same-name ConstructiveWorld-Main baseline
      module (statement-face Set-carrier completion).  Adaptation to the
      argument-less interface: [R] is [Real] by notation ([UpReqSumD.v]
      L58), the strict-order face is [real_lt] ([UpReqSumD.v] L113-114),
      law fields resolve through [RealEnhancedReal] ([UpReqSumD.v]
      L68-72), and [dsu_neg] is retyped at [Set] as [A -> Empty_set]
      (the world [Not] face, [S01_BaseRing]).

    Constructivity.  All statements are Set-layer; every proof is
      [Qed]-closed with zero admitted items; no new axioms.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      abl_sumd_strict.v] compiles cleanly (exit 0); the first eight bytes
      of the artifact are [436f7121 00015ff4]. *)

Require Import UpReqSumD.
(* [RealInterfaceEnhancedSetoid] and [RealInterfaceEnhancedMod] are defined
   in [S07]; a plain [Require] does not re-export their short names, so
   this file imports the module itself; the [Real] short name is imported
   explicitly by [S02] (already present in the transitive closure, the
   short name serves the notation-rebinding site). *)
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v L58 precedent). *)
Notation R := Real.

(* Set-face negation synonym: carried at [Set] (A -> Empty_set), the world
   Not face (S01_BaseRing); the source piece carried a Prop-typed twin
   against an environment without [Not], this world supplies the Set face
   directly and the named synonym is kept for statement stability. *)
Definition dsu_neg (A : Set) : Set := A -> Empty_set.

(* ============================================================ *)
(* Section DsuStrictSum: strict generic sum monotonicity (positivity      *)
(*   premise form); the section variables mirror the host UpReqSumD       *)
(*   Section SumDischarge shape, and the sum machine is consumed          *)
(*   directly (sumd_list_sum / sumd_sumf, zero rewriting of the           *)
(*   finite-sum definition face).                                         *)
(* ============================================================ *)
Section DsuStrictSum.

Variable S : Set.
Variable enum : list S.

(* ============ station 1: cons form (head-witness strict sum monotone) ==== *)
(* f pointwise strictly positive (positivity-premise form, adjudicated
   shape) + f<g pointwise strict implies the head sum strictly increases.
   Proof: structural induction on the tail list l -- the nil case reduces
   the tail sum to zero, the plus_zero reshaping goes through req_lt_compat
   (req reshaping, zero wall contact); the induction step assembles the
   head strict leg (Hlt x) with the same-head tail IH via the double-strict
   field lt_plus_compat. The generic positivity-free shape lands on the
   RW-MIX mixed-ordering wall (UpReqAlgebra ReqStrictOrderBridge
   forbidden-hard-proof registration); its disposition is out of scope
   here. *)
Lemma dsu_list_sum_lt_cons : forall (f g : S -> R) (x : S) (l : list S),
  (forall s : S, real_lt zero (f s)) ->
  (forall s : S, real_lt (f s) (g s)) ->
  real_lt (sumd_list_sum S f (x :: l)) (sumd_list_sum S g (x :: l)).
Proof.
  intros f g x l Hfp Hlt. revert x.
  induction l as [| y t IH]; intro x.
  - (* nil case: sumd_list_sum reduces to plus _ zero, closed by the
       req_lt_compat reshaping (verified against the source direction note:
       req_lt_compat transports req x1 x2 -> req y1 y2 -> lt x1 y1 ->
       lt x2 y2, so the plus_zero legs enter flipped through req_sym). *)
    simpl.
    exact (req_lt_compat (f x) (plus (f x) zero)
             (g x) (plus (g x) zero)
             (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
             (req_sym (plus (g x) zero) (g x) (plus_zero (g x)))
             (Hlt x)).
  - (* cons case y::t: head strict leg (Hlt x) + same-shape tail IH (y),
       one-shot assembly by the double-strict field lt_plus_compat *)
    exact (lt_plus_compat (f x) (g x)
             (sumd_list_sum S f (y :: t)) (sumd_list_sum S g (y :: t))
             (Hlt x) (IH y)).
Qed.

(* ============ station 2: slot form (nonempty enum, positivity-premise flagship) ============ *)
(* Same datum slot as the host sumd_sum_pos: the nonemptiness premise is an
   explicit slot at the dsu_neg (enum = nil) position (Set-carried
   negation face, same shape and order as the host); the nil branch
   explodes, the cons branch cites station 1 verbatim. *)
Lemma dsu_sum_lt_pos : forall f g : S -> R,
  (forall s : S, real_lt zero (f s)) -> (forall s : S, real_lt (f s) (g s)) ->
  dsu_neg (enum = nil) -> real_lt (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros f g Hfp Hlt Hne.
  unfold sumd_sumf.
  destruct enum as [| x t].
  - destruct (Hne eq_refl).
  - exact (dsu_list_sum_lt_cons f g x t Hfp Hlt).
Qed.

End DsuStrictSum.

(* ============ assumption audit ============ *)
Print Assumptions dsu_list_sum_lt_cons.
Print Assumptions dsu_sum_lt_pos.
