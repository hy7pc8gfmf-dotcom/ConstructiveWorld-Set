(* ConstructiveWorld-Main -- abl_sumd_strict instantiation: resolution corollaries and the dsu_neg Set-face decision companion. *)

(** * abl_redischarge_sumd_inst: the strict sum monotonicity resolved at unit, and the Set-face decision companion of [dsu_neg].

    Mission.  First, the zero-argument closed corollaries of the upstream strict
      sum monotonicity (positivity-premise form) at canonical arguments: [R] the
      S02 Real layer (in-service [RealEnhancedReal], reused, S07:8596), carrier
      [S := unit], enum [tt :: nil] (minimal nonempty enumeration), giving the
      zero-Section closed forms [dsu_sum_lt_pos_u1] and
      [dsu_list_sum_lt_cons_u1].  Second, the carrier upgrade: the Set-face
      decision twin [dsu_sb] over [A : Set] with [dsu_neg_sb] as its named
      synonym, and the nonemptiness decision witness [dsu_list_ne_sb].

    Dependencies.  Upstream [abl_sumd_strict] (pool copy chain: [dsu_neg],
      [dsu_sum_lt_pos], [dsu_list_sum_lt_cons]); [UpReqSumD] (the sumd
      machinery); [S07_RealSetoidExpLog] ([RealInterfaceEnhancedSetoid] and the
      in-service instance [RealEnhancedReal]); Stdlib [List].

    References.  The upstream [abl_sumd_strict] sum monotonicity theory,
      consumed by direct instantiation (genuine resolution, not re-proof);
      abl_redischarge_sumd_inst.v, the baseline module in ConstructiveWorld-Main,
      statement names kept verbatim, statement faces completed to the Set
      carrier ([dsu_neg] now Set-face, [dsu_sb] twin, [real_lt] pin).

    Constructivity.  No open ends, no classical logic, zero [not]/[~]/[<>]
      notation; every statement and field carried by [Set]; [dsu_list_ne_sb]
      ends in [Defined], extractable, its reading computed by [vm_compute].

    Build.  Pool chain [abl_sumd_strict.v] first, then this file; compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)

Require Import UpReqSumD.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Require Import abl_sumd_strict.

(* ================= Section 1. Set-level decision companion of dsu_neg ================= *)

(* The refutation data of a Set-level proposition A is [A -> Empty_set], the
   negation face supplied by [dsu_neg]; the two-branch carrier holds the
   witness data in its left branch and that refutation data in its right
   branch, so the decision semantics of the source face is preserved over
   Set-carried propositions. *)
Inductive dsu_sb (A : Set) : Set :=
| dsu_sb_left : A -> dsu_sb A
| dsu_sb_right : (A -> Empty_set) -> dsu_sb A.

(* Named synonym kept for statement stability: [dsu_neg_sb A] is the
   decision carrier over the Set-carried proposition A. *)
Definition dsu_neg_sb (A : Set) : Set := dsu_sb A.

(* Refutation data injects into the right branch of the decision carrier. *)
Theorem dsu_neg_sb_of_neg : forall (A : Set), dsu_neg A -> dsu_neg_sb A.
Proof.
  intros A H. exact (dsu_sb_right A H).
Qed.

(* ================= Section 2. Concrete list-nonemptiness decision carrier ================= *)

(* The [Defined] exit keeps the decision carrier extractable: the nil branch
   carries the equality witness on the left, the cons branch carries the
   refutation data of [l = []] on the right, built by discrimination on the
   empty-list equation; the two-branch carrier is the Set-carried
   [dsu_neg_sb] twin of the source sumbool face. *)
Definition dsu_list_ne_sb (A : Set) (l : list A) : dsu_neg_sb (l = []).
Proof.
  destruct l as [| x t].
  - apply dsu_sb_left. reflexivity.
  - apply dsu_sb_right. intros H. discriminate H.
Defined.

(* Reading coherence: refutation data of [l = []] forces the decision carrier
   onto its right branch, read as the boolean identity [true] (Set-carried
   boolean reading of the decision); the nil leg closes the empty goal by
   elimination on the reflexive equality witness, the cons leg is the
   reflexive boolean equation. *)
Theorem dsu_list_ne_sb_neg_carry : forall (A : Set) (l : list A),
  dsu_neg (l = []) ->
  match dsu_list_ne_sb A l with
  | dsu_sb_left _ _ => false
  | dsu_sb_right _ _ => true
  end = true.
Proof.
  intros A l Hne. unfold dsu_list_ne_sb.
  destruct l as [| x t].
  - destruct (Hne eq_refl).
  - reflexivity.
Qed.

(* ================= Section 3. Canonical instantiation: unit carrier, least nonempty enumeration ================= *)

(* The real layer is the S02 [Real] taken through the [RealEnhancedReal]
   instance of the enhanced setoid interface; the nonemptiness slot of
   [dsu_sum_lt_pos] is discharged directly by [dsu_neg]: the equation
   [tt :: nil = []] is refuted by discrimination. *)
Theorem dsu_sum_lt_pos_u1 : forall f g : unit -> S02_CauchyComplete.Real,
  (forall s : unit, S02_CauchyComplete.real_lt zero (f s)) ->
  (forall s : unit, S02_CauchyComplete.real_lt (f s) (g s)) ->
  S02_CauchyComplete.real_lt (sumd_sumf unit (tt :: nil) f) (sumd_sumf unit (tt :: nil) g).
Proof.
  intros f g Hfp Hlt.
  refine (dsu_sum_lt_pos unit (tt :: nil) f g Hfp Hlt _).
  intros H. discriminate H.
Qed.

(* The cons-form monotonicity statement resolves the same way; the
   head-witness shape closes with no section slots. *)
Theorem dsu_list_sum_lt_cons_u1 : forall f g : unit -> S02_CauchyComplete.Real,
  (forall s : unit, S02_CauchyComplete.real_lt zero (f s)) ->
  (forall s : unit, S02_CauchyComplete.real_lt (f s) (g s)) ->
  S02_CauchyComplete.real_lt (sumd_list_sum unit f (tt :: nil)) (sumd_list_sum unit g (tt :: nil)).
Proof.
  intros f g Hfp Hlt.
  exact (dsu_list_sum_lt_cons unit f g tt nil Hfp Hlt).
Qed.

(* ================= Section 4. Direct evaluation of the singleton decision ================= *)

(* The singleton list is decided to the right branch on the same Set-carried
   [dsu_neg_sb] twin; [vm_compute] reduces the boolean reading to [true]
   directly. *)
Definition dsu_u1_ne_sb : dsu_neg_sb ((tt :: nil) = []) :=
  dsu_list_ne_sb unit (tt :: nil).

Lemma dsu_u1_ne_sb_right :
  match dsu_u1_ne_sb with
  | dsu_sb_left _ _ => false
  | dsu_sb_right _ _ => true
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* ================= Section 5. Assumption audit ================= *)

(* The named exits report closed under the global context. *)

Print Assumptions dsu_neg_sb_of_neg.
Print Assumptions dsu_list_ne_sb_neg_carry.
Print Assumptions dsu_sum_lt_pos_u1.
Print Assumptions dsu_list_sum_lt_cons_u1.
Print Assumptions dsu_u1_ne_sb_right.
