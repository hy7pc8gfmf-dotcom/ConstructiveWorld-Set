(* ========================================================================== *)
(*  abl_SecondLaw_inst_11.v -- SecondLawQuantified section assumption       *)
(*  instantiation (sumf := list-sum form; live-tree source read-only).      *)
(*  Mission.: instantiate the five SlqSecondLaw slots (L48-346) with the    *)
(*        sum function concretely read as real_list_sum: the assumption    *)
(*        slots sumpos/sumext/sumlinear/sumadd become provable lemmas;      *)
(*        T_pos is instantiated at T := real_plus real_one real_one (= 2);  *)
(*        S/energy are pure data slots carried by a concrete X.             *)
(*        (a) sumpos positivity needs a non-empty list: the cons-form       *)
(*        precedent of the source resolution block (L590-594) is kept and   *)
(*        the non-empty enumeration form (abl11_sumpos_nonempty, l <> nil   *)
(*        premise slot after source L356/L444; Prop-premise bridge outside  *)
(*        the extraction check group) is derived. (b) T_pos composes        *)
(*        S02:3197 with S07:6967, 0+0==0 transported along S02:2348.        *)
(*        (c) a head witness via real_boltzmann_dist_temp would need the    *)
(*        large S14 module built first (out of the pool under the timeout   *)
(*        discipline); its filler (source L70-73 call shape) is prepared.   *)
(*  Dependencies.: S01_BaseRing S02_CauchyComplete S03_QExp                 *)
(*        S04_RealExpLogConv S05_AlignmentGRPO S06_DiffSamplingGibbs        *)
(*        S07_RealSetoidExpLog S08_RealMainlineDPO; Stdlib List+Extraction. *)
(*  References.: SecondLawQuantified.v (live tree, read-only source);       *)
(*        S08 RealListSumMain section (sum closure lemmas).                 *)
(*  Constructivity.: purely constructive, zero classical steps, all proofs  *)
(*        Qed-closed; no Prop beyond the single registered l <> nil bridge; *)
(*        tail Print Assumptions all Closed; extraction Obj.magic = 0.      *)
(*  Build.: rocq c -native-compiler no -q -Q <seat>/world "" born in place  *)
(*        in that world directory of certified read-only vo copies from    *)
(*        the live tree (single file, gate cap 1, thermal-guard wrapped).  *)
(* ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ============================================================ *)
(*  Structure note: Part 1 gives five machine anchors for the     *)
(*  section slot shapes (source L51-67 re-stated verbatim as      *)
(*  Definitions; type checking = faithful re-statement; S renamed *)
(*  S0 to avoid shadowing, everything else unchanged). Part 2     *)
(*  instantiates the four summation assumption slots (sumpos by   *)
(*  an independent construction chain with zero False            *)
(*  elimination; sumext/sumlinear/sumadd close directly on four   *)
(*  S08 RealListSumMain section library lemmas). Part 3           *)
(*  instantiates T := 2. Part 4 houses the concrete instances in  *)
(*  the anchor shapes (the machine-judged face of the             *)
(*  instantiation).                                               *)
(* ============================================================ *)

(* ============================================================ *)
(* Part 1 - section-shape machine anchors (source                *)
(*   SecondLawQuantified.v L51-67 re-stated verbatim as          *)
(*   Definitions: type checking = faithful re-statement; S       *)
(*   renamed S0 to avoid shadowing, zero other changes).         *)
(* ============================================================ *)

Definition abl11_shape_sumpos (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) -> real_lt real_zero (sumf f).

Definition abl11_shape_sumext (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).

Definition abl11_shape_sumlinear (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (a : Real) (f : S0 -> Real),
    real_eq (sumf (fun s : S0 => real_mult a (f s))) (real_mult a (sumf f)).

Definition abl11_shape_sumadd (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f g : S0 -> Real),
    real_eq (sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (sumf f) (sumf g)).

Definition abl11_shape_T_pos (T0 : Real) := real_lt real_zero T0.

(* ============================================================ *)
(* Part 2 - the sumf instance reading + instantiation of the      *)
(*   four summation assumption slots.                             *)
(*   abl11_sumf X l f := real_list_sum X f l (the S08             *)
(*   RealListSumMain section L281 Fixpoint, first argument X      *)
(*   after the section closed).                                   *)
(* ============================================================ *)

Definition abl11_sumf (X : Type) (l : list X) (f : X -> Real) : Real :=
  real_list_sum X f l.

(* ---- Slot 1 - sumpos (cons-form main instantiation; independent    *)
(*      construction chain, zero False elimination) ------------------- *)
(*   Chain: a single-element list gives f x + 0, transported along    *)
(*   real_plus_zero to f x > 0 (same shape as the S08                 *)
(*   real_list_sum_pos singleton case); for a multi-element list      *)
(*   both summands are positive, hence the sum is positive            *)
(*   (witnessed by S02 real_lt_plus_compat). The nil branch is        *)
(*   never touched (unreachable under the cons form), so the whole    *)
(*   chain has no False elimination and a clean extraction face.      *)
Lemma abl11_listsum_pos_aux : forall (X : Type) (l : list X) (f : X -> Real),
  (forall s : X, real_lt real_zero (f s)) ->
  forall x : X, real_lt real_zero (real_list_sum X f (cons x l)).
Proof.
  intros X l.
  induction l as [| y rest IH]; intros f Hf x; simpl.
  - (* cons x nil: f x + 0 == f x transported along eq (S08 singleton case) *)
    apply (RealSetoid.real_lt_id_r real_zero (f x) (real_plus (f x) real_zero)).
    + apply (real_eq_sym (real_plus (f x) real_zero) (f x)).
      apply (real_plus_zero (f x)).
    + exact (Hf x).
  - (* cons x (y::rest): 0+0 < f x + (f y + sum rest), lower bound      *)
    (* transported along plus_zero                                      *)
    apply (RealSetoid.real_lt_compat
             (real_plus real_zero real_zero) real_zero
             (real_plus (f x) (real_plus (f y) (real_list_sum X f rest)))
             (real_plus (f x) (real_plus (f y) (real_list_sum X f rest)))).
    + exact (real_plus_zero real_zero).
    + apply real_eq_refl.
    + exact (real_lt_plus_compat real_zero (f x) real_zero
               (real_plus (f y) (real_list_sum X f rest)) (Hf x) (IH f Hf y)).
Qed.

Theorem abl11_sumpos : forall (X : Type) (f : X -> Real) (x : X) (l : list X),
  (forall s : X, real_lt real_zero (f s)) ->
  real_lt real_zero (abl11_sumf X (cons x l) f).
Proof.
  intros X f x l Hf.
  unfold abl11_sumf.
  exact (abl11_listsum_pos_aux X l f Hf x).
Qed.

(* Slot 1 completion - derivation of the position left open by the    *)
(*   source resolution block: the arbitrary non-empty enumeration     *)
(*   form (l <> nil premise slot, same statement-face precedent as    *)
(*   the source Part 2 main theorems L356/L444; a Prop-premise        *)
(*   carrying bridge, not in the extraction check group).             *)
Theorem abl11_sumpos_nonempty : forall (X : Type) (l : list X) (f : X -> Real),
  l <> nil ->
  (forall s : X, real_lt real_zero (f s)) ->
  real_lt real_zero (abl11_sumf X l f).
Proof.
  intros X l f Hnn Hf.
  destruct l as [| x l0].
  - exfalso. exact (Hnn eq_refl).
  - unfold abl11_sumf. exact (abl11_listsum_pos_aux X l0 f Hf x).
Qed.

(* ---- Slot 2 - sumext (closed directly by the S08:296 pointwise     *)
(*      extension lemma) --------------------------------------------- *)
Theorem abl11_sumext : forall (X : Type) (l : list X) (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (abl11_sumf X l f) (abl11_sumf X l g).
Proof.
  intros X l f g H.
  unfold abl11_sumf.
  exact (real_list_sum_ext X f g l H).
Qed.

(* ---- Slot 3 - sumlinear (closed directly by the S08:363            *)
(*      coefficient extraction lemma) -------------------------------- *)
Theorem abl11_sumlinear : forall (X : Type) (l : list X) (a : Real) (f : X -> Real),
  real_eq (abl11_sumf X l (fun s : X => real_mult a (f s)))
          (real_mult a (abl11_sumf X l f)).
Proof.
  intros X l a f.
  unfold abl11_sumf.
  exact (real_list_sum_linear X a f l).
Qed.

(* ---- Slot 4 - sumadd (closed directly by the S08:341 pointwise     *)
(*      addition lemma) ---------------------------------------------- *)
Theorem abl11_sumadd : forall (X : Type) (l : list X) (f g : X -> Real),
  real_eq (abl11_sumf X l (fun s : X => real_plus (f s) (g s)))
          (real_plus (abl11_sumf X l f) (abl11_sumf X l g)).
Proof.
  intros X l f g.
  unfold abl11_sumf.
  exact (real_list_sum_add X f g l).
Qed.

(* ============================================================ *)
(* Part 3 - slot 5 - T_pos (instantiated at the concrete T := 2   *)
(*   reading). two := real_plus real_one real_one; 0+0 < 1+1 by   *)
(*   the additive composition of two real_lt_zero_one arms        *)
(*   (S02:3197), the 0+0==0 side transported along S02:2348.      *)
(* ============================================================ *)

Definition abl11_T : Real := real_plus real_one real_one.

Theorem abl11_T_pos : real_lt real_zero abl11_T.
Proof.
  unfold abl11_T.
  apply (RealSetoid.real_lt_compat (real_plus real_zero real_zero) real_zero
           (real_plus real_one real_one) (real_plus real_one real_one)).
  - exact (real_plus_zero real_zero).
  - apply real_eq_refl.
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Part 4 - fillers: the concrete instances inhabit the section   *)
(*   shape anchors (the machine-judged face of the               *)
(*   instantiation). The five filler Definitions are exactly the  *)
(*   Part 1 anchor shapes instantiated at sumf := abl11_sumf X l  *)
(*   and T := abl11_T -- type checking = the concrete reading     *)
(*   satisfies the section assumption shapes verbatim (the        *)
(*   machine proof of the shape correspondence). Definition       *)
(*   bodies (no Qed; type checking is their verification).        *)
(* ============================================================ *)

Definition abl11_fill_sumpos (X : Type) (x : X) (l : list X) :
  abl11_shape_sumpos X (abl11_sumf X (cons x l)) :=
  fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
    abl11_sumpos X f x l Hf.

Definition abl11_fill_sumext (X : Type) (l : list X) :
  abl11_shape_sumext X (abl11_sumf X l) :=
  fun (f g : X -> Real) (H : forall s : X, real_eq (f s) (g s)) =>
    abl11_sumext X l f g H.

Definition abl11_fill_sumlinear (X : Type) (l : list X) :
  abl11_shape_sumlinear X (abl11_sumf X l) :=
  fun (a : Real) (f : X -> Real) => abl11_sumlinear X l a f.

Definition abl11_fill_sumadd (X : Type) (l : list X) :
  abl11_shape_sumadd X (abl11_sumf X l) :=
  fun (f g : X -> Real) => abl11_sumadd X l f g.

Definition abl11_fill_T_pos : abl11_shape_T_pos abl11_T := abl11_T_pos.

(* ============================================================ *)
(* Final audit - assumption face + extraction check               *)
(*   Reconciliation triple: theorem name list 7 = Qed count 7 =   *)
(*   Print Assumptions lines 7, zero discrepancy.                 *)
(*   Theorems 7: abl11_listsum_pos_aux / abl11_sumpos /           *)
(*           abl11_sumpos_nonempty / abl11_sumext /               *)
(*           abl11_sumlinear / abl11_sumadd / abl11_T_pos         *)
(*   Definitions 12 (no Qed; type checking is the verification):  *)
(*           abl11_sumf / five shape anchors / five fillers /     *)
(*           abl11_T.                                             *)
(* ============================================================ *)

Print Assumptions abl11_listsum_pos_aux.
Print Assumptions abl11_sumpos.
Print Assumptions abl11_sumpos_nonempty.
Print Assumptions abl11_sumext.
Print Assumptions abl11_sumlinear.
Print Assumptions abl11_sumadd.
Print Assumptions abl11_T_pos.

(* Extraction check group (six commands; criterion = merged output   *)
(* Obj.magic count 0): the five main instantiation pieces + the      *)
(* sumf anchor (pure Fixpoint). The Hnil bridge is not in the        *)
(* group (registered in the header).                                 *)
Recursive Extraction abl11_sumf.
Recursive Extraction abl11_sumpos.
Recursive Extraction abl11_sumext.
Recursive Extraction abl11_sumlinear.
Recursive Extraction abl11_sumadd.
Recursive Extraction abl11_T_pos.
