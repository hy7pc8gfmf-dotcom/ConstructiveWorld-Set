(* ========================================================================= *)
(* Module   : abl_tbase_lcsum_feed                                          *)
(* Mission. A generic finite-sum machine over an arbitrary carrier for the  *)
(*            enhanced setoid interface of the Real development: the list   *)
(*            fold [tblc_ltsum], its extensionality / additivity /          *)
(*            linearity laws, and the four-term associativity reshuffle    *)
(*            used by the additivity proof; then the three sum-algebra      *)
(*            feed forms at the [Type] carrier, the same three at the       *)
(*            [Set] carrier, and the strict-positivity feed form at the     *)
(*            cons shape (the head witness carries nonemptiness as data).   *)
(* Dependencies. S01_BaseRing through S07_RealSetoidExpLog (the interface   *)
(*            class and its global instance), UpReqSumD ([sumd_sumf],       *)
(*            [sumd_list_sum_pos_cons]); Stdlib List.                       *)
(* References. The sum-algebra slot faces at [S : Type] and the temperature  *)
(*            slot faces at [S : Set] of the log-free-energy host section,  *)
(*            and the Gibbs-pilot positivity slot of the migration host of  *)
(*            this development; proof shapes follow UpReqSumD.              *)
(* Constructivity. Every predicate position is a Set-valued interface       *)
(*            field ([req], [lt] : Real -> Real -> Set), so each statement  *)
(*            is a Prop-sorted record of Set-carried proofs and extracts    *)
(*            without erasure; proofs are constructive Prop derivations.    *)
(*            Qed closes these pure Prop proof faces only; the single       *)
(*            definition, the fold [tblc_ltsum], stays transparent.  No     *)
(*            Q-level order faces occur, so the decidable Q-order bridge    *)
(*            family is not exercised; no classical logic, no axioms.       *)
(* Build. rocq c -native-compiler no -q -Q <this tree root> ""              *)
(*            abl_tbase_lcsum_feed.v in the piece directory; green verdict  *)
(*            = exit 0, zero error lines, every Print Assumptions Closed,   *)
(*            fresh .vo with the reference magic header.                    *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* ============================================================ *)
(* Generic finite-sum machine.  The interface binder pair            *)
(* {R : Set} {RIS : RealInterfaceEnhancedSetoid R} of the baseline   *)
(* statement faces is carrier-ized away: the class is a              *)
(* zero-argument Class in this tree, the carrier is pinned to the    *)
(* global Real, and the interface fields resolve through the         *)
(* global instance.                                                  *)
(* ============================================================ *)

(* The list fold: the enumerated sum in cons shape, generic in the *)
(* carrier type [S]; Set carriers instantiate directly.            *)
Fixpoint tblc_ltsum (S : Type) (en : list S) (f : S -> R) : R :=
  match en with
  | nil => zero
  | x :: t => plus (f x) (tblc_ltsum S t f)
  end.

(* Extensionality: pointwise interface equality implies the sums are equal. *)
Lemma tblc_ltsum_ext : forall (S : Type) (en : list S) (f g : S -> R),
  (forall s : S, req (f s) (g s)) -> req (tblc_ltsum S en f) (tblc_ltsum S en g).
Proof.
  intros S en f g H. induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl. exact (req_plus_compat (f x) (g x) (tblc_ltsum S t f) (tblc_ltsum S t g) (H x) IH).
Qed.

(* Four-term reshuffle: the single nontrivial rearrangement law the   *)
(* additivity proof needs, as one explicit five-node term chain.      *)
Lemma tblc_plus_shuffle : forall (a b c d : R),
  req (plus (plus a b) (plus c d)) (plus (plus a c) (plus b d)).
Proof.
  intros a b c d.
  apply (req_trans (plus (plus a b) (plus c d)) (plus a (plus b (plus c d)))
           (plus (plus a c) (plus b d))
           (req_sym (plus a (plus b (plus c d))) (plus (plus a b) (plus c d))
                    (plus_assoc a b (plus c d)))).
  apply (req_trans (plus a (plus b (plus c d))) (plus a (plus (plus b c) d))
           (plus (plus a c) (plus b d))
           (req_plus_compat a a (plus b (plus c d)) (plus (plus b c) d)
              (req_refl a) (plus_assoc b c d))).
  apply (req_trans (plus a (plus (plus b c) d)) (plus a (plus (plus c b) d))
           (plus (plus a c) (plus b d))
           (req_plus_compat a a (plus (plus b c) d) (plus (plus c b) d)
              (req_refl a)
              (req_plus_compat (plus b c) (plus c b) d d (plus_comm b c)
                 (req_refl d)))).
  apply (req_trans (plus a (plus (plus c b) d)) (plus a (plus c (plus b d)))
           (plus (plus a c) (plus b d))
           (req_plus_compat a a (plus (plus c b) d) (plus c (plus b d))
              (req_refl a)
              (req_sym (plus c (plus b d)) (plus (plus c b) d)
                       (plus_assoc c b d)))).
  exact (plus_assoc a c (plus b d)).
Qed.

(* Additivity: the fold of the pointwise sum is the sum of the folds. *)
Lemma tblc_ltsum_add : forall (S : Type) (en : list S) (f g : S -> R),
  req (tblc_ltsum S en (fun s : S => plus (f s) (g s)))
      (plus (tblc_ltsum S en f) (tblc_ltsum S en g)).
Proof.
  intros S en f g. induction en as [| x t IH].
  - simpl. exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - simpl.
    exact (req_trans
             (plus (plus (f x) (g x))
                   (tblc_ltsum S t (fun s : S => plus (f s) (g s))))
             (plus (plus (f x) (g x)) (plus (tblc_ltsum S t f) (tblc_ltsum S t g)))
             (plus (plus (f x) (tblc_ltsum S t f)) (plus (g x) (tblc_ltsum S t g)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (tblc_ltsum S t (fun s : S => plus (f s) (g s)))
                (plus (tblc_ltsum S t f) (tblc_ltsum S t g))
                (req_refl (plus (f x) (g x))) IH)
             (tblc_plus_shuffle (f x) (g x) (tblc_ltsum S t f) (tblc_ltsum S t g))).
Qed.

(* Linearity: the fold of the pointwise scaled function is the scaled fold. *)
Lemma tblc_ltsum_linear : forall (S : Type) (en : list S) (a : R) (f : S -> R),
  req (tblc_ltsum S en (fun s : S => mult a (f s))) (mult a (tblc_ltsum S en f)).
Proof.
  intros S en a f. induction en as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - simpl. exact (req_trans
             (plus (mult a (f x)) (tblc_ltsum S t (fun s : S => mult a (f s))))
             (plus (mult a (f x)) (mult a (tblc_ltsum S t f)))
             (mult a (plus (f x) (tblc_ltsum S t f)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (tblc_ltsum S t (fun s : S => mult a (f s))) (mult a (tblc_ltsum S t f))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (tblc_ltsum S t f)))
                (plus (mult a (f x)) (mult a (tblc_ltsum S t f)))
                (distrib a (f x) (tblc_ltsum S t f)))).
Qed.

(* ============================================================ *)
(* Feed forms at the [Type] carrier: the sum-algebra slot faces of   *)
(* the log-free-energy host section, with the slot operator          *)
(* instantiated at [fun f => tblc_ltsum S en f].                     *)
(* ============================================================ *)

Theorem tblc_lcfep_sum_ext :
  forall (S : Type) (en : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (tblc_ltsum S en f) (tblc_ltsum S en g).
Proof.
  intros S en f g H.
  exact (tblc_ltsum_ext S en f g H).
Qed.

Theorem tblc_lcfep_sum_add :
  forall (S : Type) (en : list S) (f g : S -> R),
    req (tblc_ltsum S en (fun s : S => plus (f s) (g s)))
        (plus (tblc_ltsum S en f) (tblc_ltsum S en g)).
Proof.
  intros S en f g.
  exact (tblc_ltsum_add S en f g).
Qed.

Theorem tblc_lcfep_sum_linear :
  forall (S : Type) (en : list S) (a : R) (f : S -> R),
    req (tblc_ltsum S en (fun s : S => mult a (f s))) (mult a (tblc_ltsum S en f)).
Proof.
  intros S en a f.
  exact (tblc_ltsum_linear S en a f).
Qed.

(* ============================================================ *)
(* Feed forms at the [Set] carrier: the same three slot faces        *)
(* specialized to a Set carrier, one named statement per slot.       *)
(* ============================================================ *)

Theorem tblc_lctemp_tsum_ext :
  forall (S : Set) (en : list S) (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (tblc_ltsum S en f) (tblc_ltsum S en g).
Proof.
  intros S en f g H.
  exact (tblc_ltsum_ext S en f g H).
Qed.

Theorem tblc_lctemp_tsum_add :
  forall (S : Set) (en : list S) (f g : S -> R),
    req (tblc_ltsum S en (fun s : S => plus (f s) (g s)))
        (plus (tblc_ltsum S en f) (tblc_ltsum S en g)).
Proof.
  intros S en f g.
  exact (tblc_ltsum_add S en f g).
Qed.

Theorem tblc_lctemp_tsum_linear :
  forall (S : Set) (en : list S) (a : R) (f : S -> R),
    req (tblc_ltsum S en (fun s : S => mult a (f s))) (mult a (tblc_ltsum S en f)).
Proof.
  intros S en a f.
  exact (tblc_ltsum_linear S en a f).
Qed.

(* ============================================================ *)
(* Positivity feed form at the cons shape: the head element          *)
(* witnesses nonemptiness as data, so the statement needs no         *)
(* Prop-level nonemptiness premise.  The operator slot is            *)
(* instantiated at the enumerated sum over [w :: rest].              *)
(* ============================================================ *)

Theorem tblc_sigmig_sum_pos_cons :
  forall (S : Set) (w : S) (rest : list S) (f : S -> R),
    (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S (w :: rest) f).
Proof.
  intros S w rest f H.
  exact (sumd_list_sum_pos_cons S f w rest H).
Qed.

(* ============================================================ *)
(* Assumption audit: one line per statement of this piece.           *)
(* ============================================================ *)

Print Assumptions tblc_ltsum_ext.
Print Assumptions tblc_plus_shuffle.
Print Assumptions tblc_ltsum_add.
Print Assumptions tblc_ltsum_linear.
Print Assumptions tblc_lcfep_sum_ext.
Print Assumptions tblc_lcfep_sum_add.
Print Assumptions tblc_lcfep_sum_linear.
Print Assumptions tblc_lctemp_tsum_ext.
Print Assumptions tblc_lctemp_tsum_add.
Print Assumptions tblc_lctemp_tsum_linear.
Print Assumptions tblc_sigmig_sum_pos_cons.
