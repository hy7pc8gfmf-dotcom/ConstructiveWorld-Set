(* ========================================================================= *)
(* Module   : abl_dtpt_dig_supply                                           *)
(* Mission. one supply theorem per premise slot of the Dig coding-tree      *)
(*            theory DTPT_DigTheory: constructor-injection supply forms     *)
(*            for the seven code constructors (slots 1-8), the              *)
(*            nonempty-list witness for the list-size positivity premise    *)
(*            (slot 9), the diagonal witness for the numeric-projection     *)
(*            round trip (slot 10), numeric-domain decision pins on the     *)
(*            numeric probe (slots 11-15), and decidable size, equality-    *)
(*            decision and proper-subterm pins over the zero probe and its  *)
(*            pair witness (slots 16-22).  Each statement names one        *)
(*            decidable instance of the corresponding host premise, so a    *)
(*            consumer can feed the host lemma and reach its conclusion.    *)
(* Dependencies. DTPT (Dig inductive, Set-valued Id, boolean NatLe),        *)
(*            DTPT_DigTheory (host theory), LW0LeibWindow (leiblw_Id);      *)
(*            Stdlib QArith.QArith, List, Bool, Arith.                      *)
(* References. LW0LeibWindow.v :66 (leiblw_Id shape); DTPT.v :28/:39        *)
(*            (Id, NatLe of the QeqT carrier family); DTPT_DigTheory.v      *)
(*            (host statements fed by the supplies below).                  *)
(* Constructivity. all 22 statements are Set-sorted with zero Prop          *)
(*            components: equality positions use the Set-valued identity    *)
(*            faces (leiblw_Id on Type carriers, Id on Set carriers), the   *)
(*            natural-order positions use NatLe, and the nonemptiness       *)
(*            witness replaces the Prop negation by the transparent         *)
(*            boolean test dig_l_neb; every proof uses only definitional    *)
(*            reduction and identity elimination, so every constant is      *)
(*            closed transparently by Defined -- no Prop-sorted statement   *)
(*            occurs; zero axioms/admits, no classical logic, no vm_compute.*)
(* Build. rocq c -native-compiler no -q -Q <Set world root> "" single shot. *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool Arith.
Require Import LW0LeibWindow.
Require DTPT.
Require DTPT_DigTheory.
Import ListNotations.
Import DTPT.DTPT.
Import DTPT_DigTheory.DTPT_DigTheory.

(* Transparent boolean nonemptiness test on a list of codes: the
   decidable Set carrier standing in for the negated-equality premise
   of the host list-size positivity statement. *)
Definition dig_l_neb (l : list Dig) : bool :=
  match l with
  | [] => false
  | _ :: _ => true
  end.

(* ============ Section 1. constructor-injection supply forms (slots 1-8) ============ *)

(* Feeds the premise of the host injection lemma dig_inj_dQ: a
   Set-valued identity between the numeric arguments yields a
   Set-valued identity between the wrapped codes. *)
Theorem tdg_dig_inj_dQ_h1 : forall x y : Q, Id x y -> leiblw_Id (dQ x) (dQ y).
Proof.
  intros x y H. destruct H. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dPair: component identities yield the
   identity of the pair codes. *)
Theorem tdg_dig_inj_dPair_h1 : forall a b c d : Dig,
  leiblw_Id a c -> leiblw_Id b d -> leiblw_Id (dPair a b) (dPair c d).
Proof.
  intros a b c d H1 H2. destruct H1. destruct H2. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dSeq: list identities yield the
   identity of the sequence codes. *)
Theorem tdg_dig_inj_dSeq_h1 : forall l1 l2 : list Dig,
  leiblw_Id l1 l2 -> leiblw_Id (dSeq l1) (dSeq l2).
Proof.
  intros l1 l2 H. destruct H. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dCode: slot-depth and table identities
   yield the identity of the code-table nodes. *)
Theorem tdg_dig_inj_dCode_h1 : forall (n m : nat) (f g : nat -> Dig),
  leiblw_Id n m -> leiblw_Id f g -> leiblw_Id (dCode n f) (dCode m g).
Proof.
  intros n m f g Hn Hf. destruct Hn. destruct Hf. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dCode_pointwise: same supply shape as
   the previous slot, one statement per host lemma. *)
Theorem tdg_dig_inj_dCode_pointwise_h1 : forall (n m : nat) (f g : nat -> Dig),
  leiblw_Id n m -> leiblw_Id f g -> leiblw_Id (dCode n f) (dCode m g).
Proof.
  intros n m f g Hn Hf. destruct Hn. destruct Hf. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dJudge. *)
Theorem tdg_dig_inj_dJudge_h1 : forall a b c d : Dig,
  leiblw_Id a c -> leiblw_Id b d -> leiblw_Id (dJudge a b) (dJudge c d).
Proof.
  intros a b c d H1 H2. destruct H1. destruct H2. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dModel. *)
Theorem tdg_dig_inj_dModel_h1 : forall a b : Dig,
  leiblw_Id a b -> leiblw_Id (dModel a) (dModel b).
Proof.
  intros a b H. destruct H. apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_inj_dProofT. *)
Theorem tdg_dig_inj_dProofT_h1 : forall a b c d : Dig,
  leiblw_Id a c -> leiblw_Id b d -> leiblw_Id (dProofT a b) (dProofT c d).
Proof.
  intros a b c d H1 H2. destruct H1. destruct H2. apply leiblw_id_intro.
Defined.

(* ============ Section 2. size, projection and numericity supplies (slots 9-15) ============ *)

(* Feeds the nonemptiness premise of dig_lsize_pos: a cons list is
   never empty, witnessed by the boolean test reducing to true. *)
Theorem tdg_dig_lsize_pos_h1 : forall (x : Dig) (l : list Dig),
  leiblw_Id (dig_l_neb (x :: l)) true.
Proof.
  intros x l. apply leiblw_id_intro.
Defined.

(* Feeds the shape premise of dig_Q_roundtrip at the diagonal instance
   d := dQ x: the wrapping of a numeric value is reflexive. *)
Theorem tdg_dig_Q_roundtrip_h1 : forall x : Q, leiblw_Id (dQ x) (dQ x).
Proof.
  intros x. apply leiblw_id_intro.
Defined.

(* Feeds the premise of is_num_inv (is_num (dQ x) = true): the numeric
   branch of the decision reduces to true on the numeric probe. *)
Theorem tdg_is_num_inv_h1 : forall x : Q, leiblw_Id (is_num (dQ x)) true.
Proof.
  intros x. apply leiblw_id_intro.
Defined.

(* Feeds the premise of is_num_inv_sigT: same shape, one statement per
   host lemma. *)
Theorem tdg_is_num_inv_sigT_h1 : forall x : Q, leiblw_Id (is_num (dQ x)) true.
Proof.
  intros x. apply leiblw_id_intro.
Defined.

(* Feeds the premise of is_num_false_not_dQ at the instance
   d := dSeq []: the empty sequence leaves the numeric domain, and the
   decision reduces to false. *)
Theorem tdg_is_num_false_not_dQ_h1 : leiblw_Id (is_num (dSeq [])) false.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the premise of dig_Q_default0: same shape, one statement per
   host lemma. *)
Theorem tdg_dig_Q_default0_h1 : leiblw_Id (is_num (dSeq [])) false.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the premise of is_num_size1: same shape, one statement per
   host lemma. *)
Theorem tdg_is_num_size1_h1 : forall x : Q, leiblw_Id (is_num (dQ x)) true.
Proof.
  intros x. apply leiblw_id_intro.
Defined.

(* ============ Section 3. decision and subterm pins (slots 16-22) ============ *)

(* Feeds the size premise of dig_eqb_size_bound at the instance
   a := dQ 0, n := 1: the numeric probe has size one, carried by the
   boolean order NatLe. *)
Theorem tdg_dig_eqb_size_bound_h1 : NatLe (dig_size (dQ 0%Q)) 1.
Proof.
  exact (NatLe_refl 1).
Defined.

(* Feeds the equality-decision premise of dig_eqb_size_bound at the
   diagonal numeric pair (dQ 0, dQ 0): the matcher reduces to true. *)
Theorem tdg_dig_eqb_size_bound_h2 : leiblw_Id (dig_eqb (dQ 0%Q) (dQ 0%Q)) true.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the size premise of sub_dig_size_bound at the instance
   d := dQ 0, n := 1: same size pin, one statement per host lemma. *)
Theorem tdg_sub_dig_size_bound_h1 : NatLe (dig_size (dQ 0%Q)) 1.
Proof.
  exact (NatLe_refl 1).
Defined.

(* Feeds the subterm-decision premise of sub_dig_size_bound at the
   witness pair (dQ 0) a proper subterm of (dPair (dQ 0) (dQ 0)): the
   proper-subterm test reduces to true. *)
Theorem tdg_sub_dig_size_bound_h2 :
  leiblw_Id (sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q))) true.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the subterm-decision premise of sub_dig_size_mono: same
   witness, one statement per host lemma. *)
Theorem tdg_sub_dig_size_mono_h1 :
  leiblw_Id (sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q))) true.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the subterm-decision premise of sub_dig_size_lt: same
   witness, one statement per host lemma. *)
Theorem tdg_sub_dig_size_lt_h1 :
  leiblw_Id (sub_dig (dQ 0%Q) (dPair (dQ 0%Q) (dQ 0%Q))) true.
Proof.
  apply leiblw_id_intro.
Defined.

(* Feeds the decision premise of is_num_h_alg1: same numeric probe
   pin, one statement per host lemma. *)
Theorem tdg_is_num_h_alg1_h1 : forall x : Q, leiblw_Id (is_num (dQ x)) true.
Proof.
  intros x. apply leiblw_id_intro.
Defined.

(* ============ Assumption audit: one Print Assumptions per supply theorem ============ *)

Print Assumptions tdg_dig_inj_dQ_h1.
Print Assumptions tdg_dig_inj_dPair_h1.
Print Assumptions tdg_dig_inj_dSeq_h1.
Print Assumptions tdg_dig_inj_dCode_h1.
Print Assumptions tdg_dig_inj_dCode_pointwise_h1.
Print Assumptions tdg_dig_inj_dJudge_h1.
Print Assumptions tdg_dig_inj_dModel_h1.
Print Assumptions tdg_dig_inj_dProofT_h1.
Print Assumptions tdg_dig_lsize_pos_h1.
Print Assumptions tdg_dig_Q_roundtrip_h1.
Print Assumptions tdg_is_num_inv_h1.
Print Assumptions tdg_is_num_inv_sigT_h1.
Print Assumptions tdg_is_num_false_not_dQ_h1.
Print Assumptions tdg_dig_Q_default0_h1.
Print Assumptions tdg_is_num_size1_h1.
Print Assumptions tdg_dig_eqb_size_bound_h1.
Print Assumptions tdg_dig_eqb_size_bound_h2.
Print Assumptions tdg_sub_dig_size_bound_h1.
Print Assumptions tdg_sub_dig_size_bound_h2.
Print Assumptions tdg_sub_dig_size_mono_h1.
Print Assumptions tdg_sub_dig_size_lt_h1.
Print Assumptions tdg_is_num_h_alg1_h1.
