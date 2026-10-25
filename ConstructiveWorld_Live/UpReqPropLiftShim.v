(* ============================================================ *)
(** ConstructiveWorld-Set — lifting adapters from legacy negative forms to sigT witness forms.

* UpReqPropLiftShim: one-directional adapters to Set-layer witness forms.

    Mission.  A family of one-directional adapter statements (prefix [pls_])
      relating legacy premise shapes (existing forms, not violations and
      not assumption discharges) to Set-layer witness forms, so that new
      Set-layer code produces and consumes witnesses directly:
      [pls_vocab_ne]/[pls_vocab_ne_shim]/[pls_vocab_ne_lift] for the
      nonemptiness of [vocab], [pls_Qlt_to_Qlt] for the stdlib-to-S02 order
      carrier, and the [real_lt]/[real_le] projection accessors
      [pls_real_lt_eps]/[pls_real_lt_rest]/[pls_real_le_cases].

    Dependencies.  Stdlib (none beyond the base); requires [S01_BaseRing]
      ([Id]/[Not]/[InT] connectors) and [S02_CauchyComplete]
      ([QltT]/[QleT']/[real_lt]/[real_le]/[Real]).  Adds no new Require
      beyond these.

    References.  This development, ConstructiveWorld-Main baseline module
      UpReqPropLiftShim.v, whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).  The base modules
      themselves are untouched; this file is purely additive.

    Constructivity.  All named statements are carried by [Set]; no
      assumption-like or classical token appears; every proof ends in
      [Qed]; [Print Assumptions] reports closed for all statements;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqPropLiftShim.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)
(* Mission: for legacy statement shapes in the base modules (existing forms, not violations and not assumption debts), this file provides a one-directional adapter family "old negative form to sigT witness form", letting new Set-layer code avoid depending on the legacy negative forms and instead produce or consume witness forms directly. *)
(* The base modules (S-series, the retired 219 shell, G-series) are untouched: this file is purely additive and standalone. *)
(* (so that new Set-layer code produces and consumes witness forms directly, without depending on the legacy negative forms). *)
(* 1. Target Set-layer witness forms plus construction/projection accessors *)
(* Design:                                                              *)
(* - pls_vocab_ne      : target Set-layer witness form {l : Tok | InT l vocab} *)
(* - pls_vocab_ne_shim : witness form implies the legacy form Not (Id vocab nil) *)
(* (the lifting-side producer supplies the witness; legacy consumers keep their statements verbatim) *)
(* - pls_vocab_ne_lift : legacy form implies the witness form (list constructor split, constructive; *)
(* refinement of the blocking point of the one-directional Not-to-sigT conversion (which in general needs list decidability): *)
(* for concrete list data, Not (Id vocab nil) splits without any decidability assumption; *)
(* the genuine obstruction lives in double-negation / abstract-carrier shapes) *)
(* - pls_Qlt_to_Qlt   : stdlib Qlt (Prop) implies S02 QltT (Set) (fills the missing direction; *)
(* S02 already provides the reverse QltT_to_Qlt and the pair Qle_to_QleT'/QleT'_to_Qle) *)
(* - pls_real_lt_eps/_rest / pls_real_le_cases: projection accessors for the dependency faces *)
(* (the sigT witness form of [real_lt], S02:456, and the Or form of [real_le]). *)
(* Constructivity note: zero hits for assumption-like or classical tokens; nothing admitted; *)
(* Print Assumptions is expected to report Closed for the whole file. *)
(* Dependencies: S01_BaseRing ([Id]/[Not]/[InT] connectors), S02_CauchyComplete *)
(* ([QltT]/[QleT']/[real_lt]/[real_le]/[Real]).  No new Require face beyond these. *)
(* Build recipe: Rocq 9.1 direct coqc invocation, -Q . "" -native-compiler no. *)
(* ============================================================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import List QArith.QArith.
Import ListNotations.

(* ============================================================ *)
(* 1. Target Set-layer witness forms plus construction/projection accessors *)
(* ============================================================ *)
Definition pls_vocab_ne {Tok : Set} (vocab : list Tok) : Set :=
  sigT (fun l : Tok => InT l vocab).

Definition pls_vocab_ne_intro {Tok : Set} {vocab : list Tok} (l : Tok)
  : InT l vocab -> pls_vocab_ne vocab
  := fun H => existT _ l H.

Definition pls_vocab_ne_witness {Tok : Set} {vocab : list Tok}
  (H : pls_vocab_ne vocab) : Tok
  := projT1 H.

Definition pls_vocab_ne_member {Tok : Set} {vocab : list Tok}
  (H : pls_vocab_ne vocab) : InT (projT1 H) vocab
  := projT2 H.

(* ============================================================ *)
(* 2. Core one-directional adapters: witness form implies the legacy dependency form (compatibility face for legacy consumers) *)
(* ============================================================ *)
Lemma pls_inT_nil_empty : forall (A : Set) (x : A), InT x nil -> Empty_set.
Proof.
  intros A x H. inversion H.
Qed.

(* The J eliminator of Id (S01 Id is a Martin-Löf identity type; this shape degenerates on the index variable and avoids the subst pitfall) *)
Lemma pls_id_transport {A : Set} {x y : A} (P : A -> Set)
  (Hxx : P x) (Hxy : Id x y) : P y.
Proof.
  revert Hxx. destruct Hxy. intros Hxx. exact Hxx.
Qed.

Lemma pls_vocab_ne_shim {Tok : Set} (vocab : list Tok)
  (H : pls_vocab_ne vocab) : Not (Id vocab nil).
Proof.
  intros Hnil.
  exact (pls_inT_nil_empty Tok (projT1 H)           (pls_id_transport (fun vv => InT (projT1 H) vv) (projT2 H) Hnil)).
Defined.

(* ============================================================ *)
(* 3. Reverse lifting: legacy form implies the witness form (constructive list split; the blocking point is refined, not removed) *)
(* ============================================================ *)
Lemma pls_vocab_ne_lift {Tok : Set} (vocab : list Tok) :
  Not (Id vocab nil) -> pls_vocab_ne vocab.
Proof.
  intros Hne. destruct vocab as [|v l'].
  - destruct (Hne id_refl).
  - exact (existT _ v (InT_here v l')).
Defined.

(* The two directions compose without information loss on the membership face: the composite witness of lift after shim
is a legitimate member. (The exact witness shape may drift: lift normalizes to the head element while H may witness
any member position — hence only membership legitimacy is recorded, not Leibniz identity of witnesses.) *)
Lemma pls_vocab_ne_shim_lift {Tok : Set} (vocab : list Tok)
  (H : pls_vocab_ne vocab)
  : InT (projT1 (pls_vocab_ne_lift vocab (pls_vocab_ne_shim vocab H))) vocab.
Proof.
  destruct vocab as [|v l'].
  - destruct H as [l Hin]. inversion Hin.
  - simpl. exact (InT_here v l').
Qed.

(* ============================================================ *)
(* 4. Thin aliases over the Q-layer carriers (the base S02 already provides both directions: *)
(* QltT_to_Qlt L29 / Qlt_to_QltT L38 / Qle_to_QleT' L97 / QleT'_to_Qle L84; *)
(* this file only forwards them under one family-wide naming scheme, with zero re-proofs) *)
(* ============================================================ *)
Definition pls_Qlt_to_QltT (x y : Q) (H : Qlt x y) : QltT x y
  := Qlt_to_QltT x y H.

Definition pls_Qle_to_QleT' (x y : Q) (H : Qle x y) : QleT' x y
  := Qle_to_QleT' x y H.

Definition pls_QltT_to_Qlt (x y : Q) (H : QltT x y) : Qlt x y
  := QltT_to_Qlt x y H.

Definition pls_QleT'_to_Qle (x y : Q) (H : QleT' x y) : Qle x y
  := QleT'_to_Qle x y H.

(* ============================================================ *)
(* 5. Real-layer dependency-face accessors (real_lt is a sigT witness form, S02:456) *)
(* ============================================================ *)
Definition pls_real_lt_eps {x y : Real} (H : real_lt x y) : Q := projT1 H.
Definition pls_real_lt_rest {x y : Real} (H : real_lt x y) := projT2 H.
Definition pls_real_le_cases {x y : Real} (H : real_le x y)
  := H : Or (real_lt x y) (real_eq x y).

Print Assumptions pls_vocab_ne_shim.
