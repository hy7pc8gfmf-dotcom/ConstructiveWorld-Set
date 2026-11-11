(* ============================================================ *)
(** ConstructiveWorld-Set — UpReqPropLiftShim: lifting adapters from legacy negative forms to sigT witness forms.

    Mission.  One-directional adapter family (prefix [pls_]) relating legacy
      premise shapes (existing forms, not violations and not assumption
      discharges) to Set-layer witness forms, so new Set-layer code produces
      and consumes witnesses directly.  [pls_vocab_ne] is the target witness
      form [sigT (fun l : Tok => InT l vocab)]; [pls_vocab_ne_shim] turns it
      into the legacy [Not (Id vocab nil)]; [pls_vocab_ne_lift] is the
      constructive list-split converse: concrete list data splits with no
      decidability assumption, unlike the general Not-to-sigT conversion.
      The Q-layer aliases forward the S02 order-carrier conversions, and the
      accessors [pls_real_lt_eps]/[pls_real_lt_rest]/[pls_real_le_cases] project
      the [real_lt]/[real_le] dependency faces (sigT witness S02:456; Or form).

    Dependencies.  Requires [S01_BaseRing] ([Id]/[Not]/[InT] connectors) and
      [S02_CauchyComplete] ([QltT]/[QleT']/[real_lt]/[real_le]/[Real]); adds no
      new Require beyond these.

    References.  ConstructiveWorld-Main baseline module UpReqPropLiftShim.v,
      whose statement names are carried over verbatim (statement-face
      Set-carrier completion); the base modules are untouched; purely additive.

    Constructivity.  All named statements are carried by [Set]; no
      assumption-like or classical token appears; every proof closes in
      [Qed]/[Defined]; [Print Assumptions] closed; [coqchk] [Axioms: none].

    Build.  Rocq 9.1 direct [coqc -native-compiler no -q -Q . "" UpReqPropLiftShim.v]
      compiles cleanly (exit 0); artifact starts [436f7121 00015ff4]. *)
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
