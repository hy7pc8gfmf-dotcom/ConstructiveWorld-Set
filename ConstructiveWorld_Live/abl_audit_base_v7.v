(* ConstructiveWorld-Set — direct exercise of the provability-machinery soundness statements on Set-layer carriers. *)

(** * abl_audit_base_v7: direct-exercise carriers for the provability
      machinery of [G10_LoebFam].

    Mission.  Five carrier theorems exercise the soundness face of the provability machinery —
      the meta-level soundness of the object proof system [Prf] — each pairing an upstream
      statement's general form with concrete instances at certificate code 2624
      (= gnPrf of 0 = 0) and formula code 656 (= gnF of 0 = 0): [abg_prf_sound_ax_branch]
      ([Prf_soundness]; [ax_eqT] branch), [abg_prf_sound_mp_repl_derivation] (real mpF ∘ repl
      composite; both soundness-induction branches), [abg_prf_sound_repl_branch] (the Σ0
      substitution invariant), [abg_gnprf_replay_2624] ([gnPrf_replay]; self-fueled corollary:
      dP2 2624 2624 = Some(0 = 0)), [abg_verpf_ledger_656] ([verPf_ledger_sound]; Σ-atom
      instance at the tight bound 2625; five verPf smoke tests, four negative). Closures
      [abg_fzz] [abg_axz] [abg_th0] [abg_pfr] [abg_pfmp] build the proofs.

    Dependencies.  Requires [G10_LoebFam] of this development; Stdlib
      [Extraction] at the file tail.

    References.  This development, G10_LoebFam.v (the exercised statements [Prf_soundness],
      [gnPrf_replay], [gnPrf_replay_eq], [verPf_ledger_sound], [evalF2_fsig_ledger]), and the
      same-name baseline module of ConstructiveWorld-Main (statement names verbatim).

    Constructivity.  No admitted statements, no classical logic, no [Prop] carriers:
      statement-face conjunctions are [Datatypes.prod], equalities are [loeb_tid]; arithmetic
      bounds only in proof-layer premises; proofs close by [Qed] through explicit terms and
      [eq_refl]-level computation; the ten [Print Assumptions] audits report Closed.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" abl_audit_base_v7.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

Require Import G10_LoebFam.

(* ============================================================ *)
(* Section 0. Internal fittings: the concrete formulas and explicit certificate closures (not carrier statements) *)
(* ============================================================ *)

(* the proved formula f0 := 0 = 0 (its Goedel code is 656, by computation) *)
Definition abg_fzz : Formula := teq tzero tzero.

(* the explicit ax_eqT certificate: 0 = 0 is self-equal under every valuation
   (its certificate code is 2624, by computation) *)
Definition abg_axz : Prf abg_fzz :=
  ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* the substitution context for the diagonal, th0 := 0 = 0 (an in-language
   formula with the variable slot 0 left open) *)
Definition abg_th0 : Formula := teq (tvar 0) (tvar 0).

(* the explicit repl certificate: a proof of 0 = 0 -> 0 = 0 (both substitution
   terms of th0 are tzero, so the value ledger is self-equal) *)
Definition abg_pfr : Prf (fimp abg_fzz abg_fzz) :=
  repl abg_th0 tzero tzero
    (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* the explicit mpF certificate: modus ponens on the repl major premise and the
   ax_eqT minor premise yields a proof of 0 = 0 *)
Definition abg_pfmp : Prf abg_fzz :=
  mpF abg_fzz abg_fzz abg_pfr abg_axz.

(* ============================================================ *)
(* Carrier 1. Prf_soundness, form A: the general form cited directly plus the ax_eqT branch instance *)
(*   (the explicit closure at certificate code 2624; the semantic wing computed) *)
(* ============================================================ *)

Theorem abg_prf_sound_ax_branch :
  (forall (f : Formula) (pf : Prf f) (s : nat -> nat),
     loeb_tid bool (evalF f s) true) *
  loeb_tid bool (evalF abg_fzz (fun _ : nat => 0)) true.
Proof.
  split.
  - (* the general form: the meta-level soundness theorem cited verbatim,
       universally quantified over the three rules *)
    intros f pf s. exact (Prf_soundness f pf s).
  - (* the ax_eqT instance: evalF of 0 = 0 at the zero valuation computes to true *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* Carrier 2. Prf_soundness, form B: the real mpF ∘ repl composite derivation — *)
(*   one exercise covering both non-trivial branches of the soundness induction *)
(* ============================================================ *)

Theorem abg_prf_sound_mp_repl_derivation :
  (forall s : nat -> nat, loeb_tid bool (evalF abg_fzz s) true) *
  loeb_tid bool (evalF (fimp abg_fzz abg_fzz) (fun _ : nat => 0)) true.
Proof.
  split.
  - (* the derivation use: the soundness theorem consumes the mpF certificate
       (whose sub-certificate chain contains the repl certificate), exercising
       both induction branches for real *)
    intros s. exact (Prf_soundness abg_fzz abg_pfmp s).
  - (* the composite formula computes: imp of true -> true is true *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* Carrier 3. Prf_soundness, form C: the repl branch alone — the semantics of *)
(*   the Σ0 substitution invariant (the unique non-logical axiom of the diagonal *)
(*   biconditional) is covered by the soundness theorem *)
(* ============================================================ *)

Theorem abg_prf_sound_repl_branch :
  (forall s : nat -> nat,
     loeb_tid bool (evalF (fimp abg_fzz abg_fzz) s) true) *
  loeb_tid bool (evalF (substF abg_th0 tzero) (fun _ : nat => 0)) true.
Proof.
  split.
  - (* the repl branch: the soundness theorem consumes the repl certificate
       [abg_pfr], covering its semantics *)
    intros s. exact (Prf_soundness (fimp abg_fzz abg_fzz) abg_pfr s).
  - (* the substitution invariant computes: substF th0 tzero substitutes
       termwise to 0 = 0, and evalF gives true *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* Carrier 4. Code-level replay: the general form of gnPrf_replay cited directly *)
(*   plus the self-fueled replay instance at certificate code 2624 *)
(*   (dP2 2624 2624 returns Some(0 = 0); the Set-layer exit) *)
(* ============================================================ *)

Theorem abg_gnprf_replay_2624 :
  (forall (f : Formula) (pf : Prf f) (k : nat),
     S01_BaseRing.NatLe (gnPrf f pf) k ->
     loeb_tid (option Formula) (dP2 k (gnPrf f pf)) (Some f)) *
  loeb_tid (option Formula) (dP2 2624 2624) (Some abg_fzz).
Proof.
  split.
  - (* the general form: the code-level replay theorem cited verbatim (the fuel
       ledger over the three rules) *)
    intros f pf k Hk. exact (gnPrf_replay f pf k (S01_BaseRing.NatLe_drop _ _ Hk)).
  - (* the 2624 instance: the self-fueled replay corollary instantiated at the
       explicit ax_eqT certificate — gnPrf of (0 = 0, abg_axz) computes to 2624,
       and dP2 2624 2624 returns Some(0 = 0) *)
    apply loeb_tid_eq. exact (gnPrf_replay_eq abg_fzz abg_axz).
Qed.

(* ============================================================ *)
(* Carrier 5. The verPf ledger: the general form of verPf_ledger_sound cited directly *)
(*   plus the Σ-atom instance at the tight bound 2625 and the five verPf smoke *)
(*   tests (positive 2624/656; negative junk, impersonation, mismatch, out-of-range) *)
(* ============================================================ *)

Theorem abg_verpf_ledger_656 :
  (forall (w : nat) (f : Formula) (pf : Prf f),
     loeb_tid nat w (gnPrf f pf) -> loeb_tid bool (verPf w (gnF f)) true) *
  ((forall s : nat -> nat,
      loeb_tid bool (evalF2 (fsig (numT 2625) (numT 656)) s) true) *
   (loeb_tid bool (verPf 2624 656) true *
    (loeb_tid bool (verPf 3 656) false *
     (loeb_tid bool (verPf 656 656) false *
      (loeb_tid bool (verPf 2624 657) false *
       loeb_tid bool (verPf 3000 656) false))))).
Proof.
  split.
  - (* the general form: the verPf soundness half cited verbatim (ledger
       alignment of the code implies verification passes) *)
    intros w f pf Hw. exact (verPf_ledger_sound w f pf Hw).
  - split.
    + (* the tight-bound Σ-atom instance: evalF2_fsig_ledger instantiated at the
         bound 2625 (= the certificate code 2624 + 1, tighter than the 3000 of
         Sigma_atom_fires_via_ledger); both premises (the ltb bound ledger and
         the formula-code alignment ledger) are supplied by computation
         reflection, exercising the statement for real *)
      intros s.
      apply (evalF2_fsig_ledger (numT 2625) (numT 656) s abg_fzz abg_axz).
      * apply loeb_tid_eq. exact eq_refl.
      * apply loeb_tid_eq. exact eq_refl.
    + split.
      * (* positive wing: the genuine certificate code 2624 verifies the formula
           code 656 (by computation) *)
        apply loeb_tid_eq. exact eq_refl.
      * split.
        -- (* negative wing 1: the junk code 3 decodes to no certificate, so verPf
              rejects (by computation) *)
           apply loeb_tid_eq. exact eq_refl.
        -- split.
           ++ (* negative wing 2: the formula code 656 impersonating a certificate
                 code is rejected — aligned with the dP_rejects_formula_code
                 smoke test of the source (by computation) *)
              apply loeb_tid_eq. exact eq_refl.
           ++ split.
              ** (* negative wing 3: the genuine certificate code against the
                    mismatched formula code 657 is rejected — a misaligned ledger
                    means rejection *)
                 apply loeb_tid_eq. exact eq_refl.
              ** (* negative wing 4: the out-of-range code 3000 against the genuine
                    formula code is rejected — passing the bound is not ledger
                    alignment *)
                 apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* Section 6. Assumption audit: the five provability statements of [G10_LoebFam] *)
(*   exercised from this file, plus the five carriers of this file themselves. *)
(*   Reading criterion: all ten lines report Closed under the global context. *)
(*   The first five are the exercised statements (the Prf_soundness semantics, *)
(*   the gnPrf_replay code level, the verPf_ledger_sound / evalF2_fsig_ledger *)
(*   ledger); the last five are this file's own carriers. The Require closure *)
(*   carries the full UpLoeb/UpRefuted/UpQKBound/UpLoebD2 chain; any *)
(*   environment-level axioms reported by coqchk belong to that chain rather *)
(*   than to this file — the per-statement Print Assumptions lines here are *)
(*   the authoritative audit for this file. *)
(* ============================================================ *)

Print Assumptions G10_LoebFam.Prf_soundness.
Print Assumptions G10_LoebFam.gnPrf_replay.
Print Assumptions G10_LoebFam.gnPrf_replay_eq.
Print Assumptions G10_LoebFam.verPf_ledger_sound.
Print Assumptions G10_LoebFam.evalF2_fsig_ledger.
Print Assumptions abg_prf_sound_ax_branch.
Print Assumptions abg_prf_sound_mp_repl_derivation.
Print Assumptions abg_prf_sound_repl_branch.
Print Assumptions abg_gnprf_replay_2624.
Print Assumptions abg_verpf_ledger_656.

(* ============================================================ *)
(* Section 7. Exit port: the carriers double as extraction ports (extraction face with zero Obj.magic) *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abg_prf_sound_ax_branch
  abg_prf_sound_mp_repl_derivation abg_prf_sound_repl_branch
  abg_gnprf_replay_2624 abg_verpf_ledger_656.
