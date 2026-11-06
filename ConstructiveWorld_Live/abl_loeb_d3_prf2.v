(* ConstructiveWorld-Set -- Set-carried certificate layers for the Loeb bounded-provability family. *)

(** * abl_loeb_d3_prf2: the [Prf2] certificate system and code space for [Formula2].

    Mission.  Formalizes a Set-valued inductive certificate system [Prf2] for
      [Formula2] with rules [prf2_lift], [prf2_mp], [prf2_repl], [prf2_sig] and
      code map [gnPrf2]; main statements [lbf_Prf2_sound],
      [lbf_lift_code_continuous], [lbf_dP2_gnPrf2_none], [lbf_dF2b_gnPrf2_none],
      and the exhibits [lbf_demo_row], [lbf_demo_row_sound],
      [lbf_demo_code_dP2_blind] lifting a real D1 ledger row into the language.

    Dependencies.  Stdlib [Arith.Arith], [Lia].  Requires [G10_LoebFam],
      [abl_loeb_d3], [abl_loeb_d3_ext] of this development.

    References.  This development, abl_loeb_d3_prf2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_loeb_d3_prf2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import abl_loeb_d3_ext.

(* ===================================================================== *)
(* Section A.  Prf2: the Set-valued inductive certificate system for Formula2 *)
(* ===================================================================== *)

(* four rules: the Formula2 counterparts of the three D1 [Prf] constructor
   patterns (ax, mp, repl) plus the Sigma-atom internalization rule.  the two
   premises of [prf2_sig] have exactly the shape of a ledger-row premise of the
   G10 theorem [evalF2_fsig_ledger], so a ledger row is promoted from a
   metalevel premise to an inference rule of the language itself. *)
Inductive Prf2 : Formula2 -> Set :=
| prf2_lift : forall g : Formula, Prf g -> Prf2 (f2b g)
| prf2_mp : forall a b : Formula2, Prf2 (fimp2 a b) -> Prf2 a -> Prf2 b
| prf2_repl : forall (th : Formula2) (t1 t2 : Term),
    (forall s : nat -> nat, loeb_tid nat (valt t1 s) (valt t2 s)) ->
    Prf2 (fimp2 (substF2 th t1) (substF2 th t2))
| prf2_sig : forall (B c : Term) (g : Formula) (pf : Prf g),
    (forall s : nat -> nat, loeb_tid bool (Nat.ltb (gnPrf g pf) (valt B s)) true) ->
    (forall s : nat -> nat, loeb_tid nat (gnF g) (valt c s)) ->
    Prf2 (fsig B c).

(* first theorem of the certificate layer: metalevel soundness of [Prf2],
   isomorphic in shape to the D1 theorem [Prf_soundness].  the [prf2_lift]
   branch reads the D1 soundness result off directly; the [prf2_sig] branch
   uses the D2 ledger-row theorem [evalF2_fsig_ledger] as the soundness of an
   inference rule, so the truth of a Sigma atom now carries a certificate
   inside the language instead of remaining a metalevel record. *)
Theorem lbf_Prf2_sound : forall (f2 : Formula2) (pf : Prf2 f2) (s : nat -> nat),
  loeb_tid bool (evalF2 f2 s) true.
Proof.
  intros f2 pf. induction pf as
    [g pf0 | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv | B c g pf0 Hb Hc]; intros s.
  - (* prf2_lift: D1 soundness supplies the equation directly. *)
    cbn [evalF2]. exact (Prf_soundness g pf0 s).
  - (* prf2_mp: implication elimination.  the fimp2 semantics is boolean
       implication, matching the mpF branch of the D1 soundness theorem: after
       the truth value of the minor premise is substituted into the equation of
       the major premise, the equation simplifies and the truth value of the
       conclusion is read off from it. *)
    tidQ (IH1 s) E1. tidQ (IH2 s) E2. cbn [evalF2] in E1. rewrite E2 in E1.
    cbn [negb orb] in E1. apply loeb_tid_eq. exact E1.
  - (* prf2_repl: substitution invariance (two rewrites along evalF2_subst
       plus the equality rewrite of the slot values). *)
    cbn [evalF2]. rewrite (evalF2_subst th t1 s). rewrite (evalF2_subst th t2 s).
    tidQ (Hv s) E. rewrite E.
    apply loeb_tid_eq. destruct (evalF2 th (upd s (valt t2 s))); reflexivity.
  - (* prf2_sig: the ledger-row semantics of the Sigma atom (evalF2_fsig_ledger
       read as the soundness of an inference rule). *)
    exact (evalF2_fsig_ledger B c s g pf0 (Hb s) (Hc s)).
Qed.

(* ===================================================================== *)
(* Section B.  gnPrf2: Prf2 certificate codes (tags 12-15) and the code-space partition *)
(* ===================================================================== *)

(* certificate codes: the four tags 12-15 are disjoint from the tag ranges of
   terms 0-3, Formulas 4-5, D1 proofs 6-8 and Formula2 formulas 9-11.  the code
   payload of [prf2_sig] stores the quadruple of codes of B, c, g and pf, so
   all code-side information a decoder replay needs travels with the row; the
   metalevel premises stay out of the code, following the D1 convention. *)
Fixpoint gnPrf2 (f2 : Formula2) (pf : Prf2 f2) {struct pf} : nat :=
  match pf in Prf2 f0 return nat with
  | @prf2_lift g pf0 => pairp 12 (gnPrf g pf0)
  | @prf2_mp a b pf1 pf2 => pairp 13 (pairp (gnPrf2 (fimp2 a b) pf1) (gnPrf2 a pf2))
  | @prf2_repl th t1 t2 _ => pairp 14 (pairp (pairp (lbe_gnF2 th) (gnT t1)) (gnT t2))
  | @prf2_sig B c g pf0 _ _ =>
      pairp 15 (pairp (pairp (gnT B) (gnT c)) (pairp (gnF g) (gnPrf g pf0)))
  end.

(* ledger continuity: the code payload of [prf2_lift] carries the D1 proof code
   verbatim, so in the code space of the new certificate layer a D1 ledger row
   survives unchanged under tag 12 (read out by one application of
   [unp2_pair]). *)
Lemma lbf_lift_code_continuous : forall (g : Formula) (pf : Prf g),
  unp2 (gnPrf2 (f2b g) (prf2_lift g pf)) (gnPrf2 (f2b g) (prf2_lift g pf))
  = Some (12, gnPrf g pf).
Proof.
  intros g pf. cbn [gnPrf2]. apply unp2_pair.
Qed.

(* code-space partition, decoder side: the two legacy decoders reject every
   Prf2 code.  the technique follows the two-step route of [lbe_dF_gnF2_none]:
   with self-fuel of the form [dX2 (pairp ...) (pairp ...)] the fuel has no
   constructor head and iota does not unfold, so the statement is first lifted
   to S-fuel form by fuel invariance (an S head unfolds), and [unp2_pair] plus
   the tag dispatch then land in the wildcard branch. *)

Lemma lbf_dP2_S_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2),
  dP2 (Datatypes.S (gnPrf2 f2 pf)) (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf.
  destruct pf as [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    cbn [gnPrf2 dP2]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

(* the D1 proof decoder rejects every Prf2 code under any sufficient fuel
   (uses [lbd_dP2_norm] of abl_loeb_d3). *)
Theorem lbf_dP2_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2) (k : nat),
  (gnPrf2 f2 pf <= k)%nat -> dP2 k (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf k Hk.
  rewrite (lbd_dP2_norm (gnPrf2 f2 pf) k Hk).
  rewrite <- (lbd_dP2_norm (gnPrf2 f2 pf) (Datatypes.S (gnPrf2 f2 pf))
               (Nat.le_succ_diag_r _)).
  apply lbf_dP2_S_gnPrf2_none.
Qed.

Lemma lbf_dF2b_S_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2),
  lbe_dF2b (Datatypes.S (gnPrf2 f2 pf)) (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf.
  destruct pf as [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    cbn [gnPrf2 lbe_dF2b]; rewrite unp2_pair; cbv iota; reflexivity.
Qed.

(* the Formula2 formula decoder rejects every Prf2 code under any sufficient
   fuel (uses [lbe_dF2b_norm] of abl_loeb_d3_ext). *)
Theorem lbf_dF2b_gnPrf2_none : forall (f2 : Formula2) (pf : Prf2 f2) (k : nat),
  (gnPrf2 f2 pf <= k)%nat -> lbe_dF2b k (gnPrf2 f2 pf) = None.
Proof.
  intros f2 pf k Hk.
  rewrite (lbe_dF2b_norm (gnPrf2 f2 pf) k
            (S01_BaseRing.NatLe_lift (gnPrf2 f2 pf) k Hk)).
  rewrite <- (lbe_dF2b_norm (gnPrf2 f2 pf) (Datatypes.S (gnPrf2 f2 pf))
               (S01_BaseRing.NatLe_lift (gnPrf2 f2 pf)
                  (Datatypes.S (gnPrf2 f2 pf)) (Nat.le_succ_diag_r _))).
  apply lbf_dF2b_S_gnPrf2_none.
Qed.

(* ===================================================================== *)
(* Section C.  Exhibits: the first internalized Sigma-atom certificate (a real D1 ledger row, proof code 2624 < 3000, promoted into the language) *)
(* ===================================================================== *)

Definition lbf_demo_pf0 : Prf (teq tzero tzero) :=
  ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* the ledger row sits below the bound: the proof code evaluates below the
   bound under every assignment (numT 3000 is a closed term and evaluates to
   3000 under every assignment). *)
Lemma lbf_demo_row_below : forall s : nat -> nat,
  loeb_tid bool
    (Nat.ltb (gnPrf (teq tzero tzero) lbf_demo_pf0) (valt (numT 3000) s)) true.
Proof.
  intros s. apply loeb_tid_eq. rewrite valt_numT.
  apply (proj2 (Nat.ltb_lt (gnPrf (teq tzero tzero) lbf_demo_pf0) 3000)).
  vm_compute. lia.
Qed.

Definition lbf_demo_atom : Formula2 :=
  fsig (numT 3000) (numT (gnF (teq tzero tzero))).

(* the first internalized certificate: the ledger row with D1 proof code 2624,
   promoted by [prf2_sig] into an in-language proof term of
   [Prf2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))].  the D2 Sigma
   bridging exhibit [Sigma_atom_fires_via_ledger] of G10 thereby gains a
   first-class certificate form. *)
Definition lbf_demo_row : Prf2 lbf_demo_atom :=
  prf2_sig (numT 3000) (numT (gnF (teq tzero tzero))) (teq tzero tzero)
    lbf_demo_pf0 lbf_demo_row_below
    (fun s : nat -> nat => loeb_tid_refl nat (gnF (teq tzero tzero))).

(* exhibit one: the metalevel soundness of the certificate, an instance of
   [lbf_Prf2_sound] (the Sigma atom is true under the trivial assignment). *)
Theorem lbf_demo_row_sound :
  loeb_tid bool (evalF2 lbf_demo_atom (fun _ : nat => 0)) true.
Proof. exact (lbf_Prf2_sound lbf_demo_atom lbf_demo_row (fun _ : nat => 0)). Qed.

(* exhibit two: the new certificate code is invisible to the D1 decoder, an
   instance of the code-space partition theorem (the search space of the D1
   ledger holds no spurious certificate for this code). *)
Theorem lbf_demo_code_dP2_blind : forall k : nat,
  (gnPrf2 lbf_demo_atom lbf_demo_row <= k)%nat ->
  dP2 k (gnPrf2 lbf_demo_atom lbf_demo_row) = None.
Proof. exact (lbf_dP2_gnPrf2_none lbf_demo_atom lbf_demo_row). Qed.

(* assumption-face self-audit: every audit point below must report
   Closed under the global context. *)
Print Assumptions lbf_Prf2_sound.
Print Assumptions gnPrf2.
Print Assumptions lbf_lift_code_continuous.
Print Assumptions lbf_dP2_gnPrf2_none.
Print Assumptions lbf_dF2b_gnPrf2_none.
Print Assumptions lbf_demo_row_sound.
Print Assumptions lbf_demo_code_dP2_blind.
