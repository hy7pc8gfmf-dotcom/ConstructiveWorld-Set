(* ConstructiveWorld-Set -- budget exhaustion witness: an explicit machine-checked counterexample to the lw5n budget-sufficiency premise at q = 22/7. *)

(** * NsepBudgetExhaustion: constructive refutation of the budget-sufficiency premise of the budgeted minimal separation index search.

    Mission.  The unconditional hit form of the budgeted minimal separation index search reduces to the
      single premise that for every q there is a hit order [n0 <= lw5n_bnd q]; this module refutes it
      constructively: q0 lies in every window from order 0 through the budget endpoint 34, the budget is
      exhausted along the whole run, the search outputs the endpoint with a non-hit decision there, and
      the unconditional form evaluates to false at q0.  Two construction steps: (1) the all-orders
      in-window lemma is folded analytically from lw5n_win_nested plus two Q-order pins at order 34 (in
      NsepBudgetVerify.v), not by materializing lw5n_shape_mono; (2) the bridge lemma lw5n_find_nsep_find
      rewrites before the destruct, avoiding the two-fixpoint 34-step expansion that froze Qed in test runs.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia],
      [Extraction].  Requires [LW0LeibWindow] (leiblw_Id, leiblw_id_eq, leiblw_id_inv_in, leiblw_Qleb),
      [S01_BaseRing] (the Set-face conjunction And := A * B), [NsepFindGeneric] (nsep_find),
      [LW5SepComplexity] (lw5n_find, lw5n_bnd, lw5n_nsep, lw5n_sep_dec, lw5n_win_nested),
      [NsepBudgetVerify] (q0, the two computational pins, the split lemma lw5n_inwin_q0_all).

    References.  LW5SepComplexity.v lw5n_find:412, lw5n_bnd:427, lw5n_nsep:429, lw5n_win_nested:228; NsepFindGeneric.v:45.

    Constructivity.  Axiom-free, zero admissions, zero classical logic; the main conclusion face of the
      first two sections is entirely Set; the two refutation statements are pure Prop-position, carried
      by the Nat.le order and bool equality with the leiblw_Id face transposed by identity lemmas inside
      the proofs (the original Set-level And face with a Prop position was REPL-tested untouchable;
      B-band item, off the extraction list per the lw5n_shape_band precedent); zero vm_compute;
      Obj.magic = 0 on the extraction face.

    Build.  [coqc -native-compiler no -q -Q . "" -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" NsepBudgetVerify.v, then the same command for NsepBudgetExhaustion.v; the dependency NsepFindGeneric.v built in the same world beforehand] compiles cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.
Require Import NsepBudgetVerify.

(* ============================================================ *)
(* S0 identity-interface supplement: extraction of the false face of leiblw_Id *)
(*    (the library leiblw_id_eq and leiblw_id_inv cover only the = true face of *)
(*    bool). *)
(* ============================================================ *)

Lemma leiblw_id_false_inv : forall b : bool, leiblw_Id b false -> b = false.
Proof.
  intros b H. destruct b as [|].
  - inversion H.
  - reflexivity.
Qed.

(* ============================================================ *)
(* S1 general exhaustion lemma: if every order in the interval is a non-hit, the *)
(*    search outputs the budget endpoint and the decision at the endpoint is a *)
(*    non-hit. *)
(* ============================================================ *)

Lemma nsep_find_exhaust :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  (forall m : nat, (n <= m)%nat -> (m <= n + fuel)%nat ->
                   leiblw_Id (dec q m) false) ->
  And (leiblw_Id (nsep_find dec q n fuel) (n + fuel)%nat)
      (leiblw_Id (dec q (nsep_find dec q n fuel)) false).
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n H.
  - simpl. split.
    + replace (n + 0)%nat with n by lia. apply leiblw_id_intro.
    + apply H; lia.
  - assert (Hn : dec q n = false)
      by (apply leiblw_id_false_inv; apply H; lia).
    assert (Hr : And (leiblw_Id (nsep_find dec q (Datatypes.S n) f)
                                (Datatypes.S n + f)%nat)
                     (leiblw_Id (dec q (nsep_find dec q (Datatypes.S n) f))
                                false)).
    { apply (IH (Datatypes.S n)). intros m Hm1 Hm2. apply H; lia. }
    destruct Hr as [Hend Hout]. simpl. rewrite Hn.
    replace (n + Datatypes.S f)%nat with (Datatypes.S n + f)%nat by lia.
    split.
    + exact Hend.
    + exact Hout.
Qed.

(* ============================================================ *)
(* S2 budget-exhaustion corollary: the search for q0 outputs the budget endpoint *)
(*    34, and the decision at the endpoint is a non-hit.  The bridge lemma rewrites *)
(*    first (lw5n_find coincides with nsep_find lw5n_sep_dec pointwise, by pure *)
(*    symbolic case analysis) and the destruct comes second, so the kernel Qed *)
(*    performs zero window computation (construction step (2), see header). *)
(*    (The original S2 instance anchor, the computational pins, and the all-orders *)
(*    in-window lemma have been split into NsepBudgetVerify.v and are in place via *)
(*    Require; the section numbering continues.) *)
(* ============================================================ *)

Lemma lw5n_find_nsep_find : forall q n fuel,
  lw5n_find q n fuel = nsep_find lw5n_sep_dec q n fuel.
Proof.
  intros q n fuel. revert n. induction fuel as [|f IH]; intros n.
  - reflexivity.
  - cbn [lw5n_find nsep_find]. destruct (lw5n_sep_dec q n).
    + reflexivity.
    + rewrite (IH (Datatypes.S n)). reflexivity.
Qed.

Lemma nsep_q0_no_hit_hyp :
  forall m : nat, (0 <= m)%nat -> (m <= 0 + 34)%nat ->
    leiblw_Id (lw5n_sep_dec q0 m) false.
Proof.
  intros m Hm1 Hm2. unfold lw5n_sep_dec.
  assert (Hb : (m <= 34)%nat) by lia.
  pose proof (lw5n_inwin_q0_all m Hb) as Hw.
  leiblw_id_inv_in Hw. rewrite Hw. apply leiblw_id_intro.
Qed.

Lemma lw5n_nsep_q0_exhaust :
  And (leiblw_Id (lw5n_nsep q0) 34%nat)
      (leiblw_Id (lw5n_sep_dec q0 (lw5n_nsep q0)) false).
Proof.
  unfold lw5n_nsep. rewrite lw5n_find_nsep_find. rewrite lw5n_bnd_q0.
  destruct (nsep_find_exhaust lw5n_sep_dec q0 34 0 nsep_q0_no_hit_hyp)
    as [Hend Hout].
  replace (0 + 34)%nat with 34%nat in Hend by lia.
  split.
  - exact Hend.
  - exact Hout.
Qed.

Lemma lw5n_nsep_q0_at_bnd : leiblw_Id (lw5n_nsep q0) (lw5n_bnd q0).
Proof. rewrite lw5n_bnd_q0. exact (fst lw5n_nsep_q0_exhaust). Qed.

(* ============================================================ *)
(* S3 refutation face: no hit order within the budget, and the unconditional form *)
(*    evaluates to false at q0.  The statements are pure Prop-position (the Nat.le *)
(*    order plus bool equality; a B-band item, following the lw5n_shape_band *)
(*    precedent, not in the extraction list). *)
(* ============================================================ *)

Theorem nsep_no_hit_q0 :
  ~ (exists n0 : nat, (n0 <= lw5n_bnd q0)%nat /\
                      lw5n_sep_dec q0 n0 = true).
Proof.
  intros [n0 [Hb Hs]].
  rewrite lw5n_bnd_q0 in Hb.
  assert (Hw : lw5n_inwin q0 n0 = true)
    by (destruct (lw5n_inwin_q0_all n0 Hb); reflexivity).
  unfold lw5n_sep_dec in Hs. apply negb_true_iff in Hs.
  rewrite Hw in Hs. discriminate Hs.
Qed.

Theorem nsep_uncond_false_q0 :
  ~ (forall q : Q, lw5n_sep_dec q (lw5n_nsep q) = true).
Proof.
  intro H.
  pose proof (H q0) as Hq.
  pose proof (snd lw5n_nsep_q0_exhaust) as Hf.
  apply leiblw_id_false_inv in Hf.
  rewrite Hq in Hf. discriminate Hf.
Qed.

(* ============================================================ *)
(* S4 extraction check and the assumptions audit. *)
(* ============================================================ *)

Separate Extraction lw5n_sep_dec lw5n_bnd lw5n_nsep.

Print Assumptions leiblw_id_false_inv.
Print Assumptions nsep_find_exhaust.
Print Assumptions lw5n_nsep_q0_exhaust.
Print Assumptions lw5n_nsep_q0_at_bnd.
Print Assumptions nsep_no_hit_q0.
Print Assumptions nsep_uncond_false_q0.
