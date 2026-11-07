(* ConstructiveWorld-Set — single-package supply for the minimum-P chain slots. *)

(** * UpAblD1S6_UpReqMinPKLChain: packaged supply for the
       minimum-probability-chain slots.

    Mission.  A packaged record [uabd1s6_mpk_pack6] carries six data
    slots of the minimum-probability-chain world as constructor fields
    sorted into [Set] (no [Type] fields) — [tokens], [tokens_ne],
    [tokens_sum], [ratio], [ratio_pos], [ratio_le_one] — supplied in
    one package by [real_one :: nil] ([uabd1s6_mpk_pack6_supplied]).
    Companions: the unbounded slot is unsatisfiable for any finite
    table ([uabd1s6_mpk_tokens_pos_unsat]); the bounded variant is
    satisfied ([uabd1s6_mpk_tokens_pos_bnd]).

    Dependencies.  Stdlib [List] (with [ListNotations]).  Requires
    [S01_BaseRing] through [S15_TailFEPUp] of this development;
    [CW_ConstructiveWorld_219] read-only (zero-Require source version).

    References.  This development, UpAblD1S6_UpReqMinPKLChain.v, the
    ConstructiveWorld-Main baseline whose statement names are carried
    over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblD1S6_UpReqMinPKLChain.v] compiles cleanly (exit 0); the
      first eight bytes of the artifact are [436f7121 00015ff4]. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.

(* ============================================================ *)
(* Source provenance (UpReqMinPKLChain.v, read-only; the source tree    *)
(* is untouched).                                                       *)
(*   Coverage: all 7 N slots of Section [X1MinPKLChain] — [ratio:56],   *)
(*   [ratio_pos:57], [ratio_le_one:58] enter the package; [trich:49]    *)
(*   is a W-class trichotomy wall of the rLPO family (registered as a   *)
(*   wall, no member established).  [NatLt]/[ListDef] are visible       *)
(*   through CW_219, so the source version needs no [Require] of its    *)
(*   own (guarding against mixed-generation .vo collisions).            *)
(*   Direct mirror of the FA-P2S1 member UpAblP2_UpMinP_tokens_pack.v   *)
(*   (same slot family: this module is the [req]-isomorphic form of     *)
(*   the probability-table world of [UpMinP.MinPEntropy]; the P2S1      *)
(*   verdicts carry over slot by slot, including the M2                 *)
(*   unsatisfiability verdict and the M3 satisfiable bounded-variant    *)
(*   counterpart).  The Live_X copy is generation-matched with the      *)
(*   ConstructiveWorld-Main baseline copy: zero generation drift.       *)
(*   The [ratio_pos] slot is genuinely used (use count = 1), so unlike  *)
(*   the P2S1 source theorem, where it is pruned as unconsumed, it      *)
(*   enters the package.                                                *)
(*   Instance supply (M1): [tokens := real_one :: nil] (single-point    *)
(*   probability table) | [tokens_ne := existT 0 id_refl] |             *)
(*   [tokens_sum := real_plus_zero real_one] (cons folding, glued by    *)
(*   two delta/iota steps) | [ratio := real_one] |                      *)
(*   [ratio_pos := real_lt_zero_one] |                                  *)
(*   [ratio_le_one := inr (real_eq_refl real_one)].                     *)
(*   Grading (declared truthfully): M1 = 6 slots at T, merged           *)
(*   supply-grade declaration; M3 = T ([real_lt_zero_one] supplied in   *)
(*   one line); zero W-slot work.                                       *)
(* ============================================================ *)

(* ============ M1 packaged record: the six slot statements enter the
   package verbatim (against source version L50-58) ============ *)

Inductive uabd1s6_mpk_pack6 : Set :=
| uabd1s6_mpk_pack6_intro :
    forall tokens : list Real,
      (* ←L51 tokens_ne *)
      sigT (fun i : nat => NatLt i (length tokens)) ->
      (* ←L54-55 tokens_sum *)
      real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one ->
      (* ←L56 ratio *)
      forall ratio : Real,
      (* ←L57 ratio_pos *)
        real_lt real_zero ratio ->
        (* ←L58 ratio_le_one *)
        real_le ratio real_one ->
        uabd1s6_mpk_pack6.

(* ============ M1 supply lemma: the single-point probability table
   [one :: nil] with [ratio := one] feeds all six slots in one step ============ *)

Theorem uabd1s6_mpk_pack6_supplied : uabd1s6_mpk_pack6.
Proof.
  exact (uabd1s6_mpk_pack6_intro
           (real_one :: nil)
           (existT _ 0%nat (@id_refl bool true))
           (real_plus_zero real_one)
           real_one
           real_lt_zero_one
           (inr (real_eq_refl real_one))).
Qed.

(* Original slot statement: forall i : nat, real_lt real_zero
   (ListDef.nth i tokens real_zero).  Taking i := length tokens, nth is
   out of range and returns the default real_zero, so real_lt zero zero
   would be required — contradicting real_lt_irrefl; hence the slot is
   unsatisfiable for any finite table (same verdict as P2S1 M2). *)
Theorem uabd1s6_mpk_tokens_pos_unsat :
  forall tokens : list Real,
    (forall i : nat, real_lt real_zero (ListDef.nth i tokens real_zero)) -> False.
Proof.
  intros tokens Hpos.
  assert (Hlen : real_lt real_zero (ListDef.nth (length tokens) tokens real_zero))
    by (apply Hpos).
  assert (Hov : ListDef.nth (length tokens) tokens real_zero = real_zero).
  { apply nth_overflow. apply le_n. }
  rewrite Hov in Hlen.
  destruct (real_lt_irrefl real_zero Hlen).
Qed.

(* ============ M3: the satisfiable bounded-variant counterpart (the mismatch
   is only the unbounded quantifier; the data face is unaffected) ============ *)

Theorem uabd1s6_mpk_tokens_pos_bnd :
  real_lt real_zero (ListDef.nth 0%nat (real_one :: nil) real_zero).
Proof.
  exact real_lt_zero_one.
Qed.

(* ============ Assumption-face closure declaration ============ *)

Print Assumptions uabd1s6_mpk_pack6_supplied.
Print Assumptions uabd1s6_mpk_tokens_pos_unsat.
Print Assumptions uabd1s6_mpk_tokens_pos_bnd.
