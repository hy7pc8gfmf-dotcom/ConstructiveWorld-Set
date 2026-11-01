(* UpAblD1S12_UpReqAttnMassSplit.v - data-supply package for the eight
   slots of Section AmsMassSplit of the upstream file
   UpReqAttnMassSplit.v (standalone auxiliary module; zero edits to
   the source tree).
   Mission.  Package the eight-slot supply interface of that section
     as one Set-sorted record: Token, vocab, vocab_nonempty, z, m,
     m_in_vocab, gamma, and gap_le binding every non-marked token x
     by real_plus (z x) gamma <= z m, all eight slots discharged by
     one witness theorem on the bool two-point instance.  The
     remaining slot token_eq_dec (upstream line 66) is the
     decidable-equality wall and stays unpackaged; the bypass is
     described at the record banner.
   Dependencies.  Stdlib List; registered tree modules S01_BaseRing
     through S15_TailFEPUp (read-only; the import face is exactly the
     source face, no added imports, no source-version imports --
     guards against mixed-generation .vo hazards).
   References.  Upstream lines 63-72, eight slots verbatim: Token:63,
     vocab:64, vocab_nonempty:65, z:67, m:68, m_in_vocab:69, gamma:70,
     gap_le:71-72.  Instance: Token := bool; vocab := cons true nil;
     z := fun x => if x then real_one else real_zero; m := true
     (membership by InT_here); gamma := real_one; gap_le := the bool
     two-case split (true case: the premise explodes by its own
     application; false case: 0+1 <= 1 by commutativity plus right
     zero).
   Constructivity.  All statements informative; predicates ride the
     real-layer Set carriers of the tree; mechanically checked
     constructive proofs only; assumption-free closure attested by
     the trailing Print Assumptions census.
   Build.  rocq c -native-compiler no -q -Q . ""
  *)

From Stdlib Require Import List.
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

(* ============ Supply-limb base lemmas: mechanical direct matches, zero coupling with the upstream file ============ *)

(* List nonempty: cons/nil constructor heads are disjoint. *)
Lemma uabd1s12_ams_vocabne : Not (Id (cons true (@nil bool)) (@nil bool)).
Proof. intro H. inversion H. Qed.

(* False-case core: 0+1 <= 1. *)
Lemma uabd1s12_ams_gap_zero_one : real_le (real_plus real_zero real_one) real_one.
Proof.
  apply RealSetoid.real_eq_le.
  apply (real_eq_trans _ (real_plus real_one real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

(* Base lemma for m_in_vocab: InT_here (tactic form is immune to argument explicitness). *)
Lemma uabd1s12_ams_mvin : InT true (cons true (@nil bool)).
Proof. apply InT_here. Qed.

(* ============ Supply record: the eight slot statements enter verbatim (upstream lines 63-72) ============ *)

(* Constructivity note: a Set-sorted Inductive constructor cannot quantify Token : Set *)
(* (Set+1<=Set is refused), so Token rises from the constructor into the Inductive's declaration-level binder (binders of that position may live in Set): sort placement and the magic-free extraction channel are preserved together. *)
Inductive uabd1s12_ams_pack8 (Token : Set) : Set :=
| uabd1s12_ams_pack8_intro :
    forall vocab : list Token,                             (* upstream L64 *)
      (Not (Id vocab nil)) ->                              (* upstream L65 *)
      forall z : Token -> Real,                            (* upstream L67 *)
        forall m : Token,                                  (* upstream L68 *)
          forall m_in_vocab : InT m vocab,                 (* upstream L69 *)
            forall gamma : Real,                           (* upstream L70 *)
              (forall x : Token, Not (Id x m) ->           (* upstream L71-72 *)
                 real_le (real_plus (z x) gamma) (z m)) ->
              uabd1s12_ams_pack8 Token.
(* The Token slot enters as the Inductive's declaration-level binder (upstream line 63, literal slot annotation). *)

(* ============ Witness: the bool two-point instance feeds all eight slots at once ============ *)

Theorem uabd1s12_ams_pack8_supplied : uabd1s12_ams_pack8 bool.
Proof.
  apply (uabd1s12_ams_pack8_intro bool (cons true (@nil bool))
           uabd1s12_ams_vocabne
           (fun x : bool => if x then real_one else real_zero)
           true uabd1s12_ams_mvin real_one).
  intros x Hx. destruct x.
  - (* x = true: the premise Not(Id true true) explodes by its own application. *)
    destruct (Hx id_refl).
  - (* x = false: 0+1 <= 1. *)
    exact uabd1s12_ams_gap_zero_one.
Qed.

(* ============ Global-context closure census ============ *)

Print Assumptions uabd1s12_ams_pack8_supplied.