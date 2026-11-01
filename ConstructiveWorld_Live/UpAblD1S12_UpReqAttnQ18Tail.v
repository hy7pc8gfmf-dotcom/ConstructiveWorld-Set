(* UpAblD1S12_UpReqAttnQ18Tail.v - standalone data-supply package for the
   eight slots of upstream Section AqtTail (zero edits to the source tree).
   Mission.  Package the eight-slot supply interface of that section as
     one Set-sorted record -- Token, vocab, vocab_nonempty, z, m,
     m_in_vocab, gamma, gap_le, the last binding every non-marked token x
     by real_plus (z x) gamma <= z m -- all discharged by one witness
     theorem (uabd1s12_aqt_pack8_supplied) at mechanical supply grade on
     the bool two-point instance.  The remaining slot token_eq_dec
     (upstream line 396), the decidable-equality wall, stays unpackaged:
     the limb instantiates Token := bool and takes its case-split effect
     directly; the blocked premise is never imported.
   Dependencies.  Stdlib List; registered tree modules S01_BaseRing
     through S15_TailFEPUp (read-only; import face exactly the source
     face, no added imports -- guards against mixed-generation .vo
     hazards).  Carriers: S01 Id/InT; S02 ring laws (real_plus/real_zero/
     real_one/real_le/real_plus_comm/real_plus_zero); S07 RealSetoid
     order bridge (real_eq_le, real_eq_trans).
   References.  Upstream UpReqAttnQ18Tail.v lines 393-402, eight slots
     verbatim: Token:393, vocab:394, vocab_nonempty:395, z:397, m:398,
     m_in_vocab:399, gamma:400, gap_le:401-402.  Instance: Token := bool;
     vocab := cons true nil; z := fun x => if x then real_one else
     real_zero; m := true (by InT_here); gamma := real_one; gap_le := the
     bool two-case split (true case: the Set-layer Not premise explodes
     by its own application; false case: 0+1 <= 1 by commutativity plus
     right zero; limbs pinned at the concrete-instance constant level --
     Fixpoint-fold divergence pitfall honored).
   Constructivity.  All statements informative, Set-sorted, Qed-closed; the
     trailing Print Assumptions census attests assumption-free closure.
   Build.  rocq c -native-compiler no -q -Q . "" (Rocq 9.1 toolchain).
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
Lemma uabd1s12_aqt_vocabne : Not (Id (cons true (@nil bool)) (@nil bool)).
Proof. intro H. inversion H. Qed.

(* False-case core: 0+1 <= 1. *)
Lemma uabd1s12_aqt_gap_zero_one : real_le (real_plus real_zero real_one) real_one.
Proof.
  apply RealSetoid.real_eq_le.
  apply (real_eq_trans _ (real_plus real_one real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

(* Base lemma for m_in_vocab: InT_here (tactic form is immune to argument explicitness). *)
Lemma uabd1s12_aqt_mvin : InT true (cons true (@nil bool)).
Proof. apply InT_here. Qed.

(* ============ Supply record: the eight slot statements enter verbatim (source file L393-402) ============ *)

(* Constructivity note: a Set-sorted Inductive constructor cannot quantify Token : Set *)
(* (Set+1<=Set is refused), so Token rises from the constructor into the Inductive's declaration-level binder (binders of that position may live in Set): sort placement and the magic-free extraction channel are preserved together. *)
Inductive uabd1s12_aqt_pack8 (Token : Set) : Set :=
| uabd1s12_aqt_pack8_intro :
    forall vocab : list Token,                             (* source file L394 *)
      (Not (Id vocab nil)) ->                              (* source file L395 *)
      forall z : Token -> Real,                            (* source file L397 *)
        forall m : Token,                                  (* source file L398 *)
          forall m_in_vocab : InT m vocab,                 (* source file L399 *)
            forall gamma : Real,                           (* source file L400 *)
              (forall x : Token, Not (Id x m) ->           (* source file L401-402 *)
                 real_le (real_plus (z x) gamma) (z m)) ->
              uabd1s12_aqt_pack8 Token.
(* The Token slot statement enters as the Inductive declaration-level binder form (source file L393, literal slot annotation). *)

(* ============ Instance supply: the bool two-point instance feeds all eight slots at once ============ *)

Theorem uabd1s12_aqt_pack8_supplied : uabd1s12_aqt_pack8 bool.
Proof.
  apply (uabd1s12_aqt_pack8_intro bool (cons true (@nil bool))
           uabd1s12_aqt_vocabne
           (fun x : bool => if x then real_one else real_zero)
           true uabd1s12_aqt_mvin real_one).
  intros x Hx. destruct x.
  - (* x = true: the premise Not(Id true true) explodes by its own application. *)
    destruct (Hx id_refl).
  - (* x = false: 0+1 <= 1. *)
    exact uabd1s12_aqt_gap_zero_one.
Qed.

(* ============ Global-context closure census ============ *)

Print Assumptions uabd1s12_aqt_pack8_supplied.
