(* UpAblD1S12_UpReqAttnUniformLimit.v - data-supply package for Section
   AlmUniform of the upstream file UpReqAttnUniformLimit.v (standalone
   auxiliary module; zero edits to the source tree).
   Mission.  Package the seven-slot supply interface of that section
     as one Set-sorted record: Token, vocab, z, m, m_in_vocab, gamma,
     and gap_le binding every non-marked token x by real_plus (z x)
     gamma <= z m, all seven slots discharged by one witness theorem
     on the bool two-point instance.  Two zero-consumer slots stay
     unpackaged (vocab_nonempty:277, gamma_pos:285 -- pruning is the
     ablation itself) and the decidable-equality wall token_eq_dec:278
     stays unpackaged; the bypass is described at the record banner.
   Dependencies.  Stdlib List; registered tree modules S01_BaseRing
     through S15_TailFEPUp (read-only; the import face is exactly the
     source face, no added imports, no source-version imports --
     guards against mixed-generation .vo hazards).
   References.  Upstream lines 275-287: Token:275, vocab:276,
     vocab_nonempty:277, token_eq_dec:278, z:279, m:282, m_in_vocab:283,
     gamma:284, gamma_pos:285, gap_le:286-287.  Instance: Token := bool;
     vocab := cons true nil; z := fun x => if x then real_one else
     real_zero; m := true (membership by InT_here); gamma := real_one;
     gap_le := the bool two-case split (true case: the premise explodes
     by its own application; false case: 0+1 <= 1 by commutativity
     plus right zero).
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

(* Single-element list nonempty: cons/nil constructor heads are disjoint (instance-bypass base for the pruned upstream line 277 slot). *)
Lemma uabd1s12_ul_vocabne : Not (Id (cons true (@nil bool)) (@nil bool)).
Proof. intro H. inversion H. Qed.

(* False-case core: 0+1 <= 1 (a two-step trans chain by commutativity plus right zero, mechanical). *)
Lemma uabd1s12_ul_gap_zero_one : real_le (real_plus real_zero real_one) real_one.
Proof.
  apply RealSetoid.real_eq_le.
  apply (real_eq_trans _ (real_plus real_one real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

(* Base lemma for m_in_vocab: InT_here (tactic form is immune to argument explicitness). *)
Lemma uabd1s12_ul_mvin : InT true (cons true (@nil bool)).
Proof. apply InT_here. Qed.

(* ============ Supply record: the seven slot statements enter verbatim (upstream lines 275-287) ============ *)

(* Constructivity note: a Set-sorted Inductive constructor cannot quantify Token : Set *)
(* (Set+1<=Set is refused), so Token rises from the constructor into the Inductive's declaration-level binder (binders of that position may live in Set): sort placement and the magic-free extraction channel are preserved together. *)
Inductive uabd1s12_ul_pack7 (Token : Set) : Set :=
| uabd1s12_ul_pack7_intro :
    forall vocab : list Token,                             (* upstream L276 *)
      forall z : Token -> Real,                            (* upstream L279 *)
        forall m : Token,                                  (* upstream L282 *)
          forall m_in_vocab : InT m vocab,                 (* upstream L283 *)
            forall gamma : Real,                           (* upstream L284 *)
              (forall x : Token, Not (Id x m) ->           (* upstream L286-287 *)
                 real_le (real_plus (z x) gamma) (z m)) ->
              uabd1s12_ul_pack7 Token.
(* The Token slot enters as the Inductive's declaration-level binder (upstream line 275, literal slot annotation). *)

(* ============ Witness: the bool two-point instance feeds all seven slots at once ============ *)

Theorem uabd1s12_ul_pack7_supplied : uabd1s12_ul_pack7 bool.
Proof.
  apply (uabd1s12_ul_pack7_intro bool (cons true (@nil bool))
           (fun x : bool => if x then real_one else real_zero)
           true uabd1s12_ul_mvin real_one).
  intros x Hx. destruct x.
  - (* x = true: the premise Not(Id true true) explodes by its own application. *)
    destruct (Hx id_refl).
  - (* x = false: 0+1 <= 1 (the base lemma after iota reduction). *)
    exact uabd1s12_ul_gap_zero_one.
Qed.

(* ============ Global-context closure census ============ *)

Print Assumptions uabd1s12_ul_pack7_supplied.
