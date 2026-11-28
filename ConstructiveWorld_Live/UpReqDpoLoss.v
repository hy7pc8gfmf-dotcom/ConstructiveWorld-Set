(* ========================================================================= *)
(* Module   : UpReqDpoLoss                                                  *)
(* Mission.  The DPO total-loss cluster over a finite preference data set:  *)
(*            fold extensionality on the req carrier (rdl_fold_plus_ext_on  *)
(*            with InT-restricted premises, rdl_fold_plus_ext unrestricted),*)
(*            single-pair loss extensionality (rdl_pair_loss_ext), the      *)
(*            total loss as the fold of single-pair losses                 *)
(*            (rdl_dpo_total_loss, rdl_dpo_total_loss_star), equality of    *)
(*            the total loss at the canonical policy with the star constant *)
(*            (rdl_dpo_total_loss_at_star), monotonicity under pointwise    *)
(*            loss domination (rdl_dpo_total_loss_monotone), and the local  *)
(*            optimality characterization (rdl_dpo_total_loss_star_char).   *)
(* Dependencies. S01_BaseRing .. S15_TailFEPUp, UpReqAlgebra, UpReqAlign,   *)
(*            UpReqAlignRestA (ralt_* DPO exports) of this development;     *)
(*            Stdlib List.                                                  *)
(* References.  UpReqAlignRestA.v (ralt_* export signatures, section        *)
(*            premises, global-Real notation block); the upstream           *)
(*            ConstructiveWorld-Main UpReqDpoLoss.v (statement names kept). *)
(* Constructivity. Statement faces are Set-carried: req/lt/le abbreviate    *)
(*            real_eq/real_lt/real_le : Real -> Real -> Set with Real :=    *)
(*            sigT (fun u : Qseq => cauchy u), the development-wide         *)
(*            carrier shape; no sigT embedding beyond that mirror. Zero     *)
(*            axioms, zero admits, no classical or extensional additions.   *)
(*            No statement is Prop, hence no Qed appears anywhere: all six  *)
(*            proofs end in Defined (delta-transparent, extraction-ready    *)
(*            conclusion face). fold_right is instantiated at the concrete  *)
(*            carrier (Preference -> R) built inside this file.             *)
(* Build.     rocq c -native-compiler no -q -Q <development root> ""        *)
(*            UpReqDpoLoss.v.                                               *)
(* ========================================================================= *)
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
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlignRestA.
Import RealInterfaceEnhancedMod.

(* The interface class of this development is unparameterized; the carrier
   and the order/equality faces are bound to their global names, matching
   the notation block of UpReqAlign.v and UpReqAlignRestA.v. *)
Notation R := Real.
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ============================================================ *)
(* Section ReqDpoLossCore: the total-loss fold over the data set. *)
(* ============================================================ *)
Section ReqDpoLossCore.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis rdl_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).
(* Logarithm compatibility premises; on section close they are read back
   out as explicit theorem arguments. *)
Hypothesis rdl_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis rdl_log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Variable Preference : Set.
Variable pref_win : Preference -> S.
Variable pref_lose : Preference -> S.
Variable pref_dataset : list Preference.

(* ---- Delta-transparent thin wrappers over the DPO exports ---- *)

Definition rdl_pair (pi : S -> R) (Hpi : forall s : S, lt zero (pi s))
           (pref : Preference) : R :=
  ralt_dpo_pair_loss S beta pi_ref pi_ref_pos Preference pref_win pref_lose
                     pi Hpi pref.

Definition rdl_pair_star (pref : Preference) : R :=
  ralt_dpo_pair_loss_star S reward Preference pref_win pref_lose pref.

Definition rdl_diff (pi : S -> R) (Hpi : forall s : S, lt zero (pi s))
           (pref : Preference) : R :=
  ralt_implicit_reward_diff S beta pi_ref pi_ref_pos Preference pref_win pref_lose
                            pi Hpi pref.

Definition rdl_diff_star (pref : Preference) : R :=
  req_minus (reward (pref_win pref)) (reward (pref_lose pref)).

(* The canonical policy and its pointwise positivity witness. *)
Definition rdl_pistar : S -> R :=
  ralt_pistar S sumf rdl_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

Definition rdl_pistar_pos : forall s : S, lt zero (rdl_pistar s) :=
  ralt_pistar_pos S sumf rdl_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* ============ Main result 1: fold extensionality on the req carrier ============ *)

(* InT-restricted form: a pointwise req premise on the listed elements
   transports through the whole fold. Proof: list induction, each step a
   two-leg req_plus_compat chain (swap the head, then carry the induction
   invariant through the tail); no function extensionality anywhere. *)
Lemma rdl_fold_plus_ext_on :
  forall (f g : Preference -> R) (l : list Preference),
    (forall a, InT a l -> req (f a) (g a)) ->
    req (fold_right (fun p acc => plus (f p) acc) zero l)
        (fold_right (fun p acc => plus (g p) acc) zero l).
Proof.
  intros f g l Hpt.
  induction l as [| p rest IH]; cbn [fold_right].
  - exact (req_refl zero).
  - apply (req_trans
             (plus (f p) (fold_right (fun p0 acc => plus (f p0) acc) zero rest))
             (plus (g p) (fold_right (fun p0 acc => plus (f p0) acc) zero rest))
             (plus (g p) (fold_right (fun p0 acc => plus (g p0) acc) zero rest))).
    + exact (req_plus_compat (f p) (g p)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (Hpt p (InT_here p rest))
               (req_refl (fold_right (fun p0 acc => plus (f p0) acc) zero rest))).
    + exact (req_plus_compat (g p) (g p)
               (fold_right (fun p0 acc => plus (f p0) acc) zero rest)
               (fold_right (fun p0 acc => plus (g p0) acc) zero rest)
               (req_refl (g p))
               (IH (fun a Hin => Hpt a (InT_next a p rest Hin)))).
Defined.

(* Unrestricted form: a pointwise premise on every element (the shape used
   by the characterization); one-line corollary of the restricted form. *)
Lemma rdl_fold_plus_ext :
  forall (f g : Preference -> R) (l : list Preference),
    (forall a, req (f a) (g a)) ->
    req (fold_right (fun p acc => plus (f p) acc) zero l)
        (fold_right (fun p acc => plus (g p) acc) zero l).
Proof.
  intros f g l Hpt.
  exact (rdl_fold_plus_ext_on f g l (fun a _ => Hpt a)).
Defined.

(* ============ Definitions: the total loss as a fold ============ *)

Definition rdl_dpo_total_loss (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) : R :=
  fold_right (fun pref acc => plus (rdl_pair pi Hpi pref) acc) zero pref_dataset.

Definition rdl_dpo_total_loss_star : R :=
  fold_right (fun pref acc => plus (rdl_pair_star pref) acc) zero pref_dataset.

(* ============ Auxiliary: single-pair loss extensionality ============ *)

(* A pointwise premise on the implicit-reward difference transports through
   the sigmoid cross-entropy: logarithm compatibility premise, then the
   one-leg and exp_neg compatibility chain. *)
Lemma rdl_pair_loss_ext :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference),
    req (rdl_diff pi Hpi pref) (rdl_diff_star pref) ->
    req (rdl_pair pi Hpi pref) (rdl_pair_star pref).
Proof.
  intros pi Hpi pref Hdiff.
  unfold rdl_pair, rdl_pair_star, ralt_dpo_pair_loss, ralt_dpo_pair_loss_star.
  apply rdl_log_req_compat.
  exact (req_plus_compat one one
           (exp_neg (rdl_diff pi Hpi pref))
           (exp_neg (rdl_diff_star pref))
           (req_refl one)
           (exp_neg_req_compat_setoid (rdl_diff pi Hpi pref)
                                      (rdl_diff_star pref) Hdiff)).
Defined.

(* ============ Main result 2: total loss at the canonical policy ============ *)

Theorem rdl_dpo_total_loss_at_star :
  req (rdl_dpo_total_loss rdl_pistar rdl_pistar_pos) rdl_dpo_total_loss_star.
Proof.
  unfold rdl_dpo_total_loss, rdl_dpo_total_loss_star.
  apply (rdl_fold_plus_ext_on (rdl_pair rdl_pistar rdl_pistar_pos)
                              rdl_pair_star pref_dataset).
  intros a Hin.
  unfold rdl_pair, rdl_pair_star.
  exact (ralt_dpo_pair_loss_at_star S sumf rdl_sum_pos reward beta beta_pos
           pi_ref pi_ref_pos Z_align_pos rdl_log_req_compat
           rdl_log_inv_exp_neg_req Preference pref_win pref_lose a).
Defined.

(* ============ Main result 3: monotonicity of the total loss ============ *)

Theorem rdl_dpo_total_loss_monotone :
  forall (pi1 pi2 : S -> R)
         (Hpi1 : forall s : S, lt zero (pi1 s))
         (Hpi2 : forall s : S, lt zero (pi2 s)),
    (forall pref, InT pref pref_dataset ->
       le (rdl_pair pi2 Hpi2 pref) (rdl_pair pi1 Hpi1 pref)) ->
    le (rdl_dpo_total_loss pi2 Hpi2) (rdl_dpo_total_loss pi1 Hpi1).
Proof.
  intros pi1 pi2 Hpi1 Hpi2 Hpt.
  unfold rdl_dpo_total_loss.
  induction pref_dataset as [| p rest IH]; cbn [fold_right].
  - apply le_refl.
  - apply le_plus_compat.
    + exact (Hpt p (InT_here p rest)).
    + apply IH. intros pref Hin. exact (Hpt pref (InT_next pref p rest Hin)).
Defined.

(* ============ Main result 4: local optimality characterization ============ *)

Theorem rdl_dpo_total_loss_star_characterization :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)),
    (forall pref, InT pref pref_dataset ->
       req (rdl_diff pi Hpi pref) (rdl_diff_star pref)) ->
    req (rdl_dpo_total_loss pi Hpi) rdl_dpo_total_loss_star.
Proof.
  intros pi Hpi Heq.
  unfold rdl_dpo_total_loss, rdl_dpo_total_loss_star.
  apply (rdl_fold_plus_ext_on (rdl_pair pi Hpi) rdl_pair_star pref_dataset).
  intros a Hin.
  apply rdl_pair_loss_ext.
  exact (Heq a Hin).
Defined.

End ReqDpoLossCore.

(* ============================================================ *)
(* Assumption audit: one Print Assumptions per theorem of this piece. *)
(* ============================================================ *)

Print Assumptions rdl_fold_plus_ext_on.
Print Assumptions rdl_fold_plus_ext.
Print Assumptions rdl_pair_loss_ext.
Print Assumptions rdl_dpo_total_loss_at_star.
Print Assumptions rdl_dpo_total_loss_monotone.
Print Assumptions rdl_dpo_total_loss_star_characterization.
