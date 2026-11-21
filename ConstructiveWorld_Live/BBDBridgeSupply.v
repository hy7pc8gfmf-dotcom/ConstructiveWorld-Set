(** * BBDBridgeSupply: realized summation interface for the Boltzmann
      free-energy bridges, with the sum-algebra premises supplied.

    Mission.  [sumf] is fixed to the list-folding sum [csm_sumf S enum]; the
    three sum premises (extensionality, additivity, left linearity) are
    discharged by [bbridge_sum_ext_supply], [bbridge_sum_add_supply],
    [bbridge_sum_linear_supply]; the two bridge identities are restated with
    no sum premises: [bbridge_energy_in_log_boltzmann_bridge] and
    [bbridge_free_energy_boltzmann_bridge] ([F = -D * log Z]), closed by
    transparent instantiation of the closed resolution lemmas.  Genuine
    premises (positivity certificates, partition condition, log
    compatibility, exp/log adjoint) stay as section slots.

    Dependencies.  Stdlib [List]; the Require lines below carry the carrier
    spine, the resolution lemmas, the folding key, the sum supply slots, and
    the bridge host statements.

    References.  mathlib [Finset.sum]: congruence, additivity, linearity of
    finite sums; Boltzmann identity [F = -T * log Z], Set-carrier form.

    Constructivity.  Every statement is carried by [Set] (identity face
    [real_eq], order face [real_lt]); no proposition-carrying statement,
    field, or binder appears.  All five statements are transparent
    ([Defined]) and extract with [Obj.magic] = 0; each is closed under the
    global context by the assumption audit.

    Build.  [coqc -Q <certified world root> "" BBDBridgeSupply.v] under
    Rocq 9.3; artifact header [436f7121 000160bc]. *)

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
Require Import UpReqLogCompD.
Require Import UpReqConcSoftmax.
Require Import ConcMixSelFeed.
Require Import BoltzmannBridgeDischarge.

(* Carrier pinning (the [UpReqLogCompD]/[G05_LogSmall]/bridge-host
   precedent).  The interface fields are re-pinned to their top-level
   [real_]* globals so the whole algebra face of this file stays in the one
   canonical scope: bare names below denote the [Set]-valued equality
   [real_eq] and the [Set]-valued strict order [real_lt], never a
   proposition.  The class module is deliberately not imported here;
   importing it after the pinning would push the boxed class-field
   projections on top of the pinned globals and split the algebra face
   into two heads the unifier cannot reconcile. *)
Notation req := real_eq.
Notation zero := real_zero.
Notation one := real_one.
Notation plus := real_plus.
Notation mult := real_mult.
Notation opp := real_opp.
Notation lt := real_lt.
Notation inv_pos := real_inv_pos.
Notation mult_positive := real_mult_positive.
Notation exp_neg := real_exp_neg.
Notation exp_neg_pos := real_exp_neg_pos.
Notation log := real_log.

(* ===================================================================== *)
(* Section BBDBridgeSumSupply: the realized-reading supply section.       *)
(*                                                                       *)
(* Triage of the bridge interface slots: the three sum premises           *)
(* (extensionality / additivity / left linearity) are resolvable -- the    *)
(* abstract [sumf] is fixed to [csm_sumf S enum] and each premise is      *)
(* supplied by a theorem below, thinning the out-of-section signature by  *)
(* three slots.  The remaining slots are genuine interface data: [D_pos]   *)
(* and [Z_pos] are the positivity certificates consumed by [inv_pos] and  *)
(* [log] (not derivable: the degenerate instance [D := zero] refutes       *)
(* them), [partition_condition] is the defining equation of the partition *)
(* sum, and [sup_compat]/[sup_log_exp_neg] are the log-interface supply   *)
(* slots closed at the Real level inside [UpReqLogCompD].                 *)
(* ===================================================================== *)
Section BBDBridgeSumSupply.

Variable S : Set.
Variable enum : list S.

(* The realized reading of the abstract sum: the list-folding sum over
   [enum], convertible with the [sumd_sumf] folding key of the supply
   slots. *)
Let sumf : (S -> Real) -> Real := csm_sumf S enum.

(* ---- supply theorems for the three sum premises ---- *)

(* Extensionality: pointwise equality is preserved by the finite sum. *)
Theorem bbridge_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S enum f g H).
Defined.

(* Left linearity: the sum commutes with left multiplication. *)
Theorem bbridge_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S enum a f).
Defined.

(* Additivity: the sum of a pointwise sum is the sum of the sums. *)
Theorem bbridge_sum_add_supply : forall f g : S -> Real,
  req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S enum f g).
Defined.

(* ---- section slots of the two bridges (positivity data kept) ---- *)
Variable base_loss : S -> Real.
Variable D : Real.
Variable D_pos : lt zero D.
Variable Z : Real.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Hypothesis sup_compat : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : Real,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* Bridge 1: the energy-in-log identity at the Real level.  The statement
   embeds the discharged witnesses of the bridge host; the proof instantiates
   the closed resolution lemma at the eight explicit slots, and the final
   conversion is closed by the same-body witnesses (both the distribution and
   its positivity certificate unfold to the identical composition of
   [inv_pos] and [exp_neg]). *)
Theorem bbridge_energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (@BBDFepWriteoff.bbd_boltzmann_dist
                                S base_loss D D_pos Z Z_pos s)
                            (@BBDFepWriteoff.bbd_boltzmann_positive
                                S base_loss D D_pos Z Z_pos s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  exact (logc_energy_in_log_boltzmann S base_loss D D_pos Z Z_pos
           sup_compat sup_log_exp_neg s).
Defined.

(* Bridge 2: the explicit free-energy identity, with all three sum
   premises supplied -- the out-of-section signature carries no sum slot.
   The proof instantiates the closed free-energy resolution lemma at the
   thirteen explicit slots, the three sum slots filled by the supply
   theorems above. *)
Theorem bbridge_free_energy_boltzmann_bridge :
  req (@BBDFepWriteoff.bbd_free_energy S sumf base_loss D
         (@BBDFepWriteoff.bbd_boltzmann_dist S base_loss D D_pos Z Z_pos)
         (@BBDFepWriteoff.bbd_boltzmann_positive S base_loss D D_pos Z Z_pos))
      (mult (opp D) (log Z Z_pos)).
Proof.
  exact (logc_free_energy_boltzmann S sumf
           bbridge_sum_ext_supply bbridge_sum_add_supply bbridge_sum_linear_supply
           base_loss D D_pos Z Z_pos partition_condition sup_compat sup_log_exp_neg).
Defined.

End BBDBridgeSumSupply.

(* ===================================================================== *)
(* Assumption audit: each of the five statements must be closed under the *)
(* global context.                                                        *)
(* ===================================================================== *)
Print Assumptions bbridge_sum_ext_supply.
Print Assumptions bbridge_sum_linear_supply.
Print Assumptions bbridge_sum_add_supply.
Print Assumptions bbridge_energy_in_log_boltzmann_bridge.
Print Assumptions bbridge_free_energy_boltzmann_bridge.
