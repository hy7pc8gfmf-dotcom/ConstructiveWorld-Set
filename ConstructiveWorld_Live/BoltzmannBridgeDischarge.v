(* ========================================================================= *)
(* BoltzmannBridgeDischarge.v — real-layer discharge of the Boltzmann        *)
(* distribution and free-energy bridge statements of the generalized         *)
(* mainline.                                                                 *)
(*                                                                           *)
(* Mission.  Close the two interface assumptions left open by the pilot      *)
(*   sections of the log-free-energy development, restated verbatim over     *)
(*   named witnesses: [bbd_energy_in_log_boltzmann_bridge]                   *)
(*   (loss s = -D * (log (dist s) + log Z)) and                              *)
(*   [bbd_free_energy_boltzmann_bridge] (F = -D * log Z), where the          *)
(*   Boltzmann distribution [dist s = exp (-(1/D) * loss s) / Z] lives over  *)
(*   the partition sum Z and the free energy F is the expected loss plus D   *)
(*   times the expected negative log-likelihood.  Both close by              *)
(*   full-slot instantiation of the resolution lemmas in                *)
(*   [UpReqLogCompD].                                                        *)
(* Dependencies.  The base modules S01_BaseRing through S15_TailFEPUp (see   *)
(*   the Require lines below), UpReqLogCompD, and Stdlib Extraction only.    *)
(* References.  Boltzmann-Gibbs statistics: the free-energy closed form      *)
(*   F = -T * log Z and the identity loss s = -T * log (dist s).             *)
(* Constructivity.  Every statement, field and witness is carried by Set:    *)
(*   the equality face is the per-epsilon carrier [real_eq], the order face  *)
(*   is the sigma-type carrier [real_lt]; no carrier is a proposition.       *)
(*   Definitions and constructive statements are transparent (Defined) so    *)
(*   conversion and extraction see every witness; statements extract with    *)
(*   [Obj.magic] = 0.                                                        *)
(* Build.  coqc -native-compiler no -q -Q . "" BoltzmannBridgeDischarge.v    *)
(*   in a directory holding the dependency .vo group.                        *)
(* ========================================================================= *)

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

(* Carrier pinning (the [UpReqLogCompD]/[G05_LogSmall] precedent).  The
   interface class [RealInterfaceEnhancedSetoid] is a zero-argument class in
   this development and the carrier R is pinned to the global [Real] by the
   [Notation R := Real] at the top of [UpReqLogCompD].  The field names used
   below are re-pinned to their top-level [real_]* globals, completing the
   small set the dependency chain does not re-export; this file therefore
   does NOT import the class module, so the whole algebra face stays in the
   one canonical scope. *)
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

Module BBDFepWriteoff.
Section BBDFepWriteoff.

(* Section slots, verbatim against the pilot-section signatures of the
   generic mainline host developments. *)
Variable S : Set.

(* The [req]-interface slots of the explicit sum (host verbatim). *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* The remaining section slots (host verbatim). *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* The two supply slots this section opens: the resolution lemmas below take
   log-compatibility and the exp/log adjoint as explicit assumptions, while
   the host pilot sections leave them as interface assumptions.  The real-
   level closures of both are supplied inside UpReqLogCompD. *)
Hypothesis sup_compat : forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Hypothesis sup_log_exp_neg : forall u : R,
  req (log (exp_neg u) (exp_neg_pos u)) (opp u).

(* Section witnesses: the host definitions, prefixed [bbd_] to stay
   name-disjoint from the resolution witnesses. *)
Definition bbd_positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition bbd_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
Definition bbd_free_energy (p : S -> R) (Hp : bbd_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition bbd_normalized (p : S -> R) : Set := req (sumf p) one.
Definition bbd_rminus (a b : R) : R := plus a (opp b).

(* Positivity of the Boltzmann distribution: the carrier of the log in the
   statements below.  Transparent so that the conversion closing the two
   bridges against the resolution witnesses can delta-reduce it. *)
Definition bbd_boltzmann_positive : bbd_positive_dist bbd_boltzmann_dist.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Defined.

(* Bridge 1.  The loss of a state equals minus D times the sum of the log of
   its Boltzmann weight and the log of the partition sum; closed by the
   energy-in-log resolution lemma instantiated at the eight explicit section
   slots, the final conversion closed by the same-body witnesses. *)
Theorem bbd_energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (bbd_boltzmann_dist s) (bbd_boltzmann_positive s))
                           (log Z Z_pos)))).
Proof.
  intro s.
  exact (logc_energy_in_log_boltzmann S base_loss D D_pos Z Z_pos
           sup_compat sup_log_exp_neg s).
Defined.

(* Bridge 2.  The free energy of the Boltzmann distribution equals minus D
   times the log of the partition sum; closed by the free-energy resolution
   lemma instantiated at the thirteen explicit section slots. *)
Theorem bbd_free_energy_boltzmann_bridge :
  req (bbd_free_energy bbd_boltzmann_dist bbd_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).
Proof.
  exact (logc_free_energy_boltzmann S sumf sum_ext sum_add sum_linear
           base_loss D D_pos Z Z_pos partition_condition
           sup_compat sup_log_exp_neg).
Defined.

End BBDFepWriteoff.
End BBDFepWriteoff.

(* Extraction audit: one command, both statement names, so the extracted
   modules reflect the full surface; the assumption audit must report both
   statements closed under the global context. *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Separate Extraction BBDFepWriteoff.bbd_energy_in_log_boltzmann_bridge
  BBDFepWriteoff.bbd_free_energy_boltzmann_bridge.

Print Assumptions BBDFepWriteoff.bbd_energy_in_log_boltzmann_bridge.
Print Assumptions BBDFepWriteoff.bbd_free_energy_boltzmann_bridge.
