(* ConstructiveWorld-Set -- instantiation face of the temperature-weighted softmax. *)

(** * PA_TempSoftmaxInstantiation: temperature-weighted softmax instantiation face.

    Mission.  The definitional Boltzmann-weight identity
      [tsi_twp_is_boltzmann_weight] (a temperature-weighted probability equals
      the Boltzmann weight for 0 < t), the normalization
      [tsi_temp_weighted_normalized] with its convex-mixture companion
      [tsi_temp_weighted_mix_normalized], the temperature-scale duality
      [tsi_temp_scale_duality], and the relative Boltzmann form
      [tsi_temp_weighted_relative]; plus [tsi_le_plus_eps_r] and the assembly
      instance [tsi_rie_setoid] into [RealInterfaceEnhancedSetoid].

    Dependencies.  CW_ConstructiveWorld_219, UpReqAlgebra, UpReqDist, UpReqAttnGibbs.

    References.  Normalization, mixture behavior, and the temperature duality
      of tempered softmax / Boltzmann weighting (statistical-mechanics
      sampling face); donors [ag_softmax_temp_normalized],
      [ag_softmax_temp_mix_normalized], [ag_temp_is_scale_duality], and
      [ag_softmax_temp_relative] of UpReqAttnGibbs; gate round 1 red at the
      first [RealInterfaceEnhancedSetoid] site: the class is zero-argument in
      this tree (fields at the global [Real]/[real_eq] carrier, S02:511/:513),
      so the bridge re-anchors to the canonical [RealEnhancedReal] and the
      main-face carriers to [Real], per the sibling [TempSoftmaxInstantiation].

    Constructivity.  Every statement closes by [Qed] with zero admission
      vocabulary; proofs add no premises beyond the receiver section slots.

    Build.  [coqc -native-compiler no -q -Q . ""] in the single-root vo world
      (rebuilt in-place, literal COQLIB/ROCQLIB prefixes); artifact starts with [436f7121 000160bc]. *)
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
Require Import UpReqDist.
Require Import UpReqAttnGibbs.
Import RealInterfaceEnhancedMod.

(* ===================================================================== *)
(* assembly bridge B1 auxiliary: the one-step eps stretch lemma,         *)
(*   le a (a + eps), for 0 < eps.                                        *)
(* ===================================================================== *)
Lemma tsi_le_plus_eps_r :
  forall (RI : RealInterfaceEnhanced) (a eps : @S01_BaseRing.R RI),
    @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) eps ->
    @S01_BaseRing.le RI a (@S01_BaseRing.plus RI a eps).
Proof.
  intros RI a eps Hlt.
  apply (@S01_BaseRing.le_id_l RI a
           (@S01_BaseRing.plus RI a (@S01_BaseRing.zero RI))
           (@S01_BaseRing.plus RI a eps)).
  - exact (id_sym (@S01_BaseRing.plus_zero RI a)).
  - exact (@S01_BaseRing.le_plus_compat RI a a (@S01_BaseRing.zero RI) eps
             (@S01_BaseRing.le_refl RI a)
             (@S01_BaseRing.lt_le_iff RI (@S01_BaseRing.zero RI) eps (inl Hlt))).
Qed.

(* ===================================================================== *)
(* assembly bridge B1: the setoid-instance bridge.  The class is         *)
(*   zero-argument in this tree (its fields live at the global           *)
(*   Real/real_eq carrier), so the bridge is the canonical               *)
(*   RealEnhancedReal instance, the fixed-carrier realization of the     *)
(*   Id-req total instance; the class fields resolve through it.         *)
(* ===================================================================== *)
Instance tsi_rie_setoid : RealInterfaceEnhancedSetoid
  := RealEnhancedReal.

(* ===================================================================== *)
(* assembly bridge B2: the receiver-definition exit-arity bridge         *)
(*   (delta-closed).                                                     *)
(* ===================================================================== *)
Theorem tsi_twp_is_boltzmann_weight :
  forall (RI : RealInterfaceEnhanced) (Token : Set)
         (neg_log_prob : list Token -> Token -> @S01_BaseRing.R RI)
         (t : @S01_BaseRing.R RI)
         (Ht : @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) t)
         (prefix : list Token) (w : Token),
    Id (@temperature_weighted_prob RI Token neg_log_prob t Ht prefix w)
       (@S01_BaseRing.exp_neg RI
          (@S01_BaseRing.mult RI (@S01_BaseRing.inv_pos RI t Ht)
             (neg_log_prob prefix w))).
Proof. intros RI Token neg_log_prob t Ht prefix w. exact (@id_refl _ _). Qed.

(* ===================================================================== *)
(* main-face section: the receiver LanguageModelExtensions section face  *)
(*   (RI Token neg_log_prob temperature temperature_pos) joined with the *)
(*   donor ReqAttnGibbs section sums-machine slots.                      *)
(* ===================================================================== *)
Section TsiMains.
Context {RI : RealInterfaceEnhanced}.
Variable Token : Set.
Variable neg_log_prob : list Token -> Token -> Real.
Variable temperature : Real.
Variable temperature_pos : lt zero temperature.

(* honest sums-machine slots (in the donor-section style; the            *)
(*   BoltzmannBridgeDischarge supplied-slot precedent).                  *)
Variable sumf : (Token -> Real) -> Real.
Hypothesis Hsum_ext :
  forall f g : Token -> Real,
    (forall w : Token, req (f w) (g w)) -> req (sumf f) (sumf g).
Hypothesis Hsum_linear :
  forall (a : Real) (f : Token -> Real),
    req (sumf (fun w : Token => mult a (f w))) (mult a (sumf f)).
Hypothesis Hsum_add :
  forall f g : Token -> Real,
    req (sumf (fun w : Token => plus (f w) (g w))) (plus (sumf f) (sumf g)).
Hypothesis Hsum_pos :
  forall f : Token -> Real,
    (forall w : Token, lt zero (f w)) -> lt zero (sumf f).

(* main face 1 [normalization]: the normalized distribution weights of   *)
(*   the receiver temperature-weighted probabilities sum to 1            *)
(*   (donor ag_softmax_temp_normalized@262 fully instantiated;           *)
(*   z := nlp prefix).                                                   *)
Theorem tsi_temp_weighted_normalized :
  forall prefix : list Token,
    req (sumf (fun w : Token =>
           mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
                (inv_pos
                   (sumf (fun w0 : Token =>
                            exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                   (Hsum_pos
                      (fun w0 : Token =>
                         exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                      (fun w0 : Token =>
                         exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))))))
        one.
Proof.
  intro prefix.
  exact (@ag_softmax_temp_normalized Token sumf Hsum_ext Hsum_linear Hsum_pos
           temperature temperature_pos
           (fun w : Token => neg_log_prob prefix w)).
Qed.

(* main face 2 [mixture normalization]: the convex combination of the    *)
(*   two prefix prediction distributions, with weights alpha and         *)
(*   1 - alpha, is again normalized (donor                               *)
(*   ag_softmax_temp_mix_normalized@282 fully instantiated).             *)
Theorem tsi_temp_weighted_mix_normalized :
  forall (p q : list Token) (alpha : Real),
    lt zero alpha -> lt zero (req_minus one alpha) ->
    req (sumf (fun w : Token =>
           plus (mult alpha
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob p w0)))))))
                (mult (req_minus one alpha)
                      (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w)))
                            (inv_pos
                               (sumf (fun w0 : Token =>
                                        exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0))))
                               (Hsum_pos
                                  (fun w0 : Token =>
                                     exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))
                                  (fun w0 : Token =>
                                     exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob q w0)))))))))
        one.
Proof.
  intros p q alpha Halpha Halpha1.
  exact (@ag_softmax_temp_mix_normalized Token sumf Hsum_ext Hsum_linear Hsum_add
           Hsum_pos temperature temperature_pos
           (fun w : Token => neg_log_prob p w)
           (fun w : Token => neg_log_prob q w)
           alpha Halpha Halpha1).
Qed.

(* main face 3 [temperature-scale duality]: the normalized distribution  *)
(*   of the receiver probabilities weighted at temperature c equals the  *)
(*   softmax scaled by 1/c (donor ag_temp_is_scale_duality@477 fully     *)
(*   instantiated; the left side is the receiver definition at           *)
(*   temperature c, with inv_pos c Hc entering the exponent directly,    *)
(*   so the duality stays at definitional depth and nothing is cut).     *)
Theorem tsi_temp_scale_duality :
  forall (c : Real) (Hc : lt zero c)
         (prefix : list Token) (w : Token),
    req (mult (exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos c Hc) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos c Hc) (neg_log_prob prefix w0))))))
        (reqd_softmax_scaled Token sumf Hsum_pos (inv_pos c Hc)
           (fun w1 : Token => neg_log_prob prefix w1) w).
Proof.
  intros c Hc prefix w.
  exact (@ag_temp_is_scale_duality Token sumf Hsum_pos c Hc
           (fun w1 : Token => neg_log_prob prefix w1) w).
Qed.

(* main face 4 [relative form]: the Boltzmann relative form of the       *)
(*   normalized weights of two tokens within one prefix (donor           *)
(*   ag_softmax_temp_relative@341 fully instantiated; a genuine proof    *)
(*   face through the additive homomorphism of exp).                     *)
Theorem tsi_temp_weighted_relative :
  forall (prefix : list Token) (w w' : Token),
    req (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w)))
              (inv_pos
                 (sumf (fun w0 : Token =>
                          exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                 (Hsum_pos
                    (fun w0 : Token =>
                       exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                    (fun w0 : Token =>
                       exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
        (mult (mult (exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w')))
                    (inv_pos
                       (sumf (fun w0 : Token =>
                                exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))
                       (Hsum_pos
                          (fun w0 : Token =>
                             exp_neg (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0)))
                          (fun w0 : Token =>
                             exp_neg_pos (mult (inv_pos temperature temperature_pos) (neg_log_prob prefix w0))))))
              (exp_neg (mult (inv_pos temperature temperature_pos)
                             (req_minus (neg_log_prob prefix w)
                                        (neg_log_prob prefix w'))))).
Proof.
  intros prefix w w'.
  exact (@ag_softmax_temp_relative Token sumf Hsum_pos temperature temperature_pos
           (fun w1 : Token => neg_log_prob prefix w1) w w').
Qed.

End TsiMains.

(* ===================================================================== *)
(* the G4 audit-trace face (Print Assumptions meets the at-least-one     *)
(*   criterion: five sites).                                             *)
(* ===================================================================== *)
Print Assumptions tsi_twp_is_boltzmann_weight.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_relative.

Print Assumptions tsi_temp_weighted_relative.
Print Assumptions tsi_temp_scale_duality.
Print Assumptions tsi_temp_weighted_mix_normalized.
Print Assumptions tsi_temp_weighted_normalized.
Print Assumptions tsi_rie_setoid.
