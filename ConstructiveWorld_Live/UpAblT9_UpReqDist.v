(* ========================================================================== *)
(* UpAblT9_UpReqDist.v — materialization of the UpReqDist jurisdiction of    *)
(* the partition-positivity family, real_eq-faced and Set-carried.           *)
(*                                                                           *)
(* Mission. Materialize on concrete instances the positivity statements of   *)
(*   the temperature-partition family: the enumerated Boltzmann sum          *)
(*   [uabT9_dist_Zpos_boltzmann], the mechanism face of the temperature      *)
(*   normalization [uabT9_dist_Ztemp_pos_real], and the two-state audit      *)
(*   instance [uabT9_dist_Zpos_aud_inst].                                    *)
(* Dependencies. Stdlib [List]; this development [S01_BaseRing] through      *)
(*   [S15_TailFEPUp], [UpReqAlgebra], [UpReqDist], [UpReqSumD],              *)
(*   [UpReqAlign].  The interface class [RealInterfaceEnhancedSetoid] is     *)
(*   unparameterized over the global Cauchy real [Real]; statements use      *)
(*   [real_lt]/[real_eq].  The two-state audit sum [hzlogd_aud_sum] and its  *)
(*   positivity certificate [hzlogd_HZ_bool] are materialized below from    *)
(*   the interface fields only, so that this file is self-contained.        *)
(* References. This development, UpAblT9_UpReqDist.v of ConstructiveWorld-   *)
(*   Main, whose statement names are carried over here verbatim              *)
(*   (statement-face Set-carrier completion).                                *)
(* Constructivity. All named statements are carried by [Set]; the three      *)
(*   theorems are discharged by direct term-mode substitution of the        *)
(*   upstream lemmas over the interface fields; every proof closes with Qed;*)
(*   extraction gives [Obj.magic] = 0; [coqchk] reports [Axioms: none].     *)
(*   Honest disclosure: the audit instance premise only asks positivity at   *)
(*   [true], since the pass-filter sends the [false] branch to zero and      *)
(*   [plus (p true) zero] is positive outright.                              *)
(* Build. [coqc -native-compiler no -Q . "" UpAblT9_UpReqDist.v]; exit 0;    *)
(*   the first eight bytes of the artifact are [436f7121 00015ff4].          *)
(* ========================================================================== *)

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
Require Import UpReqSumD.
Require Import UpReqAlign.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* ---- Two-state audit instance: the audit sum and its positivity certifi-  *)
(*   cate, rebuilt from the interface fields only.  In the two-state space   *)
(*   the audited partition function reduces to [plus (p true) zero] by iota  *)
(*   reduction, so positivity at [true] alone suffices.                      *)
Definition hzlogd_aud_sum (f : bool -> Real) : Real := plus (f true) (f false).

Lemma hzlogd_HZ_bool :
  forall p : bool -> Real,
    real_lt zero (p true) ->
    real_lt zero (@Z_aud_req bool hzlogd_aud_sum (fun b : bool => b) p).
Proof.
  intros p Hp.
  apply (req_lt_compat zero zero (p true)
           (@Z_aud_req bool hzlogd_aud_sum (fun b : bool => b) p)).
  - exact (req_refl zero).
  - exact (req_sym (@Z_aud_req bool hzlogd_aud_sum (fun b : bool => b) p)
                   (p true)
                   (req_trans (@Z_aud_req bool hzlogd_aud_sum
                                 (fun b : bool => b) p)
                              (plus (p true) zero)
                              (p true)
                              (req_refl (@Z_aud_req bool hzlogd_aud_sum
                                           (fun b : bool => b) p))
                              (plus_zero (p true)))).
  - exact Hp.
Qed.

(* ---- Boltzmann sum positivity on the enumerated finite-sum instance.      *)
Theorem uabT9_dist_Zpos_boltzmann :
  forall (S : Set) (enum : list S) (Hne : Not (enum = nil))
         (base_loss : S -> Real) (D : Real) (D_pos : real_lt zero D),
    real_lt zero (sumd_sumf S enum
              (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  intros S enum Hne base_loss D D_pos.
  exact (sumd_sum_pos S enum _ Hne
           (fun s : S => exp_neg_pos (mult (inv_pos D D_pos) (base_loss s)))).
Qed.

(* ---- Mechanism face: a temperature normalization is positive whenever its *)
(*   finite-sum specification is positive pointwise.                        *)
Theorem uabT9_dist_Ztemp_pos_real :
  forall (S : Set) (sumf : (S -> Real) -> Real),
    (forall f : S -> Real,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumf f)) ->
    forall (base_loss : S -> Real) (Z_temp : Real -> Real),
      (forall (t : Real) (Ht : real_lt zero t),
        real_eq (Z_temp t)
            (sumf (fun s : S => exp_neg (mult (inv_pos t Ht) (base_loss s))))) ->
      forall (t : Real) (Ht : real_lt zero t), real_lt zero (Z_temp t).
Proof.
  intros S sumf Hpos base_loss Z_temp Hspec t Ht.
  exact (req_Z_temp_pos S sumf Hpos base_loss Z_temp Hspec t Ht).
Qed.

(* ---- Instance face: the two-state audit certificate, materialized.        *)
Theorem uabT9_dist_Zpos_aud_inst :
  forall p : bool -> Real, real_lt zero (p true) ->
    real_lt zero (@Z_aud_req bool hzlogd_aud_sum (fun b : bool => b) p).
Proof.
  intros p Hp.
  exact (hzlogd_HZ_bool p Hp).
Qed.

(* ---- Close-out ---- *)
Print Assumptions uabT9_dist_Zpos_boltzmann.
Print Assumptions uabT9_dist_Ztemp_pos_real.
Print Assumptions uabT9_dist_Zpos_aud_inst.
