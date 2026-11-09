(* ============================================================
   Mission.  the three summation properties hold on enum list sums:
     extensionality (pointwise real_eq gives real_eq of the sums),
     order preservation (pointwise real_le gives real_le of the
     sums) and additivity (the sum of the pointwise sums equals
     real_plus of the two sums); concrete instances of the Section
     assumptions real_sum_over_S_ext / real_sum_over_S_le /
     real_sum_over_S_add of S08_RealMainlineDPO, plus a fully
     concrete instance over the bool carrier with enum
     true::false::nil with no residual abstract variable.
     replacement theorem list: e66s_real_sum_over_S_ext /
     e66s_real_sum_over_S_le / e66s_real_sum_over_S_add (3 items).
   Dependencies.  the libraries named by the in-file Require face;
     CW_ConstructiveWorld_219 (containing S08_RealMainlineDPO),
     UpReqSumD (sumd_sum_ext / sumd_sum_le / sumd_sum_add, the
     summing operator sumd_sumf).
   References.  mathlib Finset.sum_congr / Finset.sum_le_sum /
     map_sum (extensionality, order preservation and additivity of
     finite sums).
   Constructivity.  all statements live in Set (real_eq and
     real_le are Set-valued predicates, no bare Prop in the
     statement face); zero axioms, all proofs close by Qed,
     assumption closures of the six theorems verified empty by
     Print Assumptions; the core piece e66s_sumf is extractable.
   Build.  coqc -native-compiler no -q -Q . "" ; magic
     [436f7121 000160bc].
   ============================================================ *)

From Stdlib Require Import Extraction.
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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ §1 the three summation properties instantiated on ======= *)
(* enum list sums; the statements agree with the Section assumptions     *)
(* real_sum_over_S_ext / real_sum_over_S_le / real_sum_over_S_add of     *)
(* S08_RealMainlineDPO, with the summing operator instantiated to        *)
(* e66s_sumf.                                                            *)
(* ====================================================================== *)
Section E66SumD.

Context (S0 : Set).
Context (enum0 : list S0).

(* the instance of the summing operator: the enum list sum, a transparent *)
(* Definition, unfolds to sumd_sumf.                                      *)
Definition e66s_sumf (f : S0 -> Real) : Real := sumd_sumf S0 enum0 f.

(* property 1 (extensionality of the sum): if the two functions agree     *)
(* pointwise under real_eq, then their enum list sums agree under         *)
(* real_eq; it follows directly from sumd_sum_ext of UpReqSumD, the       *)
(* equality face real_eq bearing the name req of the donor interface at   *)
(* the Real instance.                                                     *)
Theorem e66s_real_sum_over_S_ext :
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (e66s_sumf f) (e66s_sumf g).
Proof.
  intros f g H.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Qed.

(* property 2 (order preservation of the sum): if the two functions       *)
(* satisfy real_le (f s) (g s) pointwise, then their enum list sums       *)
(* satisfy real_le; it follows directly from sumd_sum_le of UpReqSumD,    *)
(* the empty list case being handled by le_refl, so the statement needs   *)
(* no nonemptiness side condition; the order face real_le bears the name  *)
(* le of the donor interface at the Real instance.                        *)
Theorem e66s_real_sum_over_S_le :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (e66s_sumf f) (e66s_sumf g).
Proof.
  intros f g H.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Qed.

(* property 3 (additivity of the sum): the list sum of the pointwise      *)
(* sums of the two functions equals real_plus of their list sums; it      *)
(* follows directly from sumd_sum_add of UpReqSumD, the reordering of     *)
(* the summation being handled by req_plus_exchange.                      *)
Theorem e66s_real_sum_over_S_add :
  forall (f g : S0 -> Real),
    real_eq (e66s_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (e66s_sumf f) (e66s_sumf g)).
Proof.
  intros f g.
  unfold e66s_sumf, sumd_sumf.
  induction enum0 as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                   (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                   (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))
             (plus (plus (f x) (sumd_list_sum S0 f t))
                   (plus (g x) (sumd_list_sum S0 g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t)
                (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))
                (req_refl (plus (f x) (g x))) IH)
             (real_plus_swap_mid (f x) (g x)
                (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))).
Qed.

End E66SumD.

(* ============================================================ *)
(* §2 fully concrete instance over a bool carrier: bool is taken as the  *)
(* carrier and true::false::nil as the enum, so the three summation      *)
(* properties hold on the Cauchy real layer Real over a fully concrete   *)
(* carrier with no residual abstract variable; the Set-layer instance of *)
(* the abstract carrier S of the S08 sections lands on this face.        *)
(*                                                                       *)
(* ============================================================ *)
Definition e66s_flag_enum : list bool := [true; false].
Definition e66s_flag_sumf (f : bool -> Real) : Real :=
  e66s_sumf bool e66s_flag_enum f.

Theorem e66s_flag_ext :
  forall (f g : bool -> Real),
    (forall s : bool, real_eq (f s) (g s)) ->
    real_eq (e66s_flag_sumf f) (e66s_flag_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_ext bool e66s_flag_enum f g H).
Qed.

Theorem e66s_flag_le :
  forall (f g : bool -> Real),
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (e66s_flag_sumf f) (e66s_flag_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_le bool e66s_flag_enum f g H).
Qed.

Theorem e66s_flag_add :
  forall (f g : bool -> Real),
    real_eq (e66s_flag_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (e66s_flag_sumf f) (e66s_flag_sumf g)).
Proof.
  intros f g.
  exact (e66s_real_sum_over_S_add bool e66s_flag_enum f g).
Qed.

(* ============ extraction check ======================================== *)
(* the only computational content of this file is the summation carrier  *)
(* piece e66s_sumf (the enum list sum, defined by a list fold); its      *)
(* OCaml output is extracted to check the computational face.  the three *)
(* property theorems live at the level of the equality and order         *)
(* predicates, are not computational content and do not enter the        *)
(* substance of the extraction output.                                   *)
(* extraction target: e66s_G3_sumf.ml.                                   *)
Set Extraction Output Directory "_tab5_g3out".
Extraction "e66s_G3_sumf.ml" e66s_sumf.

(* assumption-closure check: the assumption closures of the theorems     *)
(* below must be empty (Closed).                                         *)
Print Assumptions e66s_real_sum_over_S_ext.
Print Assumptions e66s_real_sum_over_S_le.
Print Assumptions e66s_real_sum_over_S_add.
Print Assumptions e66s_flag_ext.
Print Assumptions e66s_flag_le.
Print Assumptions e66s_flag_add.
