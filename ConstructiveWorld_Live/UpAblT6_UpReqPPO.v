(* Five-field index | Mission.  Formalization of the properties stated by the
   theorem declarations of this unit: the three sumf-interface theorems of the
   ReqPPOAdvantage section (UpReqPPO.v L72/L74/L77 sum_ext/sum_add/sum_linear,
   statement faces quoted verbatim), discharged at the concrete finite-sum
   operator sumf := sumd_sumf S enum taken from UpReqSumD, with each
   interface-assumption slot reduced to a pure data slot (the enumeration
   list); the premise face thins to exactly that data slot.
   Dependencies.  S01_BaseRing through S15_TailFEPUp and UpReqSumD of this
     development (read-only use, zero edits to the tree of origin); Stdlib
     [List] with [ListNotations]; the record-field view of
     RealInterfaceEnhancedMod is imported so [req]/[plus]/[mult] resolve on
     the Real carrier instance.
   References.  Discharge instances sumd_sum_ext (UpReqSumD L113),
     sumd_sum_add (L185), sumd_sum_linear (L143); the nontrivial content
     lives in the list-induction chains of UpReqSumD, consumed here directly
     without inflation; carrier note: the original section
     Context {R}{RIS} has zero occurrences in the use face (eliminated on
     exit from the section), the actual type of sumf is (S -> Real) -> Real,
     so this unit pins the carrier to Real and the sumd family resolves
     through the global instance.
   Constructivity.  Zero extraction-barrier statements: all three conclusions
     are carried by real_eq over the Real carrier instance, so the whole
     statement face is Set-level (the source faces name the req field of
     RealInterfaceEnhancedSetoid; this unit writes its instance value
     real_eq, which RealEnhancedReal sets req := real_eq, so the meaning is
     unchanged); each theorem ends with Print Assumptions and reports
     Closed under the global context.
   Build.  rocq c -native-compiler no -q -Q . "" UpAblT6_UpReqPPO.v
     compiles cleanly (exit 0); the artifact starts with the bytes
     436f7121 00015ff4. *)

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

(* ============ ReqPPOAdvantage (UpReqPPO.v L67-79) ============ *)
(* The original section Context {R}{RIS} has zero occurrences in the use face  *)
(* (eliminated on exit from the section); the actual type of sumf is           *)
(* (S -> Real) -> Real; this unit pins the carrier to Real (global instance    *)
(* resolution) and swaps the sum operator to the sumd_sumf S enum instance.    *)

(* A1 <- L72 sum_ext; discharge instance sumd_sum_ext@UpReqSumD:113. *)
Theorem uabT6_rppo_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl _).
  - simpl. exact (req_plus_compat _ _ _ _ (H x) IH).
Qed.

(* A2 <- L74 sum_add; discharge instance sumd_sum_add@UpReqSumD:185. *)
Theorem uabT6_rppo_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> Real),
    real_eq (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (plus_zero _)).
  - simpl.
        exact (req_trans (plus (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat _ _ _ _ (req_refl _) IH) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_sym _ _ (plus_assoc (f x) (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (req_trans (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (f x) (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus_assoc (g x) (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_trans (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (g x) (sumd_list_sum S f t)) (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t) (sumd_list_sum S g t) (plus_comm (g x) (sumd_list_sum S f t)) (req_refl (sumd_list_sum S g t))) (req_sym _ _ (plus_assoc (sumd_list_sum S f t) (g x) (sumd_list_sum S g t)))))) (plus_assoc (f x) (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))))).
Qed.

(* A3 <- L77 sum_linear; discharge instance sumd_sum_linear@UpReqSumD:143. *)
Theorem uabT6_rppo_sum_linear :
  forall (S : Set) (enum : list S) (a : Real) (f : S -> Real),
    real_eq (sumd_sumf S enum (fun s => mult a (f s)))
      (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (mult_zero _)).
  - simpl.
    exact (req_trans _ _ _
             (req_plus_compat _ _ _ _ (req_refl _) IH)
             (req_sym _ _ (distrib _ _ _))).
Qed.

(* ============ PA closure section (per-theorem Closed reading) ============ *)
Print Assumptions uabT6_rppo_sum_ext.
Print Assumptions uabT6_rppo_sum_add.
Print Assumptions uabT6_rppo_sum_linear.
