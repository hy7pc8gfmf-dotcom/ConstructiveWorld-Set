(* Mission.  Ablation theorems for the EvictIdReq sum-interface face of the
   baseline module G13_EvictFam: at the concrete enumerated finite-sum operator
   [sumd_sumf S enum], the three interface assumption slots -- affine scaling
   [sum_linear], distribution over pointwise sums [sum_add], and congruence
   [sum_ext] -- hold unconditionally.  The interface section's premise
   structure therefore thins to the pure data slots (the enumeration list),
   and each assumption slot is discharged by a named theorem.
Dependencies.  Stdlib [List].  Requires the backbone [S01_BaseRing] through
   [S15_TailFEPUp] plus [UpReqSumD] (operators [sumd_sumf]/[sumd_list_sum])
   of this development.  The interface class [RealInterfaceEnhancedSetoid]
   is unparameterized over the global Cauchy real [Real]; statements are
   fixed to its global instance [RealEnhancedReal] (fields resolve by
   instance search).
References.  This development.  Statement faces are carried over from the
   [EvictIdReq] section of the baseline module G13_EvictFam (slots at its
   lines 435/438/441), instantiated at [sumf := sumd_sumf S enum]; the
   discharge proofs follow the list-induction chains of [UpReqSumD]
   ([sumd_list_sum_linear]/[sumd_list_sum_ext] and companions).
Constructivity.  All statements are carried by [Set], stated on the
   definitional [real_eq] carrier (conversion-identical to the interface
   field [req] at the global instance; the extraction-clean registered
   face); proofs are pure term-mode chains over interface fields
   ([req_refl]/[req_sym]/[req_trans]/[req_plus_compat], [plus_assoc]/
   [plus_comm]/[plus_zero], [distrib], [mult_zero]); each theorem carries
   its own [Print Assumptions] verdict at file end.
Build.  [rocq c -native-compiler no -q -Q . ""] (Rocq 9.1.0); exit 0; the
   first eight bytes of the artifact are [436f7121 00015ff4]. *)

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

(* Interface-face note (one-repair-round clause; registered precedent: the
   same adaptation in UpReqAlgebra and UpDebtSqrtAbsReq, class declaration at
   S07_RealSetoidExpLog "Class RealInterfaceEnhancedSetoid").  The baseline
   EvictIdReq section was written against the older parameterized-interface
   world (Context {R : Set} + Context {RIS : RealInterfaceEnhancedSetoid R}).
   In this tree the interface class is unparameterized: its carrier is the
   global Real and its fields resolve through the global instance
   [RealEnhancedReal].  The per-theorem binder head
   [forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R}] is therefore
   replaced by the notation below, and each quantifier face keeps its
   remaining binders [(S : Set) (enum : list S) (a : R) (f : S -> R)] with
   the instance argument resolved by instance search.  The mathematical
   content of every statement is unchanged. *)
Notation R := Real.

(* ============ EvictIdReq sum-interface face (baseline slots 435/438/441) ============ *)
(* Out-of-section form: R is the notation above (the unparameterized class
   carrier); the interface assumption slots are discharged at the concrete
   instance sumf := sumd_sumf S enum. *)

(* A1 <- slot sum_linear.  Baseline face: forall (a : R) (f : S -> R),
   req (sumf (fun s => mult a (f s))) (mult a (sumf f)). *)
Theorem uabT12_g13_sum_linear :
  forall (S : Set) (enum : list S) (a : R) (f : S -> R),
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

(* A2 <- slot sum_add.  Baseline face: forall f g : S -> R,
   req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)). *)
Theorem uabT12_g13_sum_add :
  forall (S : Set) (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - simpl. exact (req_sym _ _ (plus_zero _)).
  - simpl.
    exact (req_trans (plus (plus (f x) (g x)) (@sumd_list_sum _ (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t))) (plus (plus (f x) (@sumd_list_sum _ f t)) (plus (g x) (@sumd_list_sum _ g t))) (req_plus_compat _ _ _ _ (req_refl _) IH) (req_trans (plus (plus (f x) (g x)) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t))) (plus (f x) (plus (g x) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t)))) (plus (plus (f x) (@sumd_list_sum _ f t)) (plus (g x) (@sumd_list_sum _ g t))) (req_sym _ _ (plus_assoc (f x) (g x) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t)))) (req_trans (plus (f x) (plus (g x) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t)))) (plus (f x) (plus (@sumd_list_sum _ f t) (plus (g x) (@sumd_list_sum _ g t)))) (plus (plus (f x) (@sumd_list_sum _ f t)) (plus (g x) (@sumd_list_sum _ g t))) (req_plus_compat (f x) (f x) (plus (g x) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t))) (plus (@sumd_list_sum _ f t) (plus (g x) (@sumd_list_sum _ g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (@sumd_list_sum _ f t) (@sumd_list_sum _ g t))) (plus (plus (g x) (@sumd_list_sum _ f t)) (@sumd_list_sum _ g t)) (plus (@sumd_list_sum _ f t) (plus (g x) (@sumd_list_sum _ g t))) (plus_assoc (g x) (@sumd_list_sum _ f t) (@sumd_list_sum _ g t)) (req_trans (plus (plus (g x) (@sumd_list_sum _ f t)) (@sumd_list_sum _ g t)) (plus (plus (@sumd_list_sum _ f t) (g x)) (@sumd_list_sum _ g t)) (plus (@sumd_list_sum _ f t) (plus (g x) (@sumd_list_sum _ g t))) (req_plus_compat (plus (g x) (@sumd_list_sum _ f t)) (plus (@sumd_list_sum _ f t) (g x)) (@sumd_list_sum _ g t) (@sumd_list_sum _ g t) (plus_comm (g x) (@sumd_list_sum _ f t)) (req_refl (@sumd_list_sum _ g t))) (req_sym _ _ (plus_assoc (@sumd_list_sum _ f t) (g x) (@sumd_list_sum _ g t)))))) (plus_assoc (f x) (@sumd_list_sum _ f t) (plus (g x) (@sumd_list_sum _ g t)))))).
Qed.

(* A3 <- slot sum_ext.  Baseline face: forall f g : S -> R,
   (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g). *)
Theorem uabT12_g13_sum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.

  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl _).
  - simpl. exact (req_plus_compat _ _ _ _ (H x) IH).
Qed.

(* ============ Print Assumptions close-out (per-theorem verdicts) ============ *)
Print Assumptions uabT12_g13_sum_linear.
Print Assumptions uabT12_g13_sum_add.
Print Assumptions uabT12_g13_sum_ext.
