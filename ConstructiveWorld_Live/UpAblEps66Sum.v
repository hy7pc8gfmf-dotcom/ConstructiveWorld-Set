(* ConstructiveWorld-Set -- the three sum properties instantiated on enum list sums. *)
(** * UpAblEps66Sum: the three sum properties (extensionality, order
    preservation, additivity) instantiated on enum list sums.

    Mission.  Extensionality (pointwise real_eq gives real_eq of the sums),
      order preservation (pointwise real_le gives real_le of the sums), and
      additivity (the sum of the termwise sum equals the real_plus of the
      sums): the concrete instances of the Section hypotheses
      real_sum_over_S_ext / real_sum_over_S_le / real_sum_over_S_add of
      S08_RealMainlineDPO, with the sum operator instantiated as
      [e66s_sumf]; plus the fully concrete bool-carrier instance
      ([e66s_flag_enum] := true::false::nil) with no residual abstract
      variables.

    Dependencies.  This development: [S01_BaseRing] .. [S15_TailFEPUp]
      (containing S08_RealMainlineDPO), [UpReqSumD] (sumd_sum_ext /
      sumd_sum_le / sumd_sum_add and the sum operator sumd_sumf); Stdlib
      [Extraction], [List].

    References.  mathlib Finset.sum_congr / Finset.sum_le_sum / map_sum
      (extensionality, order preservation, additivity of finite sums);
      the same-name ConstructiveWorld-Main baseline.

    Constructivity.  All statements Set-layer (real_eq / real_le are
      Set-valued predicates, zero bare Prop); axiom-free, all Qed; the core
      piece [e66s_sumf] is extractable.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpAblEps66Sum.v] (direct call, cpu_guard wrapped). *)

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

(* ================= §1 instantiating the three sum properties on enum list sums ========= *)
(* The statements match the Section hypotheses real_sum_over_S_ext /
   real_sum_over_S_le / real_sum_over_S_add of S08_RealMainlineDPO, with
   only the sum operator instantiated as e66s_sumf. *)
(* ============================================================ *)
Section E66SumD.

Context (S0 : Set).
Context (enum0 : list S0).

(* The instance of the sum operator: the enum list sum, a transparent
   Definition; unfolding gives sumd_sumf. *)
Definition e66s_sumf (f : S0 -> Real) : Real := sumd_sumf S0 enum0 f.

(* Property 1 (extensionality of the sum): if two functions are pointwise
   real_eq-equal, their enum list sums are real_eq-equal.  Derived directly
   from sumd_sum_ext of UpReqSumD; the equality face real_eq and the
   donor-interface req are the same name under the Real instance. *)
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

(* Property 2 (order preservation of the sum): if two functions satisfy
   real_le (f s) (g s) pointwise, their enum list sums satisfy real_le.
   Derived directly from sumd_sum_le of UpReqSumD, the empty-list case
   handled by le_refl, so the statement needs no nonemptiness premise; the
   order face real_le and the donor-interface le are the same name. *)
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

(* Property 3 (additivity of the sum): the list sum of the termwise sum of
   two functions equals the real_plus of their list sums; derived directly
   from sumd_sum_add of UpReqSumD, the reordering of the summation handled
   by req_plus_exchange. *)
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
(* §2 the fully concrete instance on the bool carrier: with bool as the carrier *)
(*   and true::false::nil as the enumeration, the three sum properties hold on *)
(*   the Cauchy-real layer Real over a fully concrete carrier, with no residual *)
(*   abstract variables; the Set-layer instances of the abstract carrier S of the *)
(*   S08 sections land here. *)
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

(* ============ extraction check ========================================== *)
(* The only computational content of this file is the sum-carrier piece
   e66s_sumf (the enum list sum, defined by a list fold); its OCaml output
   is extracted to check the computational face.
   The three property theorems live at the equality and order-predicate
   level, are not computational content, and do not enter the substance of
   the extraction output.
   Extraction target: e66s_G3_sumf.ml. *)
Set Extraction Output Directory "_tab5_g3out".
Extraction "e66s_G3_sumf.ml" e66s_sumf.

(* Assumption-closure check: the assumption closures of the following
   theorems should be empty (Closed). *)
Print Assumptions e66s_real_sum_over_S_ext.
Print Assumptions e66s_real_sum_over_S_le.
Print Assumptions e66s_real_sum_over_S_add.
Print Assumptions e66s_flag_ext.
Print Assumptions e66s_flag_le.
Print Assumptions e66s_flag_add.
