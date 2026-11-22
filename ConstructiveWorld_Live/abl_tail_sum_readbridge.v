(* ==========================================================================
   abl_tail_sum_readbridge.v — sum-read unification bridge.

   Mission.  One uniform reading of the enumerated finite sum for the tail
   hosts: the four sum laws (extensionality, left linearity, additive
   split, monotony) on the req/le faces, the same four on the
   real_eq/real_le faces, and the pointwise zero-discharge slot on the
   two-point boolean enumeration.  The folding key is fixed to [sumd_sumf]
   (canonical read of the root pieces cms_sum_ext/linear/add/le,
   ConcMixSelFeed.v); the zero slot is discharged by
   [uabT1_rte_fsum_zero_nonneg] (UpAblT1_UpReqTempEntropy.v).

   Dependencies.  S01_BaseRing..S15_TailFEPUp; UpReqSumD ([sumd_sumf],
   [sumd_in]); ConcMixSelFeed; UpAblT1_UpReqTempEntropy; Stdlib [List].
   The relation fields req/le are Notation-bound to the concrete S02
   carriers [real_eq]/[real_le] — the bindings the global instance
   [RealEnhancedReal] assigns; same form as ConcMixSelFeed.v.

   References.  This development; statement names carried over verbatim
   from the baseline module in ConstructiveWorld-Main (Set-carrier wash).

   Constructivity.  All named statements are Set-carried: conclusions in
   [real_eq]/[real_le] (Bishop per-eps [sigT] forms over the Cauchy
   real), membership as the Set-level family [sumd_in_fam].  All ten
   pieces end in [Defined] and derive by direct instantiation of the root
   pieces; the substantive chains live in those roots.  Extraction is
   magic-free on both faces; coqchk reports none.

   Build.  coqc -Q tree_root "" abl_tail_sum_readbridge.v exits 0; artifact bytes 436f7121 000160bc.
   ========================================================================== *)

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
Require Import ConcMixSelFeed.
Require Import UpAblT1_UpReqTempEntropy.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* Carrier binding of the statement-face relation fields, same form as *)
(* ConcMixSelFeed.v: [req]/[le] name the concrete S02_CauchyComplete   *)
(* Set carriers [real_eq]/[real_le] -- the bindings the global instance *)
(* [RealEnhancedReal] assigns to the class fields.  The binding keeps   *)
(* the statement terms on the informative concrete carriers, so the     *)
(* extracted code carries no boxed class-field projections.            *)
Notation req := real_eq.
Notation le := real_le.

(* ---- Section 1: the four sum laws on the req/le face.  The folding *)
(* ---- key is [sumd_sumf S0 en], generic in the carrier [S0] and the *)
(* ---- enumeration [en]. --------------------------------------------- *)

(* Extensionality of the enumerated sum under pointwise identification. *)
Theorem tspbr_sum_ext : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) -> req (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Defined.

(* Left linearity: the sum of a scalar multiple is the scalar multiple. *)
Theorem tspbr_sum_linear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => mult a (f s)))
        (mult a (sumd_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Defined.

(* Additive split of the sum over a pointwise sum of functions. *)
Theorem tspbr_sum_add :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => plus (f s) (g s)))
        (plus (sumd_sumf S0 en f) (sumd_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Defined.

(* Monotony: pointwise domination is preserved by the sum. *)
Theorem tspbr_sum_le :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, le (f s) (g s)) -> le (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_le S0 en f g H).
Defined.

(* ---- Section 2: the same four laws on the real_eq/real_le face.  The *)
(* ---- root pieces already conclude in the concrete carriers, since the *)
(* ---- Notations above name exactly those carriers; the [mult]/[plus]  *)
(* ---- projections reduce to [real_mult]/[real_plus] on the global     *)
(* ---- instance [RealEnhancedReal]. ----------------------------------- *)

(* Real-face extensionality. *)
Theorem tspbr_real_sum_ext :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_ext S0 en f g H).
Defined.

(* Real-face monotony. *)
Theorem tspbr_real_sum_le :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  exact (cms_sum_le S0 en f g H).
Defined.

(* Real-face left linearity. *)
Theorem tspbr_real_sum_linear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    real_eq (sumd_sumf S0 en (fun s : S0 => real_mult a (f s)))
            (real_mult a (sumd_sumf S0 en f)).
Proof.
  intros S0 en a f.
  exact (cms_sum_linear S0 en a f).
Defined.

(* Real-face additive split. *)
Theorem tspbr_real_sum_add :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    real_eq (sumd_sumf S0 en (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (sumd_sumf S0 en f) (sumd_sumf S0 en g)).
Proof.
  intros S0 en f g.
  exact (cms_sum_add S0 en f g).
Defined.

(* ---- Section 3: the pointwise zero-discharge slot on the two-point *)
(* ---- boolean enumeration.  Membership on [true :: false :: nil] is *)
(* ---- given directly by the two branches of the Set-level family    *)
(* ---- [sumd_in_fam]; the slot itself is the root discharge theorem.  *)

(* Membership witness for the two-point boolean enumeration: the head *)
(* branch covers [true], the head-of-tail branch covers [false]. *)
Lemma tspbr_bool_two_enum_in_witness : forall s : bool,
  sumd_in bool s (true :: false :: nil).
Proof.
  intro s.
  destruct s as [|].
  - exact (sumd_in_head bool true true (false :: nil) id_refl).
  - exact (sumd_in_tail bool false true (false :: nil)
             (sumd_in_head bool false false nil id_refl)).
Defined.

(* Pointwise zero discharge: nonnegative point values with a zero total *)
(* on the two-point enumeration force every point value to zero. *)
Theorem tspbr_sum_zero_nonneg_bool :
  forall f : bool -> Real,
    (forall s : bool, real_le zero (f s)) ->
    req (sumd_sumf bool (true :: false :: nil) f) zero ->
    forall s : bool, req (f s) zero.
Proof.
  intros f Hnn H0 s.
  exact (@uabT1_rte_fsum_zero_nonneg bool (true :: false :: nil)
           tspbr_bool_two_enum_in_witness f Hnn H0 s).
Defined.

(* ---- Assumption audit: each named statement reads Closed. ---- *)
Print Assumptions tspbr_sum_ext.
Print Assumptions tspbr_sum_linear.
Print Assumptions tspbr_sum_add.
Print Assumptions tspbr_sum_le.
Print Assumptions tspbr_real_sum_ext.
Print Assumptions tspbr_real_sum_le.
Print Assumptions tspbr_real_sum_linear.
Print Assumptions tspbr_real_sum_add.
Print Assumptions tspbr_bool_two_enum_in_witness.
Print Assumptions tspbr_sum_zero_nonneg_bool.
