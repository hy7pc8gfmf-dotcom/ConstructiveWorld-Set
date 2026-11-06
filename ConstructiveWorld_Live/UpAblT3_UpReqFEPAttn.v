(* ConstructiveWorld-Set -- upstream FEP attention sum-interface ablations. *)

(** * UpAblT3_UpReqFEPAttn: unconditional list-sum instances of the
    sumf interface requirements.

    Mission.  Formalizes the sum-interface requirements of the use-face
      file UpReqFEPAttn.v (sections ReqFEPAttn, ReqRowView, ReqFEPLogZ)
      as unconditional statements about the concrete finite list sum
      [sumd_sumf] over an enumeration [enum]: extensionality, additivity,
      linearity, monotonicity, positivity, and zero elimination, named
      [uabT3_reqfepattn_sum_ext] through [uabT3_reqfeplogz_sum_pos].

    Dependencies.  Stdlib [List] (with [ListNotations]).  Requires the
      base chain [S01_BaseRing] through [S15_TailFEPUp] and [UpReqSumD]
      (importing [RealInterfaceEnhancedMod]) of this development.

    References.  This development, UpAblT3_UpReqFEPAttn.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].  The tree's unparameterized interface makes the
      baseline binder pair [(R : Set)] [RIS] vacuous; it is removed and
      the relation names rebound by notation, no statement name altered.

    Build.  [coqc -native-compiler no -q -Q <world> "" -Q . "" UpAblT3_UpReqFEPAttn.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
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

(* Set-carrier completion bridge: the interface class in this tree is *)
(*   unparameterized; its carrier is the global Cauchy real Real.     *)
Notation R := Real.
(* The relation statements are written over the concrete layer relation *)
(*   names ([real_eq]/[real_lt]/[real_le]), the extraction discipline of *)
(*   the temperature entropy layer (bare class fields are projections *)
(*   whose casts surface on the extraction face). *)
Notation req := real_eq.
Notation lt := real_lt.
Notation le := real_le.

(* ============ Section A, ReqFEPAttn: the summation requirements of the
   use-face sections, restated for the concrete list sum; the carrier [R]
   becomes explicit, the setoid instance stays implicit, and the abstract
   summation operator is instantiated at [sumd_sumf S enum]. ============ *)

(* A1, extensionality: families agreeing pointwise have equal finite
   sums; discharged by [sumd_sum_ext]. *)
Theorem uabT3_reqfepattn_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* A2, additivity: the finite sum of a pointwise sum splits into the sum
   of the finite sums; discharged by [sumd_sum_add]. *)
Theorem uabT3_reqfepattn_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* A3, linearity: scaling commutes with the finite sum; discharged by
   [sumd_sum_linear]. *)
Theorem uabT3_reqfepattn_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* A4, monotonicity: pointwise order lifts to the finite sum; discharged
   by [sumd_sum_le]. *)
Theorem uabT3_reqfepattn_sum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* A5, zero elimination: a pointwise nonnegative family whose finite sum
   is zero vanishes at every listed element, the enumeration being
   required to list all of [S]; discharged by
   [sumd_sum_zero_nonneg_surj] in the same shape. *)
Theorem uabT3_reqfepattn_sum_zero_nonneg :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, le zero (f s)) -> req (sumd_sumf S enum f) zero ->
      forall s : S, req (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* A6, positivity: a pointwise positive family has positive finite sum,
   the enumeration being required to be nonempty; discharged by
   [sumd_sum_pos] in the same shape. *)
Theorem uabT3_reqfepattn_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ Section B, ReqRowView: the row-view requirements,
   discharged on the same list-sum instance. ============ *)

(* B1, extensionality: families agreeing pointwise have equal finite
   sums; discharged by [sumd_sum_ext]. *)
Theorem uabT3_reqrowview_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* B2, positivity: nonempty listing as in A6; discharged by
   [sumd_sum_pos]. *)
Theorem uabT3_reqrowview_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ Section C, ReqFEPLogZ: the log-partition requirements,
   discharged on the same list-sum instance. ============ *)

(* C1, extensionality: families agreeing pointwise have equal finite
   sums; discharged by [sumd_sum_ext]. *)
Theorem uabT3_reqfeplogz_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* C2, additivity: the finite sum of a pointwise sum splits into the sum
   of the finite sums; discharged by [sumd_sum_add]. *)
Theorem uabT3_reqfeplogz_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* C3, linearity: scaling commutes with the finite sum; discharged by
   [sumd_sum_linear]. *)
Theorem uabT3_reqfeplogz_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* C4, positivity: nonempty listing as in A6; discharged by
   [sumd_sum_pos]. *)
Theorem uabT3_reqfeplogz_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ Closing audit: each global exit statement must report
   Closed under the global context. ============ *)
Print Assumptions uabT3_reqfepattn_sum_ext.
Print Assumptions uabT3_reqfepattn_sum_add.
Print Assumptions uabT3_reqfepattn_sum_linear.
Print Assumptions uabT3_reqfepattn_sum_le.
Print Assumptions uabT3_reqfepattn_sum_zero_nonneg.
Print Assumptions uabT3_reqfepattn_sum_pos.
Print Assumptions uabT3_reqrowview_sum_ext.
Print Assumptions uabT3_reqrowview_sum_pos.
Print Assumptions uabT3_reqfeplogz_sum_ext.
Print Assumptions uabT3_reqfeplogz_sum_add.
Print Assumptions uabT3_reqfeplogz_sum_linear.
Print Assumptions uabT3_reqfeplogz_sum_pos.
