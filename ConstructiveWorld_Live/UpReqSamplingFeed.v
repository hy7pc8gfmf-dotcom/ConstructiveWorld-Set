(* ========================================================================= *)
(* Module   : UpReqSamplingFeed                                              *)
(* Mission. Supply, at the concrete enumerated fold [csm_sumf] (the Cauchy-  *)
(*          real list sum over an explicit carrier enumeration), the honest  *)
(*          finite-sum interface slots of the two upstream sampling sections *)
(*          (extensionality, unit scaling, additivity, order reflection,     *)
(*          double-list exchange, the absolute-value identity, the strict    *)
(*          mixed-order addition law, the epsilon-adjacent triangle form     *)
(*          |sum f| <= sum |f| + eps, strict positivity over a nonempty      *)
(*          enumeration) plus the two-point instance data certificates.      *)
(* Dependencies. S01_BaseRing..S15_TailFEPUp, UpReqAlgebra, UpReqSumD,       *)
(*          UpReqConcSoftmax (csm_sumf, csm_abs_sum_le_eps),                 *)
(*          UpReqSampling (rsq_bs_opp_lt, rsq_bs_list_sum), ConcMixSelFeed   *)
(*          (cms_ sum/mix supply family); Stdlib List.                       *)
(* References. The finite-sum interface slots (sum_ext/linear/add/le/pos,    *)
(*          sum_eq_list, double-list exchange) of the contraction and        *)
(*          bounded-softmax sampling sections; the epsilon-adjacent triangle *)
(*          reading |sum f| <= sum |f| + eps (the plain pointwise triangle   *)
(*          has no constructive route for mixed signs and is not claimed).   *)
(* Constructivity. Statement faces carry zero Prop: lt/req/le are the        *)
(*          Set-valued order/equality of the Cauchy Q-sequence carrier       *)
(*          (S02_CauchyComplete real_lt/real_eq/real_le); nonemptiness rides *)
(*          the Set-level membership InT through sigT.  All proofs end in    *)
(*          Defined (no Qed: no purely-Prop bridge face occurs); the single  *)
(*          class-field consumption one_pos is pinned by an explicitly typed *)
(*          Definition usrq_one_pos; zero axioms/admits/classical logic.     *)
(* Build. rocq c -native-compiler no -q -Q <Set Live tree> ""                *)
(*          UpReqSamplingFeed.v (single shot, this directory as workdir).    *)
(* ========================================================================= *)
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ================= Section 1: fold interface supply, contraction slots === *)
(* Each slot restates the upstream interface obligation at the concrete     *)
(* fold [csm_sumf S en], delegating to the cms_ supply family; the fold     *)
(* prescription csm_sumf S en f is definitionally the sumd_sumf machine.    *)

Section UsumContractionSlots.

Variable S : Set.
Variable en : list S.

Theorem usrq_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (csm_sumf S en f) (csm_sumf S en g).
Proof.
  intros f g H.
  exact (cms_sum_ext S en f g H).
Defined.

Theorem usrq_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (csm_sumf S en (fun s : S => mult a (f s))) (mult a (csm_sumf S en f)).
Proof.
  intros a f.
  exact (cms_sum_linear S en a f).
Defined.

Theorem usrq_sum_add_supply : forall f g : S -> Real,
  req (csm_sumf S en (fun s : S => plus (f s) (g s)))
      (plus (csm_sumf S en f) (csm_sumf S en g)).
Proof.
  intros f g.
  exact (cms_sum_add S en f g).
Defined.

Theorem usrq_sum_le_supply : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (csm_sumf S en f) (csm_sumf S en g).
Proof.
  intros f g H.
  exact (cms_sum_le S en f g H).
Defined.

Theorem usrq_sum_swap_cc_supply : forall f : S -> S -> Real,
  req (csm_sumf S en (fun s : S => csm_sumf S en (fun s' : S => f s s')))
      (csm_sumf S en (fun s' : S => csm_sumf S en (fun s : S => f s s'))).
Proof.
  intros f.
  exact (cms_bs_swap S en f).
Defined.

(* The absolute-value identity |a| = a for 0 <= a: the strict branch is     *)
(* real_abs_pos_req; the equality branch routes through compatibility of    *)
(* abs with equality and |0| = 0.                                           *)
Theorem usrq_abs_ge_zero_req_supply : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

(* Strict mixed-order addition: a < b and c <= d give a + c < b + d.        *)
Theorem usrq_lt_plus_compat_lt_le_h_supply :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (cms_lt_plus_compat_lt_le_time a b c d Hab Hcd).
Defined.

End UsumContractionSlots.

(* ================= Section 2: fold interface supply, softmax slots ======= *)
(* The same five fold slots, the epsilon-adjacent triangle form, and the    *)
(* strict-positivity slot: nonemptiness is carried as a sigT InT witness    *)
(* (Set level), so the empty-enumeration branch closes by the empty         *)
(* membership family and the nonempty branch by the head-witness fold step. *)

Section UsumSoftmaxSlots.

Variable S : Set.
Variable en : list S.

Theorem usrq_bs_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (csm_sumf S en f) (csm_sumf S en g).
Proof.
  intros f g H.
  exact (cms_sum_ext S en f g H).
Defined.

Theorem usrq_bs_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (csm_sumf S en (fun s : S => mult a (f s))) (mult a (csm_sumf S en f)).
Proof.
  intros a f.
  exact (cms_sum_linear S en a f).
Defined.

Theorem usrq_bs_sum_add_supply : forall f g : S -> Real,
  req (csm_sumf S en (fun s : S => plus (f s) (g s)))
      (plus (csm_sumf S en f) (csm_sumf S en g)).
Proof.
  intros f g.
  exact (cms_sum_add S en f g).
Defined.

Theorem usrq_bs_sum_le_supply : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (csm_sumf S en f) (csm_sumf S en g).
Proof.
  intros f g H.
  exact (cms_sum_le S en f g H).
Defined.

Theorem usrq_bs_sum_pos_supply : forall (f : S -> Real),
  sigT (fun t : S => InT t en) ->
  (forall s : S, lt zero (f s)) -> lt zero (csm_sumf S en f).
Proof.
  intros f Hne H.
  destruct Hne as [x Hx].
  destruct en as [| y t].
  - exact (match Hx with end).
  - exact (sumd_list_sum_pos_cons S f y t H).
Defined.

Theorem usrq_bs_abs_sum_le_eps_supply : forall (f : S -> Real) (eps : Real),
  lt zero eps ->
  le (abs (csm_sumf S en f))
     (plus (csm_sumf S en (fun s : S => abs (f s))) eps).
Proof.
  intros f eps Heps.
  exact (csm_abs_sum_le_eps S en f eps Heps).
Defined.

Theorem usrq_bs_swap_supply : forall f : S -> S -> Real,
  req (csm_sumf S en (fun s : S => csm_sumf S en (fun s' : S => f s s')))
      (csm_sumf S en (fun s' : S => csm_sumf S en (fun s : S => f s s'))).
Proof.
  intros f.
  exact (cms_bs_swap S en f).
Defined.

(* Same absolute-value identity, rehearsed in place for this slot block.    *)
Theorem usrq_bs_abs_supply : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

Theorem usrq_bs_lpc_supply :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (cms_lt_plus_compat_lt_le_time a b c d Hab Hcd).
Defined.

(* The fold agrees with the plain list sum over the same enumeration.       *)
Theorem usrq_sum_eq_list_supply : forall g : S -> Real,
  req (csm_sumf S en g) (rsq_bs_list_sum S g en).
Proof.
  intro g.
  exact (cms_sum_eq_list S en g).
Defined.

End UsumSoftmaxSlots.

(* ================= Section 3: two-point world data certificates ========== *)
(* Temperature and step size take the unit one; the signature is the        *)
(* symmetric plus/minus-one map on bool, bounded in absolute value by the   *)
(* step size via rsq_bs_opp_lt; the enumeration is the two-element table,   *)
(* with nonemptiness given by the Set-level head-membership witness.        *)

Definition usrq_temp : Real := one.

(* Explicitly typed pin of the class field one_pos (interface honesty).     *)
Definition usrq_one_pos : lt zero one := one_pos.

Theorem usrq_temp_pos_supply : lt zero usrq_temp.
Proof.
  unfold usrq_temp.
  exact usrq_one_pos.
Defined.

Definition usrq_Delta : Real := one.

Theorem usrq_Delta_pos_supply : lt zero usrq_Delta.
Proof.
  unfold usrq_Delta.
  exact usrq_one_pos.
Defined.

Definition usrq_z (s s' : bool) : Real := if s then one else opp one.

Theorem usrq_z_lb_supply : forall s s' : bool, le (opp usrq_Delta) (usrq_z s s').
Proof.
  intros s s'. destruct s as [ | ].
  - exact (inl (rsq_bs_opp_lt usrq_Delta usrq_Delta_pos_supply)).
  - exact (real_le_refl (opp usrq_Delta)).
Defined.

Theorem usrq_z_ub_supply : forall s s' : bool, le (usrq_z s s') usrq_Delta.
Proof.
  intros s s'. destruct s as [ | ].
  - exact (real_le_refl usrq_Delta).
  - exact (inl (rsq_bs_opp_lt usrq_Delta usrq_Delta_pos_supply)).
Defined.

Definition usrq_enum : list bool := [true; false].

Theorem usrq_enum_nonempty_supply : sigT (fun t : bool => InT t usrq_enum).
Proof.
  exact (existT _ true (InT_here true (false :: nil))).
Defined.

(* ============ Assumption audit: one Print Assumptions per theorem ======== *)

Print Assumptions usrq_sum_ext_supply.
Print Assumptions usrq_sum_linear_supply.
Print Assumptions usrq_sum_add_supply.
Print Assumptions usrq_sum_le_supply.
Print Assumptions usrq_sum_swap_cc_supply.
Print Assumptions usrq_abs_ge_zero_req_supply.
Print Assumptions usrq_lt_plus_compat_lt_le_h_supply.
Print Assumptions usrq_bs_sum_ext_supply.
Print Assumptions usrq_bs_sum_linear_supply.
Print Assumptions usrq_bs_sum_add_supply.
Print Assumptions usrq_bs_sum_le_supply.
Print Assumptions usrq_bs_sum_pos_supply.
Print Assumptions usrq_bs_abs_sum_le_eps_supply.
Print Assumptions usrq_bs_swap_supply.
Print Assumptions usrq_bs_abs_supply.
Print Assumptions usrq_bs_lpc_supply.
Print Assumptions usrq_sum_eq_list_supply.
Print Assumptions usrq_temp_pos_supply.
Print Assumptions usrq_Delta_pos_supply.
Print Assumptions usrq_z_lb_supply.
Print Assumptions usrq_z_ub_supply.
Print Assumptions usrq_enum_nonempty_supply.
