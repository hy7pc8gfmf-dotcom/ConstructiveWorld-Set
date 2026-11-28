(* ========================================================================== *)
(* Module   : UpReqConcB2Time                                                *)
(* Mission. The unconditional B2 mixing-time assembly over a substantial      *)
(*   two-dimensional signed logit kernel: the exponential dual pair, the      *)
(*   kernel world (unit states, q = (+1,-1), k = (-1,+1), temperature one,    *)
(*   cap Delta = temp * max|dot| + 1 with the eps = 1/2 strict certificates   *)
(*   of UpReqConcB2), the one-element plain abs-sum slot, the total-variation *)
(*   machine with its mass-premise discharge, and the terminal pair: for      *)
(*   mass-normalized mu nu and every positive budget there is an iterate k    *)
(*   with TV(T^k mu, T^k nu) below budget (strict and weak forms).            *)
(* Dependencies. Stdlib List, QArith.QArith, QArith.Qabs, Lia; this           *)
(*   development S01..S15, UpReqAlgebra, UpReqSumD, UpReqConcSoftmax,         *)
(*   UpReqSampling, UpReqConcMixSel, UpReqConcB1, UpReqConcB2, AttnDoeblin.   *)
(* References. ConstructiveWorld-Main UpReqConcB2Time.v (statement lineage);  *)
(*   landed sibling UpReqConcB1.v (assembly discipline); NsepBudgetVerify.v   *)
(*   (audit-tail template).                                                   *)
(* Constructivity. Every statement face is Set-carried: order and equality    *)
(*   faces are the decidable Q reflections real_lt/real_le/real_eq (QltT /    *)
(*   QeqT boolean Id forms), terminal conclusions are sigT over nat with      *)
(*   Set families, so both heads extract. Zero Prop statements: the two       *)
(*   certificate positions inherited from the landed upstream interfaces      *)
(*   (the [enum_nonempty] slots of rsq_bs_kernel / k_titer /                  *)
(*   cmk_attention_mixing_time, and the [In] completeness premises of         *)
(*   cb2_z_lb_all / cb2_z_ub_all) are fed anonymous stdlib-mirror-form terms  *)
(*   written inline in definition and proof bodies and never eliminated       *)
(*   into Set; the numeric smoke pins are QeqT/QltT closed by computation.    *)
(*   All proofs end with the transparent closer; no opaque closer anywhere.   *)
(* Build. rocq c -native-compiler no -q -Q <tree root> "" UpReqConcB2Time.v   *)
(*   (single shot, this directory as workdir).                                *)
(* ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
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
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import UpReqConcB2.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* Section 1. The exponential dual pair: the Cauchy exponential with its       *)
(*   strict monotonicity face and the constructive-Or weak face (the left      *)
(*   branch goes through the strict lemma, the right branch through the        *)
(*   pointwise equality transport of the exponential).                         *)
(* ============================================================ *)

Definition cbt_expf : Real -> Real := cauchy_real_exp.

Lemma cbt_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (cbt_expf a) (cbt_expf b).
Proof. intros a b H. exact (cauchy_real_exp_mono a b H). Defined.

Lemma cbt_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (cbt_expf a) (cbt_expf b).
Proof.
  intros a b H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (inl (cauchy_real_exp_mono a b Hlt)).
  - exact (inr (cauchy_real_exp_wd a b Heq)).
Defined.

(* ============================================================ *)
(* Section 2. The B2 kernel world: the one-element state space with the        *)
(*   substantial two-dimensional signed logit vectors, the cap list, the      *)
(*   temperature, and the concrete kernel value/cap with their certificates.   *)
(* ============================================================ *)

Definition cbt_q : unit -> list Real :=
  fun _ : unit => real_one :: real_opp real_one :: nil.
Definition cbt_k : unit -> list Real :=
  fun _ : unit => real_opp real_one :: real_one :: nil.
Definition cbt_lmax : list (list Real * list Real) := (cbt_q tt, cbt_k tt) :: nil.

Definition cbt_temp : Real := one.

Lemma cbt_temp_pos : real_lt real_zero cbt_temp.
Proof. unfold cbt_temp. exact one_pos. Defined.

Definition cbt_z (s s' : unit) : Real := cb2_z unit cbt_q cbt_k cbt_temp s s'.
Definition cbt_Delta_core : Real := cb2_Delta_core cbt_temp cbt_lmax.
Definition cbt_Delta : Real := cb2_Delta cbt_temp cbt_lmax.

(* Positivity of the assembled cap: the strict branch carries the slack by
   eps = 1/2 (the [cb2_Delta_pos] certificate). *)
Lemma cbt_Delta_pos : real_lt real_zero cbt_Delta.
Proof. exact (cb2_Delta_pos cbt_temp cbt_temp_pos cbt_lmax). Defined.

(* The kernel value is bracketed by the negated cap and the cap: the
   completeness premise of the landed [cb2_z_lb_all]/[cb2_z_ub_all] is an
   [In] face, discharged inline by computing the one-pair cap list. *)
Lemma cbt_z_lb : forall s s' : unit, real_le (real_opp cbt_Delta) (cbt_z s s').
Proof.
  intros s s'.
  apply (cb2_z_lb_all unit cbt_q cbt_k cbt_temp cbt_temp_pos cbt_lmax).
  intros s0 s'0. unfold cbt_lmax. simpl. left. reflexivity.
Defined.

Lemma cbt_z_ub : forall s s' : unit, real_le (cbt_z s s') cbt_Delta.
Proof.
  intros s s'.
  apply (cb2_z_ub_all unit cbt_q cbt_k cbt_temp cbt_temp_pos cbt_lmax).
  intros s0 s'0. unfold cbt_lmax. simpl. left. reflexivity.
Defined.

(* ---- The softmax kernel instantiation (the landed 10+2-slot form) ---- *)

Definition cbt_sumf (f : unit -> Real) : Real := @csm_sumf unit [tt] f.

Lemma cbt_sum_eq_list : forall g : unit -> Real,
  real_eq (cbt_sumf g) (rsq_bs_list_sum unit g [tt]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum unit g [tt])). Defined.

(* The enum_nonempty slot of the landed kernel interface is an
   [Not]-face certificate; it is written here inline, term form, and
   consumed positionally only. *)
Definition cbt_kernel : unit -> unit -> Real :=
  @rsq_bs_kernel unit cbt_sumf [tt]
    (fun H : [tt] = (@nil unit) =>
       match H in (_ = l) return (match l with tt :: nil => True | _ => Empty_set end) with
       | eq_refl => I
       end)
    cbt_temp cbt_temp_pos cbt_Delta cbt_z cbt_z_lb cbt_sum_eq_list.

(* ============================================================ *)
(* Section 3. The sum interface slots: the plain one-element abs-sum bound,    *)
(*   the eps-shaped side form, and the total-variation discharge.              *)
(* ============================================================ *)

Lemma cbt_abs_sum_le : forall f : unit -> Real,
  real_le (abs (cbt_sumf f)) (cbt_sumf (fun s : unit => abs (f s))).
Proof.
  intro f.
  exact (le_id_r _ _ _
           (req_sym _ _ (plus_zero (abs (f tt))))
           (le_id_l _ _ _
              (req_abs_compat (plus (f tt) zero) (f tt) (plus_zero (f tt)))
              (le_refl (abs (f tt))))).
Defined.

Definition cbt_abs_sum_le_eps : forall (f : unit -> Real) (eps : Real),
  real_lt zero eps ->
  real_le (abs (cbt_sumf f)) (plus (cbt_sumf (fun s : unit => abs (f s))) eps) :=
  csm_abs_sum_le_eps unit [tt].

Definition cbt_inv_two : Real := inv_pos (plus one one) req_two_pos.

Definition cbt_tv (mu nu : unit -> Real) : Real :=
  mult cbt_inv_two (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))).

(* The mass premises force the one-element difference to vanish, so the
   nonnegativity of the total variation holds without any order dichotomy. *)
Lemma cbt_tv0 : forall mu nu : unit -> Real,
  real_eq (cbt_sumf mu) one -> real_eq (cbt_sumf nu) one ->
  real_le zero (cbt_tv mu nu).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hmu0 : real_eq (mu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (mu tt))) Hmu). }
  assert (Hnu0 : real_eq (nu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (nu tt))) Hnu). }
  assert (Hw0 : real_eq (req_minus (mu tt) (nu tt)) zero).
  { exact (req_trans _ _ _
             (req_plus_compat (mu tt) one (opp (nu tt)) (opp one)
                Hmu0 (req_opp_compat (nu tt) one Hnu0))
             (plus_opp one)). }
  assert (Habs : real_le zero (abs (req_minus (mu tt) (nu tt)))).
  { exact (le_id_r _ _ _
             (req_sym _ _ (req_abs_compat (req_minus (mu tt) (nu tt)) zero Hw0))
             (le_id_r zero zero (abs zero)
                (req_sym _ _ abs_zero) (le_refl zero))). }
  assert (Hprod : real_le zero (mult (abs (req_minus (mu tt) (nu tt))) cbt_inv_two)).
  { exact (le_id_l _ _ _
             (req_sym _ _
                (req_trans _ _ _ (mult_comm zero cbt_inv_two)
                   (mult_zero cbt_inv_two)))
             (le_mult_compat_weak zero (abs (req_minus (mu tt) (nu tt)))
                cbt_inv_two
                (lt_le_iff zero cbt_inv_two
                   (inl (inv_pos_pos (plus one one) req_two_pos)))
                Habs)). }
  assert (Hsw : real_le zero (mult cbt_inv_two (abs (req_minus (mu tt) (nu tt))))).
  { exact (le_id_r _ _ _ (mult_comm (abs (req_minus (mu tt) (nu tt))) cbt_inv_two)
             Hprod). }
  unfold cbt_tv.
  exact (le_id_r _ _ _
           (req_mult_compat cbt_inv_two cbt_inv_two
              (abs (req_minus (mu tt) (nu tt)))
              (plus (abs (req_minus (mu tt) (nu tt))) zero)
              (req_refl cbt_inv_two)
              (req_sym _ _ (plus_zero (abs (req_minus (mu tt) (nu tt))))))
           Hsw).
Defined.

(* The iterate wrapper over the landed iterator, fed the whole B2 data
   (the enum_nonempty slot again inline, positional only). *)
Definition cbt_titer (n : nat) (mu : unit -> Real) : unit -> Real :=
  k_titer unit cbt_sumf [tt]
    (fun H : [tt] = (@nil unit) =>
       match H in (_ = l) return (match l with tt :: nil => True | _ => Empty_set end) with
       | eq_refl => I
       end)
    cbt_temp cbt_temp_pos cbt_Delta cbt_z cbt_z_lb cbt_sum_eq_list n mu.

(* ============================================================ *)
(* Section 4. The terminal assembly: every slot of the landed closing          *)
(*   theorem filled explicitly, leaving only the two mass premises, the       *)
(*   budget premise, the growth certificate and the nonnegativity premise.    *)
(* ============================================================ *)

Definition cbt_mixing_cert :=
  @cmk_attention_mixing_time
    real_lt_plus_compat_lt_le
    unit cbt_sumf
    (csm_sum_ext unit [tt])
    (csm_sum_linear unit [tt])
    (csm_sum_add unit [tt])
    (csm_sum_le unit [tt])
    cbt_abs_sum_le
    [tt]
    (fun H : [tt] = (@nil unit) =>
       match H in (_ = l) return (match l with tt :: nil => True | _ => Empty_set end) with
       | eq_refl => I
       end)
    cbt_temp cbt_temp_pos
    cbt_Delta cbt_Delta_pos
    cbt_z cbt_z_lb cbt_z_ub
    (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
    cb1_bs_abs
    real_lt_plus_compat_lt_le
    cbt_sum_eq_list.

Theorem cbt_unconditional_mixing_time :
  forall mu nu : unit -> Real,
  real_eq (cbt_sumf mu) one -> real_eq (cbt_sumf nu) one ->
  forall budget : Real, real_lt zero budget ->
  sigT (fun k : nat =>
    real_lt (cbt_tv (cbt_titer k mu) (cbt_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (cbt_mixing_cert mu nu Hmu Hnu budget Hbudget
           cb1_arch (cbt_tv0 mu nu Hmu Hnu)).
Defined.

Theorem cbt_unconditional_mixing_time_le :
  forall mu nu : unit -> Real,
  real_eq (cbt_sumf mu) one -> real_eq (cbt_sumf nu) one ->
  forall budget : Real, real_lt zero budget ->
  sigT (fun k : nat =>
    real_le (cbt_tv (cbt_titer k mu) (cbt_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (@cmk_attention_mixing_time_le
           real_lt_plus_compat_lt_le
           unit cbt_sumf
           (csm_sum_ext unit [tt])
           (csm_sum_linear unit [tt])
           (csm_sum_add unit [tt])
           (csm_sum_le unit [tt])
           cbt_abs_sum_le
           [tt]
           (fun H : [tt] = (@nil unit) =>
              match H in (_ = l) return
                (match l with tt :: nil => True | _ => Empty_set end) with
              | eq_refl => I
              end)
           cbt_temp cbt_temp_pos
           cbt_Delta cbt_Delta_pos
           cbt_z cbt_z_lb cbt_z_ub
           (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
           cb1_bs_abs
           real_lt_plus_compat_lt_le
           cbt_sum_eq_list
           mu nu Hmu Hnu budget Hbudget
           cb1_arch (cbt_tv0 mu nu Hmu Hnu)).
Defined.

(* ============================================================ *)
(* Section 5. Computed smoke pins on the signed kernel: dot(q,k)(5) = -2      *)
(*   (nondegenerate), cap core 2, assembled cap 3 (the visible unit slack),   *)
(*   and the strict gap 5 > 1/2 behind the eps = 1/2 certificates.  All       *)
(*   four are decidable Q-carrier faces (QeqT / QltT), closed by              *)
(*   computation alone.                                                       *)
(* ============================================================ *)

Lemma cbt_smoke_z : QeqT (projT1 (cbt_z tt tt) 5%nat) (-2)%Q.
Proof. reflexivity. Defined.

Lemma cbt_smoke_Delta_core : QeqT (projT1 cbt_Delta_core 5%nat) 2%Q.
Proof. reflexivity. Defined.

Lemma cbt_smoke_Delta : QeqT (projT1 cbt_Delta 5%nat) 3%Q.
Proof. reflexivity. Defined.

Lemma cbt_smoke_gap : QltT (1#2)%Q
  (projT1 cbt_Delta 5%nat - projT1 (cbt_z tt tt) 5%nat).
Proof. reflexivity. Defined.

(* ============================================================ *)
(* Assumption audit: every named result of this piece, one line each.          *)
(* ============================================================ *)

Print Assumptions cbt_expf_mono_lt.
Print Assumptions cbt_expf_mono_le.
Print Assumptions cbt_temp_pos.
Print Assumptions cbt_Delta_pos.
Print Assumptions cbt_z_lb.
Print Assumptions cbt_z_ub.
Print Assumptions cbt_kernel.
Print Assumptions cbt_sum_eq_list.
Print Assumptions cbt_abs_sum_le.
Print Assumptions cbt_abs_sum_le_eps.
Print Assumptions cbt_tv0.
Print Assumptions cbt_titer.
Print Assumptions cbt_mixing_cert.
Print Assumptions cbt_unconditional_mixing_time.
Print Assumptions cbt_unconditional_mixing_time_le.
Print Assumptions cbt_smoke_z.
Print Assumptions cbt_smoke_Delta_core.
Print Assumptions cbt_smoke_Delta.
Print Assumptions cbt_smoke_gap.
