(* ConstructiveWorld-Set -- the free-energy / KL gap over finite state lists. *)
(** * FreeEnergyKLGap: the free-energy gap identity and its inequality faces.

    Mission.  For a finite state space (a head state consed onto a list), a
    base loss, a temperature [D] and a partition function [Z], this file
    proves the free-energy principle core: (1) the gap identity
    [F(p) == F(pi_b) + D * sum_s kl_term(p, pi_b)] with [pi_b] the Boltzmann
    distribution ([fekl_gap_decomp_general]; list instances close it through
    [rkd_boltzmann_normalized]); (2) the lower-bound face [F(pi_b) <=_b F(p)]
    ([fekl_fep_gap_le_b]; canonical-Z instance [fekl_fep_gap_canonical_le_b]);
    (3) the eps face [F(pi_b) <= F(p) + eps] ([fekl_fep_gap_eps]); (4) the
    complexity comparison [sf_n2r(|v|) <=_b sf_vfe(v, v)] on the SF carrier.

    Dependencies.  Stdlib [QArith.Qring].  Requires [S01_BaseRing] through
    [S15_TailFEPUp], [RealKLDecomp], [UpRealLeB], [UpRealLeB2], [UpRealLeB3]
    of this development.

    References.  This development, FreeEnergyKLGap.v, the baseline module in
    ConstructiveWorld-Main whose statement names are carried over here
    verbatim (statement-face Set-carrier completion).

    Constructivity.  Every named statement is carried by [Set]
    ([real_eq]/[real_lt]/[real_le]/[real_le_b] are Set-valued here; the
    order faces are QltT-witnessed sigT forms of S02_CauchyComplete); no
    statement is Prop-faced, hence no Qed: all proofs end [Defined] and the
    proof terms stay transparent and extractable.  Zero axioms, zero
    classical logic, zero unproven statements.

    Build.  [coqc -native-compiler no -q -Q . "" FreeEnergyKLGap.v]; the tail
    audits every statement by [Print Assumptions]. *)
From Stdlib Require Import QArith.Qring.
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
Require Import RealKLDecomp.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ============================================================ *)
(* Part 0: conversion lemmas (difference form, the D * eps shift, *)
(* and order preservation under positive scaling).                *)
(* ============================================================ *)

(* 0.1 Difference-form conversion: fp == fb + dk entails fp + (-fb) == dk *)
(*   (a pure eq chain over assoc/comm/opp/zero; no order facts used). *)
Lemma fekl_diff_shift : forall (fb fp dk : Real),
  real_eq fp (real_plus fb dk) ->
  real_eq (real_plus fp (real_opp fb)) dk.
Proof.
  intros fb fp dk H.
  apply (real_eq_trans
           (real_plus fp (real_opp fb))
           (real_plus (real_plus fb dk) (real_opp fb))
           dk).
  - apply (RealSetoid.real_eq_plus_compat fp (real_opp fb)
             (real_plus fb dk) (real_opp fb)
             H (real_eq_refl (real_opp fb))).
  - (* (fb + dk) + (-fb) == dk: a middle-segment reordering chain. *)
    apply (real_eq_trans
             (real_plus (real_plus fb dk) (real_opp fb))
             (real_plus dk real_zero)
             dk).
    + apply (real_eq_trans
               (real_plus (real_plus fb dk) (real_opp fb))
               (real_plus fb (real_plus dk (real_opp fb)))
               (real_plus dk real_zero)).
      * exact (real_eq_sym (real_plus fb (real_plus dk (real_opp fb)))
                 (real_plus (real_plus fb dk) (real_opp fb))
                 (real_plus_assoc fb dk (real_opp fb))).
      * (* fb + (dk + (-fb)) == dk + 0: a five-step assoc/comm chain. *)
        apply (real_eq_trans
                 (real_plus fb (real_plus dk (real_opp fb)))
                 (real_plus (real_plus fb dk) (real_opp fb))
                 (real_plus dk real_zero)).
        -- exact (real_plus_assoc fb dk (real_opp fb)).
        -- apply (real_eq_trans
                     (real_plus (real_plus fb dk) (real_opp fb))
                     (real_plus (real_plus dk fb) (real_opp fb))
                     (real_plus dk real_zero)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus fb dk) (real_opp fb)
                       (real_plus dk fb) (real_opp fb)
                       (real_plus_comm fb dk) (real_eq_refl (real_opp fb))).
           ++ apply (real_eq_trans
                        (real_plus (real_plus dk fb) (real_opp fb))
                        (real_plus dk (real_plus fb (real_opp fb)))
                        (real_plus dk real_zero)).
              ** exact (real_eq_sym
                          (real_plus dk (real_plus fb (real_opp fb)))
                          (real_plus (real_plus dk fb) (real_opp fb))
                          (real_plus_assoc dk fb (real_opp fb))).
              ** apply (RealSetoid.real_eq_plus_compat dk
                           (real_plus fb (real_opp fb)) dk real_zero
                           (real_eq_refl dk) (real_plus_opp fb)).
    + exact (real_plus_zero dk).
Defined.

(* 0.2 D * (eps * inv D) == eps (the positivity certificate HD discharges *)
(*   the inverse; assoc/comm/inv chain). *)
Lemma fekl_d_eps : forall (D eps : Real) (HD : real_lt real_zero D),
  real_eq (real_mult D (real_mult eps (real_inv_pos D HD))) eps.
Proof.
  intros D eps HD.
  apply (real_eq_trans
           (real_mult D (real_mult eps (real_inv_pos D HD)))
           (real_mult eps (real_mult D (real_inv_pos D HD)))
           eps).
  - (* leg A: D * (eps * inv) == eps * (D * inv), three reordering steps. *)
    apply (real_eq_trans
             (real_mult D (real_mult eps (real_inv_pos D HD)))
             (real_mult (real_mult D eps) (real_inv_pos D HD))
             (real_mult eps (real_mult D (real_inv_pos D HD)))).
    + exact (real_mult_assoc D eps (real_inv_pos D HD)).
    + apply (real_eq_trans
               (real_mult (real_mult D eps) (real_inv_pos D HD))
               (real_mult (real_mult eps D) (real_inv_pos D HD))
               (real_mult eps (real_mult D (real_inv_pos D HD)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult D eps)
                  (real_inv_pos D HD) (real_mult eps D) (real_inv_pos D HD)
                  (real_mult_comm D eps) (real_eq_refl (real_inv_pos D HD))).
      * exact (real_eq_sym (real_mult eps (real_mult D (real_inv_pos D HD)))
                 (real_mult (real_mult eps D) (real_inv_pos D HD))
                 (real_mult_assoc eps D (real_inv_pos D HD))).
  - (* leg B: eps * (D * inv) == eps * 1 == eps. *)
    apply (real_eq_trans
             (real_mult eps (real_mult D (real_inv_pos D HD)))
             (real_mult eps real_one)
             eps).
    + apply (RealSetoid.real_eq_mult_compat eps (real_mult D (real_inv_pos D HD))
               eps real_one (real_eq_refl eps) (real_inv_pos_correct D HD)).
    + exact (real_mult_one eps).
Defined.

(* 0.3 D * (K + eps * inv D) == D*K + eps (distributivity + 0.2; the *)
(*   shift-conversion core). *)
Lemma fekl_d_move_eps : forall (D K eps : Real) (HD : real_lt real_zero D),
  real_eq (real_mult D (real_plus K (real_mult eps (real_inv_pos D HD))))
          (real_plus (real_mult D K) eps).
Proof.
  intros D K eps HD.
  apply (real_eq_trans
           (real_mult D (real_plus K (real_mult eps (real_inv_pos D HD))))
           (real_plus (real_mult D K) (real_mult D (real_mult eps (real_inv_pos D HD))))
           (real_plus (real_mult D K) eps)).
  - exact (real_distrib D K (real_mult eps (real_inv_pos D HD))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult D K)
             (real_mult D (real_mult eps (real_inv_pos D HD)))
             (real_mult D K) eps
             (real_eq_refl (real_mult D K)) (fekl_d_eps D eps HD)).
Defined.

(* 0.4 Order preservation under positive scaling (Or form): D > 0 and *)
(*   0 <= x entail 0 <= D*x.  The Or premise is eliminated branch by *)
(*   branch (constructive sum elimination; no excluded-middle step). *)
Lemma fekl_mult_pos_le : forall (D x : Real),
  real_lt real_zero D -> real_le real_zero x ->
  real_le real_zero (real_mult D x).
Proof.
  intros D x HD Hx. destruct Hx as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req real_zero (real_mult D x)). left.
    exact (real_mult_positive D x HD Hlt).
  - apply (RealSetoid.real_lt_le_iff_req real_zero (real_mult D x)). right.
    apply (real_eq_trans real_zero (real_mult D real_zero) (real_mult D x)).
    + exact (real_eq_sym (real_mult D real_zero) real_zero (real_mult_zero D)).
    + apply (RealSetoid.real_eq_mult_compat D real_zero D x
               (real_eq_refl D) Heq).
Defined.

(* 0.5 Order preservation under positive scaling (lower-bound form): *)
(*   D > 0 and 0 <=_b K entail 0 <=_b D*K, via leb3_le_b_pos_scale_l plus *)
(*   left-endpoint transport of the zero form. *)
Lemma fekl_mult_pos_le_b : forall (D K : Real),
  real_lt real_zero D -> real_le_b real_zero K ->
  real_le_b real_zero (real_mult D K).
Proof.
  intros D K HD HK.
  apply (leb3_le_b_eq_l (real_mult D real_zero) real_zero (real_mult D K)
           (real_mult_zero D)).
  exact (leb3_le_b_pos_scale_l real_zero K D HK HD).
Defined.

(* ============================================================ *)
(* Part 1: the general sumf gap identity (real_eq form, fully      *)
(*   explicit interface).  F(p) - F(pi_b) == D * sum_s kl_term     *)
(*   (direct link to the KL decomposition piece + 0.1).            *)
(* ============================================================ *)
Theorem fekl_gap_decomp_general :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one),
  real_eq
    (real_plus
       (real_free_energy S sumf real_base_loss D p Hp)
       (real_opp
          (real_free_energy S sumf real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos))))
    (real_mult D
       (sumf (fun s : S =>
          real_kl_term (p s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
            (Hp s)
            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos
         p Hp Hnormp Hnormb.
  apply fekl_diff_shift.
  exact (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear
           real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb).
Defined.

(* ============================================================ *)
(* Part 2: the list-carrier (s0 :: l) summation instance.          *)
(*   sumf := fekl_sumf (the cons-carrier closure of real_list_sum); *)
(*   the ext/add/linear interface trio is discharged by direct     *)
(*   instantiation of the real_list_sum compatibility lemmas.      *)
(* ============================================================ *)
Definition fekl_sumf (X : Type) (s0 : X) (l : list X) (f : X -> Real) : Real :=
  real_list_sum X f (s0 :: l).

Lemma fekl_sumf_ext : forall (X : Type) (s0 : X) (l : list X)
  (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (fekl_sumf X s0 l f) (fekl_sumf X s0 l g).
Proof.
  intros X s0 l f g Hfg.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (RealSetoid.real_eq_plus_compat (f s0) real_zero (g s0) real_zero
             (Hfg s0) (real_eq_refl real_zero)).
  - exact (RealSetoid.real_eq_plus_compat (f s0)
             (real_plus (f w) (real_list_sum X f rest))
             (g s0)
             (real_plus (g w) (real_list_sum X g rest))
             (Hfg s0) (IH w)).
Defined.

Lemma fekl_sumf_add : forall (X : Type) (s0 : X) (l : list X)
  (f g : X -> Real),
  real_eq (fekl_sumf X s0 l (fun s : X => real_plus (f s) (g s)))
          (real_plus (fekl_sumf X s0 l f) (fekl_sumf X s0 l g)).
Proof.
  intros X s0 l f g.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (real_eq_trans
             (real_plus (real_plus (f s0) (g s0)) real_zero)
             (real_plus (f s0) (g s0))
             (real_plus (real_plus (f s0) real_zero)
                        (real_plus (g s0) real_zero))
             (real_plus_zero (real_plus (f s0) (g s0)))
             (RealSetoid.real_eq_plus_compat (f s0) (g s0)
                (real_plus (f s0) real_zero) (real_plus (g s0) real_zero)
                (real_eq_sym (real_plus (f s0) real_zero) (f s0)
                   (real_plus_zero (f s0)))
                (real_eq_sym (real_plus (g s0) real_zero) (g s0)
                   (real_plus_zero (g s0))))).
  - exact (real_eq_trans
             (real_plus (real_plus (f s0) (g s0))
                        (real_plus (real_plus (f w) (g w))
                                   (real_list_sum X
                                      (fun s : X => real_plus (f s) (g s))
                                      rest)))
             (real_plus (real_plus (f s0) (g s0))
                        (real_plus (real_plus (f w) (real_list_sum X f rest))
                                   (real_plus (g w) (real_list_sum X g rest))))
             (real_plus
                (real_plus (f s0) (real_plus (f w) (real_list_sum X f rest)))
                (real_plus (g s0) (real_plus (g w) (real_list_sum X g rest))))
             (RealSetoid.real_eq_plus_compat
                (real_plus (f s0) (g s0))
                (real_plus (real_plus (f w) (g w))
                           (real_list_sum X
                              (fun s : X => real_plus (f s) (g s)) rest))
                (real_plus (f s0) (g s0))
                (real_plus (real_plus (f w) (real_list_sum X f rest))
                           (real_plus (g w) (real_list_sum X g rest)))
                (real_eq_refl (real_plus (f s0) (g s0)))
                (IH w))
             (real_plus_swap_mid (f s0) (g s0)
                (real_plus (f w) (real_list_sum X f rest))
                (real_plus (g w) (real_list_sum X g rest)))).
Defined.

Lemma fekl_sumf_linear : forall (X : Type) (s0 : X) (l : list X)
  (a : Real) (f : X -> Real),
  real_eq (fekl_sumf X s0 l (fun s : X => real_mult a (f s)))
          (real_mult a (fekl_sumf X s0 l f)).
Proof.
  intros X s0 l a f.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (real_eq_trans
             (real_plus (real_mult a (f s0)) real_zero)
             (real_mult a (f s0))
             (real_mult a (real_plus (f s0) real_zero))
             (real_plus_zero (real_mult a (f s0)))
             (real_eq_sym (real_mult a (real_plus (f s0) real_zero))
                (real_mult a (f s0))
                (real_eq_trans
                   (real_mult a (real_plus (f s0) real_zero))
                   (real_plus (real_mult a (f s0)) (real_mult a real_zero))
                   (real_mult a (f s0))
                   (real_distrib a (f s0) real_zero)
                   (real_eq_trans
                      (real_plus (real_mult a (f s0)) (real_mult a real_zero))
                      (real_plus (real_mult a (f s0)) real_zero)
                      (real_mult a (f s0))
                      (RealSetoid.real_eq_plus_compat (real_mult a (f s0))
                         (real_mult a real_zero) (real_mult a (f s0))
                         real_zero
                         (real_eq_refl (real_mult a (f s0)))
                         (real_mult_zero a))
                      (real_plus_zero (real_mult a (f s0))))))).
  - exact (real_eq_sym
             (real_mult a
                (real_plus (f s0) (real_plus (f w) (real_list_sum X f rest))))
             (real_plus (real_mult a (f s0))
                        (real_plus (real_mult a (f w))
                                   (real_list_sum X
                                      (fun s : X => real_mult a (f s)) rest)))
             (real_eq_trans
                (real_mult a
                   (real_plus (f s0)
                      (real_plus (f w) (real_list_sum X f rest))))
                (real_plus (real_mult a (f s0))
                           (real_mult a
                              (real_plus (f w) (real_list_sum X f rest))))
                (real_plus (real_mult a (f s0))
                           (real_plus (real_mult a (f w))
                                      (real_list_sum X
                                         (fun s : X => real_mult a (f s))
                                         rest)))
                (real_distrib a (f s0)
                   (real_plus (f w) (real_list_sum X f rest)))
                (RealSetoid.real_eq_plus_compat (real_mult a (f s0))
                   (real_mult a (real_plus (f w) (real_list_sum X f rest)))
                   (real_mult a (f s0))
                   (real_list_sum X (fun s : X => real_mult a (f s))
                      (w :: rest))
                   (real_eq_refl (real_mult a (f s0)))
                   (real_eq_sym
                      (real_list_sum X (fun s : X => real_mult a (f s))
                         (w :: rest))
                      (real_mult a (real_plus (f w) (real_list_sum X f rest)))
                      (IH w))))).
Defined.

(* Partition function: Z := sum over s0::l of exp(-e(s)/D) *)
(*   (positivity: a pointwise positive exponential plus a nonempty cons). *)
Definition fekl_part (X : Type) (s0 : X) (l : list X)
           (real_base_loss : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D) : Real :=
  real_list_sum X
    (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
    (s0 :: l).

Lemma fekl_part_pos : forall (X : Type) (s0 : X) (l : list X)
  (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_lt real_zero (fekl_part X s0 l real_base_loss D D_pos).
Proof.
  intros X s0 l real_base_loss D D_pos. unfold fekl_part.
  apply (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
           (s0 :: l)).
  - intro s.
    exact (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s))).
  - discriminate.
Defined.

(* ============================================================ *)
(* Part 3: the FEP core, lower-bound face.                        *)
(*   F(pi_b) <=_b F(p) with premises the two normalization        *)
(*   hypotheses.  Assembly: 0 <=_b D*K (Gibbs lower-bound face +  *)
(*   positive scaling), and F(p) == F(pi_b) + D*K transported on  *)
(*   the right endpoint.                                          *)
(* ============================================================ *)
Theorem fekl_fep_gap_le_b :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                   (s0 :: l)) real_one),
  real_le_b
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos))
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
Proof.
  intros X s0 l real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb.
  set (Fpi := real_free_energy X (fekl_sumf X s0 l) real_base_loss D
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos)).
  set (Fp := real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
  set (K := real_list_sum X (fun s : X =>
              real_kl_term (p s)
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s))
              (s0 :: l)).
  (* step 1: 0 <=_b K, a direct link to real_gibbs_inequality_B. *)
  assert (HK : real_le_b real_zero K).
  { exact (real_gibbs_inequality_B X (s0 :: l) p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
             Hp
             (fun s : X => real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s)
             Hnormp Hnormb). }
  (* step 2: 0 <=_b D*K by positive scaling (Part 0.5). *)
  assert (HDK : real_le_b real_zero (real_mult D K))
    by exact (fekl_mult_pos_le_b D K D_pos HK).
  (* step 3: F(p) == F(pi_b) + D*K, a direct link to the decomposition. *)
  assert (Hdec : real_eq Fp (real_plus Fpi (real_mult D K))).
  { exact (rkd_kl_decomp_full X (fekl_sumf X s0 l)
             (fekl_sumf_ext X s0 l) (fekl_sumf_add X s0 l)
             (fekl_sumf_linear X s0 l)
             real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb). }
  (* step 4: F(pi_b) + 0 <=_b F(pi_b) + D*K (additive compatibility). *)
  assert (Hstep : real_le_b (real_plus Fpi real_zero)
                            (real_plus Fpi (real_mult D K))).
  { exact (real_le_b_plus_compat Fpi Fpi real_zero (real_mult D K)
             (leb3_le_b_refl Fpi) HDK). }
  (* step 5: erase the +0 on the left, transport the right endpoint. *)
  exact (leb3_le_b_eq_r Fpi (real_plus Fpi (real_mult D K)) Fp
           (leb3_le_b_eq_l (real_plus Fpi real_zero) Fpi
              (real_plus Fpi (real_mult D K)) (real_plus_zero Fpi) Hstep)
           (real_eq_sym Fp (real_plus Fpi (real_mult D K)) Hdec)).
Defined.

(* ============================================================ *)
(* Part 4: the FEP core, canonical partition instance (premises   *)
(*   reduced to the single normalization of p, fully closed).     *)
(*   Z := sum exp(-e/D) (fekl_part, internal positivity); the     *)
(*   sum pi_b == 1 premise is discharged by rkd_boltzmann_normalized *)
(*   at the definitional partition identity.                      *)
(* ============================================================ *)
Theorem fekl_fep_gap_canonical_le_b :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one),
  real_le_b
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos
          (fekl_part X s0 l real_base_loss D D_pos)
          (fekl_part_pos X s0 l real_base_loss D D_pos))
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos
          (fekl_part X s0 l real_base_loss D D_pos)
          (fekl_part_pos X s0 l real_base_loss D D_pos)))
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
Proof.
  intros X s0 l real_base_loss D D_pos p Hp Hnormp.
  apply (fekl_fep_gap_le_b X s0 l real_base_loss D D_pos
           (fekl_part X s0 l real_base_loss D D_pos)
           (fekl_part_pos X s0 l real_base_loss D D_pos) p Hp Hnormp).
  exact (rkd_boltzmann_normalized X (fekl_sumf X s0 l)
           (fekl_sumf_ext X s0 l) (fekl_sumf_linear X s0 l)
           real_base_loss D D_pos
           (fekl_part X s0 l real_base_loss D D_pos)
           (fekl_part_pos X s0 l real_base_loss D D_pos)
           (real_eq_refl (fekl_sumf X s0 l
              (fun s : X =>
                 real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))).
Defined.

(* ============================================================ *)
(* Part 5: the FEP core, eps-witness face.  F(pi_b) <= F(p) + eps. *)
(*   Assembly: 0 <= K + eps*inv(D) (real_gibbs_inequality_eps) ->  *)
(*   positive-scaling order preservation (0.4) -> shift conversion *)
(*   0 <= D*K + eps (0.3) -> both Or branches construct            *)
(*   F(pi_b) <= F(pi_b) + (D*K + eps) -> right-end transport along *)
(*   the decomposition.                                            *)
(* ============================================================ *)
Theorem fekl_fep_gap_eps :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                   (s0 :: l)) real_one)
    (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos))
    (real_plus
       (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp) eps).
Proof.
  intros X s0 l real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb eps Heps.
  set (Fpi := real_free_energy X (fekl_sumf X s0 l) real_base_loss D
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos)).
  set (Fp := real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
  set (K := real_list_sum X (fun s : X =>
              real_kl_term (p s)
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s))
              (s0 :: l)).
  assert (Hdec : real_eq Fp (real_plus Fpi (real_mult D K))).
  { exact (rkd_kl_decomp_full X (fekl_sumf X s0 l)
             (fekl_sumf_ext X s0 l) (fekl_sumf_add X s0 l)
             (fekl_sumf_linear X s0 l)
             real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb). }
  (* step 1: 0 <= K + eps*inv(D), a direct link to real_gibbs_inequality_eps. *)
  assert (HKd : real_le real_zero
                  (real_plus K (real_mult eps (real_inv_pos D D_pos)))).
  { exact (real_gibbs_inequality_eps X (s0 :: l) p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
             Hp
             (fun s : X => real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s)
             Hnormp Hnormb
             (real_mult eps (real_inv_pos D D_pos))
             (real_mult_positive eps (real_inv_pos D D_pos) Heps
                (real_inv_pos_pos D D_pos))). }
  (* step 2: positive scaling, 0 <= D*(K + eps*inv(D)) (Part 0.4). *)
  assert (HDk : real_le real_zero
                  (real_mult D (real_plus K (real_mult eps (real_inv_pos D D_pos))))).
  { exact (fekl_mult_pos_le D (real_plus K (real_mult eps (real_inv_pos D D_pos)))
             D_pos HKd). }
  (* step 3: shift conversion, 0 <= D*K + eps (Part 0.3). *)
  assert (HDe : real_le real_zero (real_plus (real_mult D K) eps)).
  { exact (RealSetoid.real_le_id_r real_zero
             (real_mult D (real_plus K (real_mult eps (real_inv_pos D D_pos))))
             (real_plus (real_mult D K) eps)
             (fekl_d_move_eps D K eps D_pos) HDk). }
  (* step 4: both Or branches construct F(pi_b) <= F(pi_b) + (D*K + eps). *)
  assert (Hshift : real_le Fpi (real_plus Fpi (real_plus (real_mult D K) eps))).
  { destruct HDe as [Hlt | Heq0].
    - apply (RealSetoid.real_lt_le_iff_req Fpi
               (real_plus Fpi (real_plus (real_mult D K) eps))). left.
      apply (RealSetoid.real_lt_id_l Fpi (real_plus Fpi real_zero)
               (real_plus Fpi (real_plus (real_mult D K) eps))).
      + exact (real_eq_sym (real_plus Fpi real_zero) Fpi (real_plus_zero Fpi)).
      + exact (real_lt_plus_translate Fpi real_zero
                 (real_plus (real_mult D K) eps) Hlt).
    - apply RealSetoid.real_eq_le.
      apply (real_eq_trans Fpi (real_plus Fpi real_zero)
               (real_plus Fpi (real_plus (real_mult D K) eps))).
      + exact (real_eq_sym (real_plus Fpi real_zero) Fpi (real_plus_zero Fpi)).
      + apply (RealSetoid.real_eq_plus_compat Fpi real_zero Fpi
                 (real_plus (real_mult D K) eps)
                 (real_eq_refl Fpi) Heq0). }
  (* step 5: transport the right endpoint F(pi_b)+(D*K+eps) == F(p)+eps. *)
  apply (RealSetoid.real_le_id_r Fpi
           (real_plus Fpi (real_plus (real_mult D K) eps))
           (real_plus Fp eps)).
  - apply (real_eq_trans
             (real_plus Fpi (real_plus (real_mult D K) eps))
             (real_plus (real_plus Fpi (real_mult D K)) eps)
             (real_plus Fp eps)).
    + exact (real_plus_assoc Fpi (real_mult D K) eps).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus Fpi (real_mult D K)) eps Fp eps
               (real_eq_sym Fp (real_plus Fpi (real_mult D K)) Hdec)
               (real_eq_refl eps)).
  - exact Hshift.
Defined.

(* ============================================================ *)
(* Part 6: the SF-carrier comparison: sf_n2r(|v|) <=_b sf_vfe(v,v) *)
(*   (the Bishop-style correspondence matching-state free energy   *)
(*   >= complexity).  The lower-bound piece is discharged at the   *)
(*   half quantity dh := eps * inv(2), which is positive and < eps; *)
(*   both Or branches close.                                       *)
(* ============================================================ *)
Theorem fekl_sf_vfe_ge_complexity_B :
  forall v : SFVec, real_le_b (sf_n2r (length v)) (sf_vfe v v).
Proof.
  intro v. unfold real_le_b. intros eps Heps.
  set (c := sf_n2r (length v)).
  set (h := real_inv_pos (real_plus real_one real_one) real_two_pos_local).
  set (dh := real_mult eps h).
  (* half quantity dh := eps * inv(2): positive, and dh < eps. *)
  assert (Hhpos : real_lt real_zero h)
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdpos : real_lt real_zero dh)
    by exact (real_mult_positive eps h Heps Hhpos).
  assert (Hde : real_lt dh eps).
  { apply (RealSetoid.real_lt_id_r dh (real_mult eps real_one) eps).
    - exact (real_mult_one eps).
    - exact (real_mult_lt_compat_l h real_one eps real_inv_two_lt_one Heps). }
  (* discharge the lower-bound piece at the half quantity dh (both Or branches). *)
  destruct (sf_vfe_ge_complexity_eps v dh Hdpos) as [Hlt | Heq].
  - (* lt branch: c - dh < vfe entails c < vfe + dh < vfe + eps. *)
    assert (HeqL : real_eq c (real_plus dh (real_plus c (real_opp dh)))).
    { apply real_eq_sym.
      apply (real_eq_trans
               (real_plus dh (real_plus c (real_opp dh)))
               (real_plus dh (real_plus (real_opp dh) c))
               c).
      - apply (RealSetoid.real_eq_plus_compat dh
                 (real_plus c (real_opp dh)) dh
                 (real_plus (real_opp dh) c)
                 (real_eq_refl dh) (real_plus_comm c (real_opp dh))).
      - apply (real_eq_trans
                 (real_plus dh (real_plus (real_opp dh) c))
                 (real_plus (real_plus dh (real_opp dh)) c)
                 c).
        + exact (real_plus_assoc dh (real_opp dh) c).
        + apply (real_eq_trans
                   (real_plus (real_plus dh (real_opp dh)) c)
                   (real_plus real_zero c)
                   c).
          * apply (RealSetoid.real_eq_plus_compat
                     (real_plus dh (real_opp dh)) c real_zero c
                     (real_plus_opp dh) (real_eq_refl c)).
          * exact (real_eq_trans (real_plus real_zero c) (real_plus c real_zero) c
                       (real_plus_comm real_zero c) (real_plus_zero c)). }
    assert (Hlt2 : real_lt c (real_plus (sf_vfe v v) dh)).
    { apply (RealSetoid.real_lt_id_r c
               (real_plus dh (sf_vfe v v)) (real_plus (sf_vfe v v) dh)).
      - exact (real_plus_comm dh (sf_vfe v v)).
      - apply (RealSetoid.real_lt_id_l c
                 (real_plus dh (real_plus c (real_opp dh)))
                 (real_plus dh (sf_vfe v v))).
        + exact HeqL.
        + exact (real_lt_plus_translate dh (real_plus c (real_opp dh))
                   (sf_vfe v v) Hlt). }
    exact (real_lt_trans c (real_plus (sf_vfe v v) dh)
             (real_plus (sf_vfe v v) eps) Hlt2
             (real_lt_plus_translate (sf_vfe v v) dh eps Hde)).
  - (* eq branch: c - dh == vfe entails c == vfe + dh < vfe + eps. *)
    assert (Heqc : real_eq c (real_plus (sf_vfe v v) dh)).
    { apply (real_eq_trans c
               (real_plus (real_plus c (real_opp dh)) dh)
               (real_plus (sf_vfe v v) dh)).
      - apply real_eq_sym.
        apply (real_eq_trans
                 (real_plus (real_plus c (real_opp dh)) dh)
                 (real_plus c (real_plus (real_opp dh) dh))
                 c).
        + exact (real_eq_sym (real_plus c (real_plus (real_opp dh) dh))
                    (real_plus (real_plus c (real_opp dh)) dh)
                    (real_plus_assoc c (real_opp dh) dh)).
        + apply (real_eq_trans
                   (real_plus c (real_plus (real_opp dh) dh))
                   (real_plus c real_zero)
                   c).
          * apply (RealSetoid.real_eq_plus_compat c
                     (real_plus (real_opp dh) dh) c real_zero
                     (real_eq_refl c)
                     (real_eq_trans (real_plus (real_opp dh) dh)
                        (real_plus dh (real_opp dh)) real_zero
                        (real_plus_comm (real_opp dh) dh)
                        (real_plus_opp dh))).
          * exact (real_plus_zero c).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_plus c (real_opp dh)) dh (sf_vfe v v) dh
                 Heq (real_eq_refl dh)). }
    apply (RealSetoid.real_lt_id_l c (real_plus (sf_vfe v v) dh)
             (real_plus (sf_vfe v v) eps) Heqc
             (real_lt_plus_translate (sf_vfe v v) dh eps Hde)).
Defined.

(* ============================================================ *)
(* Assumption audit: every statement of this module is closed     *)
(* under the global context.                                      *)
(* ============================================================ *)
Print Assumptions fekl_diff_shift.
Print Assumptions fekl_d_eps.
Print Assumptions fekl_d_move_eps.
Print Assumptions fekl_mult_pos_le.
Print Assumptions fekl_mult_pos_le_b.
Print Assumptions fekl_gap_decomp_general.
Print Assumptions fekl_sumf_ext.
Print Assumptions fekl_sumf_add.
Print Assumptions fekl_sumf_linear.
Print Assumptions fekl_part_pos.
Print Assumptions fekl_fep_gap_le_b.
Print Assumptions fekl_fep_gap_canonical_le_b.
Print Assumptions fekl_fep_gap_eps.
Print Assumptions fekl_sf_vfe_ge_complexity_B.
