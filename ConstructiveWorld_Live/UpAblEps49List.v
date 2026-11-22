(* ConstructiveWorld-Set -- free-energy KL decomposition on the list carrier. *)

(** * UpAblEps49List: KL decomposition (theorem 4.9) on a finite state list.
    Mission.  The interface theorem [rkd_kl_decomp_full_partition]
      (UpAblEps49RKDBase) leaves [sumf_ext]/[sumf_add]/[sumf_linear] and the
      partition positivity [Zp] abstract.  This module discharges all of them
      for [sumf := real_list_sum] on a state list [l]:
      [e49l_real_kl_decomp_full_list] concludes
      [F(p) == F(p_b) + D * sum kl_term(p, p_b)] from ([Hp], [Hnormp]) alone;
      [e49l_boltzmann_normalized_list] supplies [sum p_b == 1].  A list may be
      empty (its sum is [real_zero], not normalized), so the empty case is
      excluded by explicit [Not (Id l nil)] premises.
    Dependencies.  Stdlib [QArith.Qring], [Extraction].  Requires [S01_BaseRing]
      through [S15_TailFEPUp], [UpAblEps49RKDBase]
      ([rkd_kl_decomp_full_partition], [rkd_boltzmann_normalized]),
      [UpAblZposReal] ([zabr_sum_over_S_pos]), [UpReqExpPos]
      ([upreq_real_zero_ne_one]).
    References.  UpAblEps49List.v, the ConstructiveWorld-Main baseline module
      with statement names carried over verbatim (Set-carrier completion); the
      fold algebra follows the S08 [RealListSumMain] pattern.
    Constructivity.  Every statement is carried by [Set] ([real_eq]/[real_lt]
      decidable Q-carriers; [Not]/[Id] the S01 set-layer aliases); proofs are
      transparent ([Defined]) so the witnesses extract; auxiliary lemmas
      proceed by list induction; extraction is expected at [Obj.magic] = 0.
    Build.  [coqc -q -Q . "" UpAblEps49List.v] compiles cleanly (exit 0).
      *)

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
Require Import UpAblEps49RKDBase.
Require Import UpAblZposReal.
Require Import UpReqExpPos.

(* Section 1. The list summation carrier: [e49l_sumf X l f] unfolds to       *)
(* [real_list_sum X f l] (the interface shape of the S08 fold).              *)
Definition e49l_sumf (X : Set) (l : list X) : (X -> Real) -> Real :=
  fun f => real_list_sum X f l.

(* Section 2. Structural premise one: extensionality (pointwise [real_eq]    *)
(* implies summation [real_eq], list form).                                  *)
Lemma e49l_lsum_ext : forall (X : Set) (l : list X) (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (e49l_sumf X l f) (e49l_sumf X l g).
Proof.
  intros X l f g H. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* Empty list: zero == zero. *)
    apply real_eq_refl.
  - (* Pointwise replacement of the head term plus the inductive
       replacement of the tail sum, through [real_eq_plus_compat_adapt]. *)
    exact (RealSetoid.real_eq_plus_compat_adapt
             (f w) (g w) (real_list_sum X f t) (real_list_sum X g t)
             (H w) IH).
Defined.

(* Section 3. Structural premise two: additivity (list form).                *)
Lemma e49l_lsum_add : forall (X : Set) (l : list X) (f g : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_plus (f s) (g s)))
          (real_plus (e49l_sumf X l f) (e49l_sumf X l g)).
Proof.
  intros X l f g. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* Empty list: zero == zero + zero. *)
    apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - (* Middle rearrangement: (fw+gw)+(Ft+Gt) == (fw+Ft)+(gw+Gt), where Ft   *)
    (* and Gt are the tail sums; closed by [real_plus_swap_mid].            *)
    apply (real_eq_trans _
               (real_plus (real_plus (f w) (g w))
                          (real_plus (real_list_sum X f t)
                                     (real_list_sum X g t))) _).
    + exact (RealSetoid.real_eq_plus_compat_adapt
               (real_plus (f w) (g w)) (real_plus (f w) (g w))
               (real_list_sum X (fun s : X => real_plus (f s) (g s)) t)
               (real_plus (real_list_sum X f t) (real_list_sum X g t))
               (real_eq_refl _) IH).
    + exact (real_plus_swap_mid (f w) (g w)
               (real_list_sum X f t) (real_list_sum X g t)).
Defined.

(* Section 4. Structural premise three: scalar linearity (list form).        *)
Lemma e49l_lsum_linear : forall (X : Set) (l : list X) (a : Real) (f : X -> Real),
  real_eq (e49l_sumf X l (fun s : X => real_mult a (f s)))
          (real_mult a (e49l_sumf X l f)).
Proof.
  intros X l a f. unfold e49l_sumf.
  induction l as [| w t IH]; simpl.
  - (* Empty list: zero == a * zero. *)
    apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - (* [real_distrib] read backwards, plus the inductive replacement of     *)
    (* the tail sum.                                                        *)
    apply (real_eq_trans _
               (real_plus (real_mult a (f w))
                          (real_mult a (real_list_sum X f t))) _).
    + exact (RealSetoid.real_eq_plus_compat_adapt
               (real_mult a (f w)) (real_mult a (f w))
               (real_list_sum X (fun s : X => real_mult a (f s)) t)
               (real_mult a (real_list_sum X f t))
               (real_eq_refl _) IH).
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum X f t)))
                         (real_plus (real_mult a (f w))
                                    (real_mult a (real_list_sum X f t)))).
      apply (real_distrib a (f w) (real_list_sum X f t)).
Defined.

(* Section 5. Normalization implies non-emptiness (standalone named lemma).  *)
(* The empty-list sum is provably zero (transport along [Id] to [nil] plus   *)
(* iota reduction), while a normalized sum cannot be zero by the zero-one    *)
(* separation lemma [upreq_real_zero_ne_one].  The whole chain stays on the  *)
(* S01 set-layer aliases: no proposition face.                               *)
Lemma e49l_nonempty_of_norm : forall (X : Set) (l : list X) (p : X -> Real),
  real_eq (real_list_sum X p l) real_one -> Not (Id l nil).
Proof.
  intros X l p Hnorm Hnil.
  assert (Hsum0 : real_eq (real_list_sum X p l) real_zero).
  { exact (real_eq_trans (real_list_sum X p l) (real_list_sum X p nil)
             real_zero
             (match Hnil in Id _ y return
                real_eq (real_list_sum X p l) (real_list_sum X p y)
              with id_refl => real_eq_refl _ end)
             (real_eq_refl real_zero)). }
  exact (upreq_real_zero_ne_one
          (real_eq_trans real_zero (real_list_sum X p l) real_one
             (real_eq_sym (real_list_sum X p l) real_zero Hsum0) Hnorm)).
Defined.

(* Section 6. Partition positivity (list form): the provable shape of        *)
(* "the exponential sum is positive".  Itemwise positivity                   *)
(* ([real_exp_neg_pos]) is closed by the fold positivity lemma               *)
(* [zabr_sum_over_S_pos]; the non-emptiness premise uses the S01             *)
(* set-layer aliases.                                                        *)
Lemma e49l_partition_pos : forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
  (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_lt real_zero
    (real_list_sum X (fun s : X => real_exp_neg
                         (real_mult (real_inv_pos D D_pos) (e s))) l).
Proof.
  intros X l Hnn e D D_pos.
  apply (zabr_sum_over_S_pos X
           (fun s : X => real_exp_neg
                          (real_mult (real_inv_pos D D_pos) (e s))) l).
  - exact Hnn.
  - intro s. apply real_exp_neg_pos.
Defined.

(* Section 7. Main statement: the premise shape carrying only [Hp] and       *)
(* [Hnormp], fully instantiated on the list carrier.  The carrier is         *)
(* concrete: [sumf := e49l_sumf X l] with the three structural premises      *)
(* proved above, the partition function taken definitionally as the          *)
(* exponential sum, positivity and non-emptiness discharged internally       *)
(* ([e49l_partition_pos] fed by [e49l_nonempty_of_norm]); the conclusion     *)
(* matches the global interface shape verbatim.                              *)
Theorem e49l_real_kl_decomp_full_list :
  forall (X : Set) (l : list X)
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p l) real_one),
  real_eq (real_free_energy X (e49l_sumf X l) e D p Hp)
          (real_plus
             (real_free_energy X (e49l_sumf X l) e D
                (real_boltzmann_dist_r X e D D_pos
                   (real_list_sum X (fun s : X => real_exp_neg
                                        (real_mult (real_inv_pos D D_pos) (e s))) l)
                   (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                      e D D_pos))
                (real_boltzmann_dist_r_pos X e D D_pos
                   (real_list_sum X (fun s : X => real_exp_neg
                                        (real_mult (real_inv_pos D D_pos) (e s))) l)
                   (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                      e D D_pos)))
             (real_mult D
                (e49l_sumf X l (fun s : X =>
                   real_kl_term (p s)
                     (real_boltzmann_dist_r X e D D_pos
                        (real_list_sum X (fun s0 : X => real_exp_neg
                                             (real_mult (real_inv_pos D D_pos) (e s0))) l)
                        (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                           e D D_pos) s)
                     (Hp s)
                     (real_boltzmann_dist_r_pos X e D D_pos
                        (real_list_sum X (fun s0 : X => real_exp_neg
                                             (real_mult (real_inv_pos D D_pos) (e s0))) l)
                        (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
                           e D D_pos) s))))).
Proof.
  intros X l e D D_pos p Hp Hnormp.
  exact (rkd_kl_decomp_full_partition X (e49l_sumf X l)
           (e49l_lsum_ext X l) (e49l_lsum_add X l) (e49l_lsum_linear X l)
           e D D_pos p Hp Hnormp
           (e49l_partition_pos X l (e49l_nonempty_of_norm X l p Hnormp)
              e D D_pos)).
Defined.

(* Section 8. Companion: the family's second normalization premise           *)
(* ([sum p_b == 1]) in list form.  The partition function is definitional,   *)
(* so [Hpart] is [real_eq_refl]; the normalization is discharged by          *)
(* [real_eq_refl]; the normalization is discharged by                        *)
(* [rkd_boltzmann_normalized].  Applicability note: a list need not be       *)
(* non-empty, so the statement carries [Not (Id l nil)] explicitly.          *)
Theorem e49l_boltzmann_normalized_list :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_eq
    (real_list_sum X
       (real_boltzmann_dist_r X e D D_pos
          (real_list_sum X (fun s : X => real_exp_neg
                               (real_mult (real_inv_pos D D_pos) (e s))) l)
          (e49l_partition_pos X l Hnn e D D_pos)) l)
    real_one.
Proof.
  intros X l Hnn e D D_pos.
  exact (rkd_boltzmann_normalized X (e49l_sumf X l)
           (e49l_lsum_ext X l) (e49l_lsum_linear X l) e D D_pos
           (real_list_sum X (fun s : X => real_exp_neg
                                (real_mult (real_inv_pos D D_pos) (e s))) l)
           (e49l_partition_pos X l Hnn e D D_pos)
           (real_eq_refl _)).
Defined.

(* ================= Dependency audit ================= *)
(* every statement of this module is closed under the global context.        *)
Print Assumptions e49l_lsum_ext.
Print Assumptions e49l_lsum_add.
Print Assumptions e49l_lsum_linear.
Print Assumptions e49l_nonempty_of_norm.
Print Assumptions e49l_partition_pos.
Print Assumptions e49l_real_kl_decomp_full_list.
Print Assumptions e49l_boltzmann_normalized_list.

(* ================= Extraction audit (isolated output directory) ================= *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_e49list_extract".
(* One merged command: separate [Separate Extraction] commands overwrite     *)
(* each other's output (only the last closure survives), so all eight names  *)
(* go out in a single shot.                                                  *)
Separate Extraction e49l_sumf e49l_lsum_ext e49l_lsum_add e49l_lsum_linear
  e49l_nonempty_of_norm e49l_partition_pos
  e49l_real_kl_decomp_full_list e49l_boltzmann_normalized_list.
