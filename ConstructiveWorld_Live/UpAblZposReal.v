(* ConstructiveWorld-Set -- real-layer instance modules of the upstream alignment families. *)

(** * UpAblZposReal: real-layer positivity of the [Z_align] partition function.

    Mission.  This file realizes the alignment partition function [Z_align] at the
      real layer and discharges its positivity constructively: the definition
      [zabr_Z_align] (reference-policy weights times exponentials of scaled
      negated rewards, summed over the state list), the fold lemma
      [zabr_list_sum_pos_cons] (positivity of the cons sum by witness
      construction in each branch), the companion [zabr_sum_over_S_pos]
      (positivity of sums over a non-empty list), and the main theorem
      [zabr_Z_align_pos].

    Dependencies.  Stdlib [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO] and [UpReqExpPos] of this development.

    References.  This development, UpAblZposReal.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblZposReal.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqExpPos.
From Stdlib Require Import Extraction.

(* ================= Section 1. Real-layer definition of the partition function (verbatim counterpart face of the S05 main section) ================= *)
Definition zabr_Z_align (X : Set) (l : list X)
  (reward : X -> Real) (beta : Real) (beta_pos : real_lt real_zero beta)
  (pi_ref : X -> Real) : Real :=
  real_list_sum X (fun s => real_mult (pi_ref s)
    (real_exp_neg (real_opp (real_mult (real_inv_pos beta beta_pos) (reward s))))) l.

(* ================= Section 2. First companion: the fold induction lemma ================= *)
(* The statement quantifies over an arbitrary head [w] of the cons sum: in  *)
(* the induction step the tail sum is exactly the previous instance, so the *)
(* non-emptiness premise stays outside the induction.  The base case is the *)
(* single element ([f w + 0] positive); the step case is a positive head    *)
(* and a positive tail sum.                                                 *)
Lemma zabr_list_sum_pos_cons :
  forall (X : Set) (f : X -> Real) (l : list X) (w : X),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f (w :: l)).
Proof.
  intros X f l.
  induction l as [| x t IH]; intro w; intro Hf.
  - (* Base case: the sum over the single-element list equals [f w + 0]. *)
    simpl.
    apply (RealSetoid.real_lt_id_r real_zero (f w) (real_plus (f w) real_zero)).
    + apply (real_eq_sym (real_plus (f w) real_zero) (f w)).
      apply (real_plus_zero (f w)).
    + exact (Hf w).
  - (* Step case: [f w] and the sum over [w :: t] are both positive; the zero side records the canonical form. *)
    simpl.
    apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
             (real_plus (f w) (real_plus (f x) (real_list_sum X f t)))).
    + apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
      apply (real_plus_zero real_zero).
    + apply (real_lt_plus_compat real_zero (f w) real_zero
               (real_plus (f x) (real_list_sum X f t))).
      * exact (Hf w).
      * exact (IH x Hf).
Qed.

(* ================= Section 3. Second companion: real-layer form of positivity of sums ================= *)
(* Aligned with the S05 [sum_over_S] positivity form: for all [f],           *)
(* itemwise positivity gives positivity of the sum.  The non-emptiness       *)
(* premise is the weakest realizable completion at the real layer (the S01   *)
(* set-layer [Not] and [Id]; zero proposition-face leakage).                 *)
Theorem zabr_sum_over_S_pos :
  forall (X : Set) (f : X -> Real) (l : list X),
    Not (Id l nil) ->
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (real_list_sum X f l).
Proof.
  intros X f l Hnn Hf.
  destruct l as [| w rest].
  - (* Empty list: immediate contradiction with the non-emptiness premise. *)
    destruct (Hnn id_refl).
  - (* Non-empty case: reduction to the fold lemma [zabr_list_sum_pos_cons]. *)
    exact (zabr_list_sum_pos_cons X f rest w Hf).
Qed.

(* ================= Section 4. Main theorem: unconditional real-layer discharge of Z_align positivity ================= *)
(* The statement face is aligned verbatim with the S05 main section: the    *)
(* [Z_align] body is the finite sum of reference-policy weights times the   *)
(* exponentials of the scaled negated rewards; the premises are itemwise    *)
(* positivity, normalization, and positive temperature.                     *)
Theorem zabr_Z_align_pos :
  forall (X : Set) (l : list X) (reward : X -> Real) (beta : Real)
         (beta_pos : real_lt real_zero beta) (pi_ref : X -> Real),
    (forall s : X, real_lt real_zero (pi_ref s)) ->
    real_eq (real_list_sum X pi_ref l) real_one ->
    real_lt real_zero (zabr_Z_align X l reward beta beta_pos pi_ref).
Proof.
  intros X l reward beta beta_pos pi_ref Hrefpos Hnorm.
  unfold zabr_Z_align.
  apply (zabr_sum_over_S_pos X _ l).
  - (* The list is non-empty: normalization gives sum = one while the empty
       list would give sum = zero, so the zero-one separation lemma
       [upreq_real_zero_ne_one] yields the contradiction. *)
    intro Hnil.
    assert (Hsum0 : real_eq (real_list_sum X pi_ref l) real_zero).
    { exact (real_eq_trans (real_list_sum X pi_ref l) (real_list_sum X pi_ref nil)
               real_zero
               (match Hnil in Id _ y return
                  real_eq (real_list_sum X pi_ref l) (real_list_sum X pi_ref y)
                with id_refl => real_eq_refl _ end)
               (real_eq_refl real_zero)). }
    exact (upreq_real_zero_ne_one
            (real_eq_trans real_zero (real_list_sum X pi_ref l) real_one
               (real_eq_sym (real_list_sum X pi_ref l) real_zero Hsum0) Hnorm)).
  - (* Itemwise positivity: positive reference weight times positive exponential ([real_mult_positive] with [real_exp_neg_pos]). *)
    intro s.
    apply real_mult_positive.
    + exact (Hrefpos s).
    + apply real_exp_neg_pos.
Qed.

(* ================= Section 5. Assumption audit (Print Assumptions) ================= *)
Print Assumptions zabr_list_sum_pos_cons.
Print Assumptions zabr_sum_over_S_pos.
Print Assumptions zabr_Z_align_pos.

(* ================= Section 6. Extraction audit (isolated output directory) ================= *)
Set Extraction Output Directory "../_ab2_zposreal_extract".
Separate Extraction zabr_Z_align.
Separate Extraction zabr_list_sum_pos_cons.
Separate Extraction zabr_sum_over_S_pos.
Separate Extraction zabr_Z_align_pos.
