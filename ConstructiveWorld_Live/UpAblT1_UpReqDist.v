(* ConstructiveWorld-Set -- assumption-free instances of the UpReqDist sum interface. *)

(** * UpAblT1_UpReqDist: unconditional interface laws for the concrete finite sum.

    Mission.  Discharges the sumf interface assumptions of the five UpReqDist sections at the concrete
      finite sum sumf := sumd_sumf S enum: extensionality, additivity, linearity, monotonicity,
      positivity and the vanishing law ([uabT1_reqsumlayer_sum_ext], [uabT1_reqsumlayer_sum_add],
      [uabT1_reqsumlayer_sum_linear], [uabT1_reqfep_fsum_zero_nonneg], [uabT1_reqsteady_ssum_ext],
      [uabT1_reqprobdist_psum_add], [uabT1_reqsoftmaxdual_sumf_pos] and their sibling laws).

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqSumD] of this development.

    References.  This development, UpAblT1_UpReqDist.v, the baseline module in ConstructiveWorld-Main
      whose statement names are carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set] (decidable Q-carriers and
      boolean identity carriers); statements extract with [Obj.magic] = 0 and no erasure; [coqchk]
      reports [Axioms: none].  The positivity law [uabT1_reqfep_fsum_pos] carries an explicit
      nonempty-enum data slot [Not (enum = nil)] and holds only over nonempty enumerations.  The
      vanishing law [uabT1_reqfep_fsum_zero_nonneg] carries the surjective-data slot
      [forall s : S, sumd_in S s enum] as an explicit premise and holds only on the enumerated
      support.  The positivity law [uabT1_reqsoftmaxdual_sumf_pos] carries the same explicit
      nonempty-enum data slot [Not (enum = nil)] as [uabT1_reqfep_fsum_pos].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT1_UpReqDist.v] compiles cleanly (exit 0); the
      artifact starts with [436f7121 000160bc]. *)
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

(* R := Real by notation: the interface is the argument-less Class
   RealInterfaceEnhancedSetoid, whose law fields resolve as bare names
   through the global instance RealEnhancedReal (the UpReqSumD
   precedent). *)
Notation R := Real.

(* ============ section A. ReqSumLayer of UpReqDist ============ *)
(* the original Context {R}{RIS} + S + sumf reduces here to S + enum +
   sumf := sumd_sumf S enum: the interface is the argument-less Class
   RealInterfaceEnhancedSetoid (module RealInterfaceEnhancedMod), the
   argumented binder pair is dropped by the binder-shell-removal +
   notation-rebinding adaptation (Notation R := Real, the UpReqSumD
   precedent), and the statement predicate faces converge to the global
   real_eq / real_le / real_lt (the UpAblD1S15 precedent) so the
   statements extract without casts. *)

(* A1, from the sum_ext interface statement, signature carried verbatim:
   forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g). *)
Theorem uabT1_reqsumlayer_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* A2, from the sum_add interface statement, signature carried verbatim:
   req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)). *)
Theorem uabT1_reqsumlayer_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.  intros S enum f g.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s))))
             (plus (plus (f x) (g x))
                (plus (sumd_sumf S t f) (sumd_sumf S t g)))
             (plus (plus (f x) (sumd_sumf S t f))
                (plus (g x) (sumd_sumf S t g)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s)))
                (plus (sumd_sumf S t f) (sumd_sumf S t g))
                (req_refl (plus (f x) (g x))) IH)
             (UpReqAlgebra.req_plus_exchange (f x) (sumd_sumf S t f)
                (g x) (sumd_sumf S t g))).
Qed.

(* A3, from the sum_linear interface statement, signature carried verbatim:
   forall (a : R) (f : S -> R),
   req (sumf (fun s => mult a (f s))) (mult a (sumf f)). *)
Theorem uabT1_reqsumlayer_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.  intros S enum a f.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s))))
             (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
             (mult a (plus (f x) (sumd_sumf S t f)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s)))
                (mult a (sumd_sumf S t f))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_sumf S t f)))
                (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
                (distrib a (f x) (sumd_sumf S t f)))).
Qed.

(* ============ section B. ReqFEP of UpReqDist ============ *)

(* B1, from the fsum_ext interface statement. *)
Theorem uabT1_reqfep_fsum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* B2, from the fsum_add interface statement. *)
Theorem uabT1_reqfep_fsum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.  intros S enum f g.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s))))
             (plus (plus (f x) (g x))
                (plus (sumd_sumf S t f) (sumd_sumf S t g)))
             (plus (plus (f x) (sumd_sumf S t f))
                (plus (g x) (sumd_sumf S t g)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s)))
                (plus (sumd_sumf S t f) (sumd_sumf S t g))
                (req_refl (plus (f x) (g x))) IH)
             (UpReqAlgebra.req_plus_exchange (f x) (sumd_sumf S t f)
                (g x) (sumd_sumf S t g))).
Qed.

(* B3, from the fsum_linear interface statement. *)
Theorem uabT1_reqfep_fsum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.  intros S enum a f.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s))))
             (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
             (mult a (plus (f x) (sumd_sumf S t f)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s)))
                (mult a (sumd_sumf S t f))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_sumf S t f)))
                (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
                (distrib a (f x) (sumd_sumf S t f)))).
Qed.

(* B4, from the fsum_pos interface statement; the nonempty enum list is an
   explicit data slot, matching the shape of sumd_sum_pos of UpReqSumD. *)
Theorem uabT1_reqfep_fsum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.  intros S enum Hne f H.
  destruct enum as [| x t].
  - destruct (Hne eq_refl).
  - exact (lt_le_trans zero (f x) (plus (f x) (sumd_sumf S t f)) (H x)
             (le_id_l (f x) (plus (f x) zero) (plus (f x) (sumd_sumf S t f))
                (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
                (le_plus_compat (f x) (f x) zero (sumd_sumf S t f)
                   (le_refl (f x))
                   (sumd_list_sum_nonneg S f t
                      (fun s : S => sumd_lt_le (f s) (H s)))))).
Qed.

(* B5, from the fsum_le interface statement. *)
Theorem uabT1_reqfep_fsum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* B6, from the fsum_zero_nonneg interface statement; the surjectivity slot
   forall s : S, sumd_in S s enum is an explicit data slot, matching the
   shape of sumd_sum_zero_nonneg_surj of UpReqSumD. *)
Theorem uabT1_reqfep_fsum_zero_nonneg :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============ section C. ReqSteadyState of UpReqDist ============ *)

(* C1, from the ssum_ext interface statement, signature carried verbatim. *)
Theorem uabT1_reqsteady_ssum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* C2, from the ssum_linear interface statement, signature carried verbatim. *)
Theorem uabT1_reqsteady_ssum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.  intros S enum a f.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s))))
             (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
             (mult a (plus (f x) (sumd_sumf S t f)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s)))
                (mult a (sumd_sumf S t f))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_sumf S t f)))
                (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
                (distrib a (f x) (sumd_sumf S t f)))).
Qed.

(* ============ section D. ReqProbDist of UpReqDist ============ *)

(* D1, from the psum_linear interface statement, signature carried verbatim. *)
Theorem uabT1_reqprobdist_psum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.  intros S enum a f.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s))))
             (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
             (mult a (plus (f x) (sumd_sumf S t f)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_sumf S t (fun s : S => mult a (f s)))
                (mult a (sumd_sumf S t f))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_sumf S t f)))
                (plus (mult a (f x)) (mult a (sumd_sumf S t f)))
                (distrib a (f x) (sumd_sumf S t f)))).
Qed.

(* D2, from the psum_add interface statement, signature carried verbatim. *)
Theorem uabT1_reqprobdist_psum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.  intros S enum f g.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s))))
             (plus (plus (f x) (g x))
                (plus (sumd_sumf S t f) (sumd_sumf S t g)))
             (plus (plus (f x) (sumd_sumf S t f))
                (plus (g x) (sumd_sumf S t g)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_sumf S t (fun s : S => plus (f s) (g s)))
                (plus (sumd_sumf S t f) (sumd_sumf S t g))
                (req_refl (plus (f x) (g x))) IH)
             (UpReqAlgebra.req_plus_exchange (f x) (sumd_sumf S t f)
                (g x) (sumd_sumf S t g))).
Qed.

(* ============ section E. ReqSoftmaxDual of UpReqDist ============ *)
(* R and RIS were inherited from the enclosing ReqAlgBridge2 section in
   the source; here the binder pair is dropped by the same notation
   rebinding as every other section. *)

(* E1, from the sumf_pos interface statement; the nonempty enum list is an
   explicit data slot as in B4. *)
Theorem uabT1_reqsoftmaxdual_sumf_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.  intros S enum Hne f H.
  destruct enum as [| x t].
  - destruct (Hne eq_refl).
  - exact (lt_le_trans zero (f x) (plus (f x) (sumd_sumf S t f)) (H x)
             (le_id_l (f x) (plus (f x) zero) (plus (f x) (sumd_sumf S t f))
                (req_sym (plus (f x) zero) (f x) (plus_zero (f x)))
                (le_plus_compat (f x) (f x) zero (sumd_sumf S t f)
                   (le_refl (f x))
                   (sumd_list_sum_nonneg S f t
                      (fun s : S => sumd_lt_le (f s) (H s)))))).
Qed.

(* ============ assumption audit (every statement Closed under the global context) ============ *)
Print Assumptions uabT1_reqsumlayer_sum_ext.
Print Assumptions uabT1_reqsumlayer_sum_add.
Print Assumptions uabT1_reqsumlayer_sum_linear.
Print Assumptions uabT1_reqfep_fsum_ext.
Print Assumptions uabT1_reqfep_fsum_add.
Print Assumptions uabT1_reqfep_fsum_linear.
Print Assumptions uabT1_reqfep_fsum_pos.
Print Assumptions uabT1_reqfep_fsum_le.
Print Assumptions uabT1_reqfep_fsum_zero_nonneg.
Print Assumptions uabT1_reqsteady_ssum_ext.
Print Assumptions uabT1_reqsteady_ssum_linear.
Print Assumptions uabT1_reqprobdist_psum_linear.
Print Assumptions uabT1_reqprobdist_psum_add.
Print Assumptions uabT1_reqsoftmaxdual_sumf_pos.
