(* ConstructiveWorld-Set -- assumption-free instances of the UpReqAlign sum interface. *)

(** * UpAblT3_UpReqAlign: unconditional interface laws for the concrete finite sum.

    Mission.  Discharges the sumf interface assumptions of the four UpReqAlign sections at the concrete
      finite sum sumf := sumd_sumf S enum: extensionality, additivity, linearity, monotonicity,
      positivity and the vanishing law ([uabT3_reqalign_sum_ext], [uabT3_reqalign_sum_add],
      [uabT3_reqalign_sum_linear], [uabT3_reqalign_sum_pos], [uabT3_reqalign_sum_le],
      [uabT3_reqalign_sum_zero_nonneg], restated for the twin sections as [uabT3_reqklproj_*],
      [uabT3_reqnatgrad_*], [uabT3_reqpporatio_*]).

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqSumD] of this development.

    References.  This development, UpAblT3_UpReqAlign.v, the baseline module in ConstructiveWorld-Main
      whose statement names are carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set] (decidable Q-carriers and
      boolean identity carriers); statements extract with [Obj.magic] = 0 and no erasure; [coqchk]
      reports [Axioms: none].  The positivity law [uabT3_reqalign_sum_pos] carries an explicit
      nonempty-enum data slot [Not (enum = nil)] and holds only over nonempty enumerations.  The
      vanishing laws [uabT3_reqalign_sum_zero_nonneg] and [uabT3_reqnatgrad_sum_zero_nonneg] carry the
      surjective-data slot [forall s : S, sumd_in S s enum] as an explicit premise and hold only on the
      enumerated support.

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT3_UpReqAlign.v] compiles cleanly (exit 0); the
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

(* ============ section A. ReqAlignCore of UpReqAlign ============ *)
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
Theorem uabT3_reqalign_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* A2, from the sum_add interface statement, signature carried verbatim:
   req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)). *)
Theorem uabT3_reqalign_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
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
Theorem uabT3_reqalign_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
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

(* A4, from the sum_pos interface statement; the nonempty enum list is an
   explicit data slot, matching the shape of sumd_sum_pos of UpReqSumD. *)
Theorem uabT3_reqalign_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
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

(* A5, from the sum_le interface statement. *)
Theorem uabT3_reqalign_sum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* A6, from the sum_zero_nonneg interface statement; the surjectivity slot
   forall s : S, sumd_in S s enum is an explicit data slot, matching the
   shape of sumd_sum_zero_nonneg_surj of UpReqSumD. *)
Theorem uabT3_reqalign_sum_zero_nonneg :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0.
  assert (Hmain : forall (l : list S) (s0 : S),
            sumd_in S s0 l -> real_eq (sumd_sumf S l f) zero -> real_eq (f s0) zero).
  { intros l s0 Hs H0'. revert H0'.
    induction Hs as [y u Heq | y u Ht IH]; intro H0'.
    - destruct Heq.
      exact (le_antisym (f y) zero
               (le_trans (f y) (plus (f y) (sumd_sumf S u f)) zero
                  (le_id_l (f y) (plus (f y) zero)
                     (plus (f y) (sumd_sumf S u f))
                     (req_sym (plus (f y) zero) (f y) (plus_zero (f y)))
                     (le_plus_compat (f y) (f y) zero (sumd_sumf S u f)
                        (le_refl (f y)) (sumd_list_sum_nonneg S f u Hnn)))
                  (le_id_r (plus (f y) (sumd_sumf S u f))
                     (plus (f y) (sumd_sumf S u f)) zero
                     H0' (le_refl (plus (f y) (sumd_sumf S u f)))))
               (Hnn y)).
    - exact (IH
               (le_antisym (sumd_sumf S u f) zero
                  (le_trans (sumd_sumf S u f)
                     (plus (sumd_sumf S u f) (f y)) zero
                     (le_id_l (sumd_sumf S u f)
                        (plus (sumd_sumf S u f) zero)
                        (plus (sumd_sumf S u f) (f y))
                        (req_sym (plus (sumd_sumf S u f) zero)
                           (sumd_sumf S u f) (plus_zero (sumd_sumf S u f)))
                        (le_plus_compat (sumd_sumf S u f)
                           (sumd_sumf S u f) zero (f y)
                           (le_refl (sumd_sumf S u f)) (Hnn y)))
                     (le_id_r (plus (sumd_sumf S u f) (f y))
                        (plus (sumd_sumf S u f) (f y)) zero
                        (req_trans (plus (sumd_sumf S u f) (f y))
                           (plus (f y) (sumd_sumf S u f)) zero
                           (plus_comm (sumd_sumf S u f) (f y)) H0')
                        (le_refl (plus (sumd_sumf S u f) (f y)))))
                  (sumd_list_sum_nonneg S f u Hnn))). }
  intro s. exact (Hmain enum s (Hsurj s) H0).
Qed.

(* ============ section B. ReqKLProjection of UpReqAlign ============ *)

(* B1, from the sum_ext interface statement. *)
Theorem uabT3_reqklproj_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* B2, from the sum_add interface statement. *)
Theorem uabT3_reqklproj_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
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

(* B3, from the sum_linear interface statement. *)
Theorem uabT3_reqklproj_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
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

(* B4, from the sum_le interface statement. *)
Theorem uabT3_reqklproj_sum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* ============ section C. ReqNaturalGradient of UpReqAlign ============ *)

(* C1, from the sum_zero_nonneg interface statement; the surjectivity slot
   is an explicit data slot as in A6, matching the shape of
   sumd_sum_zero_nonneg_surj of UpReqSumD. *)
Theorem uabT3_reqnatgrad_sum_zero_nonneg :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0.
  assert (Hmain : forall (l : list S) (s0 : S),
            sumd_in S s0 l -> real_eq (sumd_sumf S l f) zero -> real_eq (f s0) zero).
  { intros l s0 Hs H0'. revert H0'.
    induction Hs as [y u Heq | y u Ht IH]; intro H0'.
    - destruct Heq.
      exact (le_antisym (f y) zero
               (le_trans (f y) (plus (f y) (sumd_sumf S u f)) zero
                  (le_id_l (f y) (plus (f y) zero)
                     (plus (f y) (sumd_sumf S u f))
                     (req_sym (plus (f y) zero) (f y) (plus_zero (f y)))
                     (le_plus_compat (f y) (f y) zero (sumd_sumf S u f)
                        (le_refl (f y)) (sumd_list_sum_nonneg S f u Hnn)))
                  (le_id_r (plus (f y) (sumd_sumf S u f))
                     (plus (f y) (sumd_sumf S u f)) zero
                     H0' (le_refl (plus (f y) (sumd_sumf S u f)))))
               (Hnn y)).
    - exact (IH
               (le_antisym (sumd_sumf S u f) zero
                  (le_trans (sumd_sumf S u f)
                     (plus (sumd_sumf S u f) (f y)) zero
                     (le_id_l (sumd_sumf S u f)
                        (plus (sumd_sumf S u f) zero)
                        (plus (sumd_sumf S u f) (f y))
                        (req_sym (plus (sumd_sumf S u f) zero)
                           (sumd_sumf S u f) (plus_zero (sumd_sumf S u f)))
                        (le_plus_compat (sumd_sumf S u f)
                           (sumd_sumf S u f) zero (f y)
                           (le_refl (sumd_sumf S u f)) (Hnn y)))
                     (le_id_r (plus (sumd_sumf S u f) (f y))
                        (plus (sumd_sumf S u f) (f y)) zero
                        (req_trans (plus (sumd_sumf S u f) (f y))
                           (plus (f y) (sumd_sumf S u f)) zero
                           (plus_comm (sumd_sumf S u f) (f y)) H0')
                        (le_refl (plus (sumd_sumf S u f) (f y)))))
                  (sumd_list_sum_nonneg S f u Hnn))). }
  intro s. exact (Hmain enum s (Hsurj s) H0).
Qed.

(* ============ section D. ReqPPORatio of UpReqAlign ============ *)

(* D1, from the sum_ext interface statement. *)
Theorem uabT3_reqpporatio_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_sumf S t f) (sumd_sumf S t g)
             (H x) IH).
Qed.

(* D2, from the sum_add interface statement. *)
Theorem uabT3_reqpporatio_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
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

(* ============ assumption audit (every statement Closed under the global context) ============ *)
Print Assumptions uabT3_reqalign_sum_ext.
Print Assumptions uabT3_reqalign_sum_add.
Print Assumptions uabT3_reqalign_sum_linear.
Print Assumptions uabT3_reqalign_sum_pos.
Print Assumptions uabT3_reqalign_sum_le.
Print Assumptions uabT3_reqalign_sum_zero_nonneg.
Print Assumptions uabT3_reqklproj_sum_ext.
Print Assumptions uabT3_reqklproj_sum_add.
Print Assumptions uabT3_reqklproj_sum_linear.
Print Assumptions uabT3_reqklproj_sum_le.
Print Assumptions uabT3_reqnatgrad_sum_zero_nonneg.
Print Assumptions uabT3_reqpporatio_sum_ext.
Print Assumptions uabT3_reqpporatio_sum_add.
