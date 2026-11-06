(* ConstructiveWorld-Set -- assumption-free instances of the UpReqSampling sum interface. *)

(** * UpAblT6_UpReqSampling: unconditional interface laws for the concrete finite sum.

    Mission.  Discharges the sumf interface assumptions of the two
      UpReqSampling sections (ReqUContraction, ReqBoundedSoftmax) at the
      concrete finite sum sumf := sumd_sumf S enum: extensionality, linearity,
      additivity, monotonicity and positivity ([uabT6_usamp_sum_ext],
      [uabT6_usamp_sum_linear], [uabT6_usamp_sum_add], [uabT6_usamp_sum_le],
      [uabT6_usamp_sum_swap_cc], [uabT6_bsoft_sum_ext], [uabT6_bsoft_sum_linear],
      [uabT6_bsoft_sum_pos], [uabT6_bsoft_sum_add], [uabT6_bsoft_sum_le], [uabT6_bsoft_sum_eq_list]).

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqSumD] of this development.

    References.  This development, UpAblT6_UpReqSampling.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblT6_UpReqSampling.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (the 9.3 magic). *)
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
(* Set-carrier completion: the interface class in this tree is unparameterized
   with carrier Real (cf. UpReqSampling.v/UpReqSumD.v); R is bridged to the
   global Real, and the operations resolve to the global instance
   RealEnhancedReal.  The statement faces are stated at the definitional
   raw-layer predicates real_eq/real_le/real_lt -- the same face as the
   UpReqSampling.v interface hypotheses -- so the extraction face carries
   no Obj.magic. *)
Notation R := Real.

(* ============ section A. ReqUContraction of UpReqSampling ============ *)
(* the original Context {R}{RIS} + S + sumf leaves the section in fully
   explicit form: the interface class in this tree is unparameterized with
   carrier Real, so R is the explicit global Real carrier (the RIS slot
   resolves through the class instance, no binder remains) and sumf becomes
   the concrete instance sumd_sumf S enum. *)

(* A1, from the sum_ext interface statement, signature carried verbatim:
   forall f g : S -> R, (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g). *)
Theorem uabT6_usamp_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* A2, from the sum_linear interface statement, signature carried verbatim:
   forall (a : R) (f : S -> R), real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f)). *)
Theorem uabT6_usamp_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
             (mult a (plus (f x) (sumd_list_sum S f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum S f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum S f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
                (distrib a (f x) (sumd_list_sum S f t)))).
Qed.

(* A3, from the sum_add interface statement, signature carried verbatim:
   forall f g : S -> R, real_eq (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)). *)
Theorem uabT6_usamp_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - (exact (req_trans (plus (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_refl (plus (f x) (g x))) IH) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (req_sym (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus_assoc (f x) (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (req_plus_compat (f x) (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus_assoc (g x) (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_trans (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (g x) (sumd_list_sum S f t)) (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t) (sumd_list_sum S g t) (plus_comm (g x) (sumd_list_sum S f t)) (req_refl (sumd_list_sum S g t))) (req_sym (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus_assoc (sumd_list_sum S f t) (g x) (sumd_list_sum S g t))))))) (plus_assoc (f x) (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))))).
Qed.

(* A4, from the sum_le interface statement, signature carried verbatim:
   forall f g : S -> R, (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g). *)
Theorem uabT6_usamp_sum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* A5, from the sum_swap_cc interface statement: the swap shape with a
   two-argument function; both sumf instance slots are replaced, and the
   proof re-derives the exchange in place by list induction (Hadd for the
   additive split of the inner sum, Hsw for the double-list reordering). *)
Theorem uabT6_usamp_sum_swap_cc :
  forall (S : Set) (enum : list S)
    (f : S -> S -> R),
    real_eq (sumd_sumf S enum (fun s : S => sumd_sumf S enum (fun s' : S => f s s')))
        (sumd_sumf S enum (fun s' : S => sumd_sumf S enum (fun s : S => f s s'))).
Proof.
  intros S enum f.
  unfold sumd_sumf.
  assert (Hadd : forall (l : list S) (u v : S -> R),
    real_eq (sumd_list_sum S (fun s : S => plus (u s) (v s)) l)
        (plus (sumd_list_sum S u l) (sumd_list_sum S v l))).
  { intros l u v.
    induction l as [| w tl IHl].
    - exact (req_sym (plus zero zero) zero (plus_zero zero)).
    - exact (req_trans
        (plus (plus (u w) (v w)) (sumd_list_sum S (fun s : S => plus (u s) (v s)) tl))
        (plus (plus (u w) (v w)) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl)))
        (plus (plus (u w) (sumd_list_sum S u tl)) (plus (v w) (sumd_list_sum S v tl)))
        (req_plus_compat (plus (u w) (v w)) (plus (u w) (v w))
           (sumd_list_sum S (fun s : S => plus (u s) (v s)) tl)
           (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl))
           (req_refl (plus (u w) (v w))) IHl)
        (req_trans
           (plus (plus (u w) (v w)) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl)))
           (plus (u w) (plus (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl))))
           (plus (plus (u w) (sumd_list_sum S u tl)) (plus (v w) (sumd_list_sum S v tl)))
           (req_sym
              (plus (u w) (plus (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl))))
              (plus (plus (u w) (v w)) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl)))
              (plus_assoc (u w) (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl))))
           (req_trans
              (plus (u w) (plus (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl))))
              (plus (u w) (plus (sumd_list_sum S u tl) (plus (v w) (sumd_list_sum S v tl))))
              (plus (plus (u w) (sumd_list_sum S u tl)) (plus (v w) (sumd_list_sum S v tl)))
              (req_plus_compat (u w) (u w)
                 (plus (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl)))
                 (plus (sumd_list_sum S u tl) (plus (v w) (sumd_list_sum S v tl)))
                 (req_refl (u w))
                 (req_trans
                    (plus (v w) (plus (sumd_list_sum S u tl) (sumd_list_sum S v tl)))
                    (plus (plus (v w) (sumd_list_sum S u tl)) (sumd_list_sum S v tl))
                    (plus (sumd_list_sum S u tl) (plus (v w) (sumd_list_sum S v tl)))
                    (plus_assoc (v w) (sumd_list_sum S u tl) (sumd_list_sum S v tl))
                    (req_trans
                       (plus (plus (v w) (sumd_list_sum S u tl)) (sumd_list_sum S v tl))
                       (plus (plus (sumd_list_sum S u tl) (v w)) (sumd_list_sum S v tl))
                       (plus (sumd_list_sum S u tl) (plus (v w) (sumd_list_sum S v tl)))
                       (req_plus_compat (plus (v w) (sumd_list_sum S u tl))
                          (plus (sumd_list_sum S u tl) (v w))
                          (sumd_list_sum S v tl) (sumd_list_sum S v tl)
                          (plus_comm (v w) (sumd_list_sum S u tl))
                          (req_refl (sumd_list_sum S v tl)))
                       (req_sym
                          (plus (sumd_list_sum S u tl) (plus (v w) (sumd_list_sum S v tl)))
                          (plus (plus (sumd_list_sum S u tl) (v w)) (sumd_list_sum S v tl))
                          (plus_assoc (sumd_list_sum S u tl) (v w) (sumd_list_sum S v tl))))))
              (plus_assoc (u w) (sumd_list_sum S u tl)
                 (plus (v w) (sumd_list_sum S v tl)))))). }
  assert (Hsw : forall l1 l2 : list S,
    real_eq (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) l1)
        (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') l1) l2)).
  { intros l1 l2.
    induction l1 as [| x t IH].
    - induction l2 as [| y t2 IH2].
      + exact (req_refl zero).
      + exact (req_trans zero
            (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
            (plus zero
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
            IH2
            (req_sym
               (plus zero
                  (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
               (req_trans
                  (plus zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
                  (plus
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
                     zero)
                  (sumd_list_sum S
                     (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2)
                  (plus_comm zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))
                  (plus_zero
                     (sumd_list_sum S
                        (fun s' : S => sumd_list_sum S (fun s : S => f s s') nil) t2))))).
    - exact (req_trans
            (plus (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) t))
            (plus (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2))
            (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') (x :: t)) l2)
            (req_plus_compat (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s' : S => f x s') l2)
               (sumd_list_sum S (fun s : S => sumd_list_sum S (fun s' : S => f s s') l2) t)
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2)
               (req_refl (sumd_list_sum S (fun s' : S => f x s') l2)) IH)
            (req_sym
               (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') (x :: t)) l2)
               (plus (sumd_list_sum S (fun s' : S => f x s') l2)
                  (sumd_list_sum S (fun s' : S => sumd_list_sum S (fun s : S => f s s') t) l2))
               (Hadd l2 (fun s' : S => f x s')
                  (fun s' : S => sumd_list_sum S (fun s : S => f s s') t)))). }
  exact (Hsw enum enum).
Qed.

(* ============ section B. ReqBoundedSoftmax of UpReqSampling ============ *)

(* B1, from the sum_ext interface statement. *)
Theorem uabT6_bsoft_sum_ext :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* B2, from the sum_linear interface statement. *)
Theorem uabT6_bsoft_sum_linear :
  forall (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
             (mult a (plus (f x) (sumd_list_sum S f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum S f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum S f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
                (distrib a (f x) (sumd_list_sum S f t)))).
Qed.

(* B3, from the sum_pos interface statement; the nonempty enum list is an
   explicit data slot, matching the shape of sumd_sum_pos of UpReqSumD. *)
Theorem uabT6_bsoft_sum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  unfold sumd_sumf.
  exact (sumd_list_sum_pos S f enum Hne H).
Qed.

(* B4, from the sum_add interface statement. *)
Theorem uabT6_bsoft_sum_add :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - (exact (req_trans (plus (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_refl (plus (f x) (g x))) IH) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (req_sym (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus_assoc (f x) (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (req_plus_compat (f x) (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus_assoc (g x) (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_trans (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (g x) (sumd_list_sum S f t)) (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t) (sumd_list_sum S g t) (plus_comm (g x) (sumd_list_sum S f t)) (req_refl (sumd_list_sum S g t))) (req_sym (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus_assoc (sumd_list_sum S f t) (g x) (sumd_list_sum S g t))))))) (plus_assoc (f x) (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))))).
Qed.

(* B5, from the sum_le interface statement. *)
Theorem uabT6_bsoft_sum_le :
  forall (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* B6, from the sum_eq_list interface statement: the list-sum bridge; on
   the concrete instance the conclusion real_eq (sumd_sumf S enum g)
   (sumd_list_sum S g enum) follows directly from sumd_sum_eq_list of
   UpReqSumD. *)
Theorem uabT6_bsoft_sum_eq_list :
  forall (S : Set) (enum : list S)
    (g : S -> R),
    real_eq (sumd_sumf S enum g) (sumd_list_sum S g enum).
Proof.
  intros S enum g.
  exact (sumd_sum_eq_list S enum g).
Qed.

(* ============ assumption audit (every statement Closed under the global context) ============ *)
Print Assumptions uabT6_usamp_sum_ext.
Print Assumptions uabT6_usamp_sum_linear.
Print Assumptions uabT6_usamp_sum_add.
Print Assumptions uabT6_usamp_sum_le.
Print Assumptions uabT6_usamp_sum_swap_cc.
Print Assumptions uabT6_bsoft_sum_ext.
Print Assumptions uabT6_bsoft_sum_linear.
Print Assumptions uabT6_bsoft_sum_pos.
Print Assumptions uabT6_bsoft_sum_add.
Print Assumptions uabT6_bsoft_sum_le.
Print Assumptions uabT6_bsoft_sum_eq_list.
