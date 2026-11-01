(* ==========================================================================
   ConcMixSelFeed.v -- req-layer supply family for the conc/mix/select
   interface (Set-lineage aligned generation).
   Mission.  Eleven cms_ pieces: the two lt_plus_compat lt/le selections
   (cms_lt_plus_compat_lt_le_sel / cms_lt_plus_compat_lt_le_time), the four
   sum pieces on the sumd_sumf folding key (extensionality / linearity /
   additivity / order: cms_sum_ext / cms_sum_linear / cms_sum_add /
   cms_sum_le), the folding coherence pair (cms_fold_req_list_sum /
   cms_sum_eq_list), the bs_swap double-list exchange, and the bs_abs /
   bs_lpc companions; every piece ends in Defined, zero admitted literals.
   Dependencies.  S01_BaseRing..S15_TailFEPUp, UpReqAlgebra, UpReqSumD,
   UpReqSampling, Stdlib List.  Interface note: in this tree
   RealInterfaceEnhancedSetoid is the argument-less Class of module
   RealInterfaceEnhancedMod (S07_RealSetoidExpLog.v); its fields resolve
   through the global Real instance RealEnhancedReal.  Carrier note:
   req/lt/le are bound by Notation directly to the concrete S02_CauchyComplete
   forms real_eq/real_lt/real_le -- the very bindings the global instance
   RealEnhancedReal assigns to these fields, so each statement elaborates to
   the same term as before; only the boxed class-field projections (which
   extract as erased type faces) are replaced by the informative concrete
   carriers (UpAlignIdReq.v form).
   References.  The req-layer unified instance family of the sum and mix
   interface (interface adapter layer).
   Constructivity.  Statements ride the Set layer (req/le/lt/plus are
   Set-valued interface fields, zero Prop leakage); zero extraction casts,
   zero classical logic; every proof ends in Defined and the trailing Print
   Assumptions block covers all eleven pieces.
   Build.  Rocq 9.1 direct rocq c -native-compiler no -Q . "" (vo shadow
   tree, same-world rebuild), cpu_guard wrapped, ulimit -s 65532.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* Carrier binding of the statement-face relation fields: req/lt/le are bound *)
(* by Notation directly to the concrete S02_CauchyComplete forms              *)
(* real_eq/real_lt/real_le -- the very bindings the global instance           *)
(* RealEnhancedReal assigns to these fields (S07_RealSetoidExpLog.v), so      *)
(* each statement elaborates to the same term as before; only the boxed       *)
(* class-field projections (which extract as erased type faces) are replaced  *)
(* by the informative concrete carriers.  Same form as UpAlignIdReq.v.        *)
Notation lt := real_lt.
Notation req := real_eq.
Notation le := real_le.

(* World pins the Cauchy Real face (the lt_plus mixed monotonicity body is   *)
(* an S07 Real-layer finished product; interface fields resolve through the  *)
(* global RealEnhancedReal instance).                                        *)

(* ========= Slots 1/2: lt_plus_compat_lt_le x2 (S07 Real-layer product) ========= *)

Theorem cms_lt_plus_compat_lt_le_sel :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

Theorem cms_lt_plus_compat_lt_le_time :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ========= Slots 3-6: the four sum slots (sumd_sumf folding key, ========= *)
(* ========= generic in S0/en)                                             ========= *)

Theorem cms_sum_ext : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) -> req (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

Theorem cms_sum_linear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => mult a (f s)))
        (mult a (sumd_sumf S0 en f)).
Proof.
  intros S0 en a f.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - simpl.
    exact (req_sym
             (mult a (plus (f x) (sumd_list_sum S0 f t)))
             (plus (mult a (f x))
                     (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
             (req_trans
                (mult a (plus (f x) (sumd_list_sum S0 f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S0 f t)))
                (plus (mult a (f x))
                        (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
                (distrib a (f x) (sumd_list_sum S0 f t))
                (req_plus_compat (mult a (f x)) (mult a (f x))
                   (mult a (sumd_list_sum S0 f t))
                   (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                   (req_refl (mult a (f x)))
                   (req_sym
                      (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                      (mult a (sumd_list_sum S0 f t)) IH)))).
Defined.

Theorem cms_sum_add :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => plus (f s) (g s)))
        (plus (sumd_sumf S0 en f) (sumd_sumf S0 en g)).
Proof.
  intros S0 en f g.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - simpl.
    exact (req_trans
             (plus (plus (f x) (g x))
                     (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                     (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))
             (plus (plus (f x) (sumd_list_sum S0 f t))
                     (plus (g x) (sumd_list_sum S0 g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t)
                (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_sym
                (plus (plus (f x) (sumd_list_sum S0 f t))
                        (plus (g x) (sumd_list_sum S0 g t)))
                (plus (plus (f x) (g x))
                        (plus (sumd_list_sum S0 f t)
                                (sumd_list_sum S0 g t)))
                (req_plus_exchange (f x) (g x)
                   (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))).
Defined.

Theorem cms_sum_le :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, le (f s) (g s)) -> le (sumd_sumf S0 en f) (sumd_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (le_refl zero).
  - simpl.
    exact (le_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

(* ========= Slot 8: sum_eq_list (folding-adapter shim + definitional ========= *)
(* ========= unfolding)                                                    ========= *)

(* Shim for the two isomorphic folding machines: sumd_list_sum and            *)
(* rsq_bs_list_sum are constructor-wise identical in shape (the nil branch    *)
(* both returns zero, the cons branch both folds plus over head and tail);    *)
(* one list-induction step, joined by req_plus_compat (the req folding face   *)
(* of the SumEqList shim, re-cast).                                           *)
Lemma cms_fold_req_list_sum :
  forall (S0 : Set) (g : S0 -> Real) (l : list S0),
    req (sumd_list_sum S0 g l) (rsq_bs_list_sum S0 g l).
Proof.
  intros S0 g l.
  induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (g x) (g x)
             (sumd_list_sum S0 g t) (rsq_bs_list_sum S0 g t)
             (req_refl (g x)) IH).
Defined.

Theorem cms_sum_eq_list : forall (S0 : Set) (en : list S0) (g : S0 -> Real),
  req (sumd_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof.
  intros S0 en g.
  unfold sumd_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl.
    exact (req_plus_compat (g x) (g x) (sumd_list_sum S0 g t)
             (rsq_bs_list_sum S0 g t) (req_refl (g x)) IH).
Defined.

(* ========= Slot 7: bs_swap (double-list generic exchange induction) ========= *)

Theorem cms_bs_swap :
  forall (S0 : Set) (en : list S0) (f : S0 -> S0 -> Real),
    req (sumd_sumf S0 en (fun s : S0 => sumd_sumf S0 en (fun s' : S0 => f s s')))
        (sumd_sumf S0 en (fun s' : S0 => sumd_sumf S0 en (fun s : S0 => f s s'))).
Proof.
  intros S0 en f.
  unfold sumd_sumf.
  assert (Hsw : forall l1 l2 : list S0,
    req (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) l1)
        (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') l1) l2)).
  { intros l1 l2.
    induction l1 as [| x t IH].
    - induction l2 as [| y t2 IH2].
      + exact (req_refl zero).
      + exact (req_trans zero
            (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
            (plus zero
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
            IH2
            (req_sym
               (plus zero
                  (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
               (req_trans
                  (plus zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
                  (plus
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
                     zero)
                  (sumd_list_sum S0
                     (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2)
                  (plus_comm zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))
                  (plus_zero
                     (sumd_list_sum S0
                        (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') nil) t2))))).
    - exact (req_trans
            (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) t))
            (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2))
            (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') (x :: t)) l2)
            (req_plus_compat (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
               (sumd_list_sum S0 (fun s : S0 => sumd_list_sum S0 (fun s' : S0 => f s s') l2) t)
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2)
               (req_refl (sumd_list_sum S0 (fun s' : S0 => f x s') l2)) IH)
            (req_sym
               (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') (x :: t)) l2)
               (plus (sumd_list_sum S0 (fun s' : S0 => f x s') l2)
                  (sumd_list_sum S0 (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t) l2))
               (cms_sum_add S0 l2 (fun s' : S0 => f x s')
                  (fun s' : S0 => sumd_list_sum S0 (fun s : S0 => f s s') t)))). }
  exact (Hsw en en).
Defined.

(* ========= Adjacent companions 9/10: bs_abs / bs_lpc ========================= *)

Theorem cms_bs_abs : forall a : Real, le zero a -> req (abs a) a.
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

Theorem cms_bs_lpc :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ========= Self-check block (G4 gauge: per-piece Closed evidence) ============ *)

Print Assumptions cms_lt_plus_compat_lt_le_sel.
Print Assumptions cms_lt_plus_compat_lt_le_time.
Print Assumptions cms_sum_ext.
Print Assumptions cms_sum_linear.
Print Assumptions cms_sum_add.
Print Assumptions cms_sum_le.
Print Assumptions cms_fold_req_list_sum.
Print Assumptions cms_sum_eq_list.
Print Assumptions cms_bs_swap.
Print Assumptions cms_bs_abs.
Print Assumptions cms_bs_lpc.
