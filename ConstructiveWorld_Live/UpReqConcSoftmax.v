(* ConstructiveWorld-Set — absolute-value bounds over the concrete softmax summation interface. *)

(** * UpReqConcSoftmax: absolute-value bounds over the summation
       interface of the concrete softmax.

    Mission.  The [csm_sumf] definition and the summation-interface
    members [csm_sum_eq_list]/[csm_sum_ext]/[csm_sum_linear]/
    [csm_sum_add]/[csm_sum_le]; the triangle chain [csm_abs_pointwise],
    [csm_abs_list_le_eps], [csm_abs_pair_tri_eps], and the main member
    [csm_abs_sum_le_eps].

    Dependencies.  Stdlib [List], [QArith.QArith], [QArith.Qabs],
    [Setoid], [Morphisms], [Lia].  Requires [S01_BaseRing] through
    [S15_TailFEPUp], [UpReqAlgebra], [UpReqSumD] of this development;
    [CW_ConstructiveWorld_219] read-only.

    References.  This development, UpReqConcSoftmax.v, the baseline
    module in ConstructiveWorld-Main whose statement names are carried
    over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].  Every member [Qed]-closed, zero
      admitted statements, no classical logic; the statement face is
      Set-carried with zero Prop leakage.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqConcSoftmax.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Open Scope Q_scope.
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
Import RealInterfaceEnhancedMod.

(* Derivation provenance: the softmax-summation-interface version of the
   finite-sum absolute-value inequality. *)

(* ============ The folding machinery and the five-slot delegation
   (Cauchy Real layer) ============ *)

Section CsmSumOver.

Variable S : Set.
Variable enum : list S.

(* The concrete finite-sum operator: folding over the enum list (a
   self-contained isomorphic form of the sumd_sumf prescription). *)
Definition csm_sumf (f : S -> Real) : Real := sumd_list_sum S f enum.

(* Grade C: the key bridge (the folding prescription is definitionally the
   list sum, grounded by req_refl; same shape as sumd_sum_eq_list). *)
Lemma csm_sum_eq_list : forall g : S -> Real,
  real_eq (csm_sumf g) (sumd_list_sum S g enum).
Proof. intro g. exact (req_refl (sumd_list_sum S g enum)). Qed.

(* Grade B: the extensionality slot (delegated to sumd_sum_ext; the
   csm_sumf folding prescription is convertible). *)
Lemma csm_sum_ext : forall f g : S -> Real,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (csm_sumf f) (csm_sumf g).
Proof.
  intros f g H.
  unfold csm_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* Grade B: the scalar-multiplication linearity slot (delegated to
   sumd_sum_linear). *)
Lemma csm_sum_linear : forall (a : Real) (f : S -> Real),
  real_eq (csm_sumf (fun s : S => mult a (f s))) (mult a (csm_sumf f)).
Proof.
  intros a f.
  unfold csm_sumf.
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

(* Grade B: the additivity slot (delegated to sumd_sum_add). *)
Lemma csm_sum_add : forall f g : S -> Real,
  real_eq (csm_sumf (fun s : S => plus (f s) (g s)))
      (plus (csm_sumf f) (csm_sumf g)).
Proof.
  intros f g.
  unfold csm_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - exact (req_trans
             (plus (plus (f x) (g x))
                   (sumd_list_sum S (fun s : S => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                   (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))
             (plus (plus (f x) (sumd_list_sum S f t))
                   (plus (g x) (sumd_list_sum S g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)
                (plus (sumd_list_sum S f t) (sumd_list_sum S g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_plus_exchange (f x) (sumd_list_sum S f t)
                (g x) (sumd_list_sum S g t))).
Qed.

(* Grade B: the monotonicity slot (delegated to sumd_sum_le). *)
Lemma csm_sum_le : forall f g : S -> Real,
  (forall s : S, real_le (f s) (g s)) -> real_le (csm_sumf f) (csm_sumf g).
Proof.
  intros f g H.
  unfold csm_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* Grade B: the nonnegativity slot (supplied directly in folding form by
   sumd_list_sum_nonneg). *)
Lemma csm_sum_zero_nonneg : forall f : S -> Real,
  (forall s : S, real_le zero (f s)) -> real_le zero (csm_sumf f).
Proof.
  intros f H.
  unfold csm_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero)
             (plus (f x) (sumd_list_sum S f t))
             (req_sym (plus zero zero) zero (plus_zero zero))
             (le_plus_compat zero (f x) zero (sumd_list_sum S f t)
                (H x) IH)).
Qed.

(* ============ Grade A: the triangle core members (the increment of this
   file) ============ *)

(* — Route A pointwise machinery (fully transparent repr lemmas for
   real_plus/real_abs/real_zero) — *)

Lemma csm_repr_plus : forall (A B : Real) (n : nat),
  projT1 (real_plus A B) n == projT1 A n + projT1 B n.
Proof. intros A B n. destruct A as [u Hu]. destruct B as [v Hv]. reflexivity. Qed.

Lemma csm_repr_abs : forall (A : Real) (n : nat),
  projT1 (real_abs A) n == Qabs (projT1 A n).
Proof. intros A n. destruct A as [u Hu]. reflexivity. Qed.

Lemma csm_repr_zero : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intro n. cbv [projT1 real_zero]. exact (Qeq_refl 0%Q). Qed.

(* Pointwise triangle: Qabs(sum f)(n) <= (sum |f|)(n) (purely at the Q
   layer, holding for every n). *)
Lemma csm_abs_pointwise : forall (l : list S) (f : S -> Real) (n : nat),
  Qle (Qabs (projT1 (sumd_list_sum S f l) n))
      (projT1 (sumd_list_sum S (fun s : S => real_abs (f s)) l) n).
Proof.
  intro l. induction l as [| x t IH]; intros f n.
  - change (Qle (Qabs (projT1 real_zero n)) (projT1 real_zero n)).
    rewrite csm_repr_zero.
    change (Qle 0%Q 0%Q).
    apply Qle_refl.
  - change (Qle (Qabs (projT1 (real_plus (f x) (sumd_list_sum S f t)) n))
                (projT1 (real_plus (real_abs (f x))
                            (sumd_list_sum S (fun s : S => real_abs (f s)) t))
                     n)).
    rewrite (csm_repr_plus (f x) (sumd_list_sum S f t) n).
    rewrite (csm_repr_plus (real_abs (f x))
              (sumd_list_sum S (fun s : S => real_abs (f s)) t) n).
    rewrite (csm_repr_abs (f x) n).
    eapply Qle_trans.
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * exact (IH f n).
Qed.

(* List level: |sum_l f| < (sum_l |f|) + eps (0 < eps; combined at the
   real_lt level with a pointwise eps margin). *)
Lemma csm_abs_list_le_eps : forall (l : list S) (f : S -> Real) (eps : Real),
  real_lt zero eps ->
  real_le (abs (sumd_list_sum S f l))
     (plus (sumd_list_sum S (fun s : S => abs (f s)) l) eps).
Proof.
  intros l f eps Heps.
  change (real_lt real_zero eps) in Heps.
  destruct Heps as [e0 [He0 [N0 HN0]]].
  change (real_le (real_abs (sumd_list_sum S f l))
                  (real_plus (sumd_list_sum S (fun s => real_abs (f s)) l) eps)).
  apply inl.
  refine (existT _ e0 _).
  split.
  - exact He0.
  - refine (existT _ N0 _).
    intros n Hn.
    assert (Hpt := csm_abs_pointwise l f n).
    remember (sumd_list_sum S (fun s => real_abs (f s)) l) as wa eqn:Hwa_def.
    remember (sumd_list_sum S f l) as uf eqn:Huf.
    destruct wa as [wb Hwb].
    destruct uf as [u Hu].
    destruct eps as [we Hwe].
    change (Qle (Qabs (u n)) (wb n)) in Hpt.
    change (QltT e0 (wb n + we n - Qabs (u n))).
    assert (H0D : Qle 0 (wb n - Qabs (u n))).
    { exact (proj1 (Qle_minus_iff (Qabs (u n)) (wb n)) Hpt). }
    apply Qlt_to_QltT.
    assert (Hltw : e0 < we n - 0) by (apply QltT_to_Qlt; exact (HN0 n Hn)).
    remember (Qabs (u n)) as qa eqn:Hqa.
    assert (HR : wb n + we n - qa == (wb n - qa) + (we n - 0)).
    { ring. }
    rewrite HR.
    apply (Qlt_le_trans e0 (we n - 0)).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + assert (HT1 : we n - 0 <= 0 + (we n - 0)).
      { exact (proj1 (@Qle_comp (0 + (we n - 0)) (we n - 0)
                        (Qplus_0_l (we n - 0))
                        (0 + (we n - 0)) (0 + (we n - 0)) (Qeq_refl _))
               (Qle_refl (0 + (we n - 0)))). }
      exact (Qle_trans _ _ _ HT1
               (Qplus_le_compat 0%Q (wb n - qa) (we n - 0) (we n - 0)
                  H0D (Qle_refl (we n - 0)))).
Qed.

(* Pairwise triangle (Bishop per-eps form): |x+y| <= |x| + |y| + eps
   (0 < eps).  Metric substitution method: the certificate machine
   real_metric_triangle_eps (x+y) x zero eps directly supplies
   le (|(x+y) - zero|) (|(x+y) - x| + |x - zero| + eps); the metric form
   is then carried slot by slot along req to the abs form
   (|a - zero| == |a|, |(x+y) - x| == |y|, and rearranged addition). *)
Lemma csm_abs_pair_tri_eps : forall x y eps : Real,
  real_lt zero eps ->
  real_le (abs (plus x y)) (plus (abs x) (plus (abs y) eps)).
Proof.
  intros x y eps Heps.
  assert (HMT : real_le (real_metric (plus x y) zero)
                   (plus (plus (real_metric (plus x y) x)
                               (real_metric x zero))
                         eps)).
  { exact (RealSetoid.real_metric_triangle_eps (plus x y) x zero eps Heps). }
  assert (Hopp0 : real_eq (opp zero) zero).
  { exact (req_trans (opp zero) (plus zero (opp zero)) zero
             (req_sym (plus zero (opp zero)) (opp zero)
               (req_plus_zero_l (opp zero)))
             (plus_opp zero)). }
  assert (Hmz : forall a : Real, real_eq (real_metric a zero) (abs a)).
  { intro a. exact (req_abs_compat (plus a (opp zero)) a
             (req_trans (plus a (opp zero)) (plus a zero) a
               (req_plus_compat a a (opp zero) zero (req_refl a) Hopp0)
               (plus_zero a))). }
  assert (Hmy : real_eq (real_metric (plus x y) x) (abs y)).
  { change (real_eq (abs (plus (plus x y) (opp x))) (abs y)).
    apply (req_abs_compat (plus (plus x y) (opp x)) y).
    apply (req_trans _ (plus x (plus (opp x) y))).
    - apply (req_trans _ (plus x (plus y (opp x)))).
      + exact (req_sym (plus x (plus y (opp x))) (plus (plus x y) (opp x))
                 (plus_assoc x y (opp x))).
      + exact (req_plus_compat x x (plus y (opp x)) (plus (opp x) y)
                 (req_refl x) (plus_comm y (opp x))).
    - apply (req_trans _ (plus (plus x (opp x)) y)).
      + exact (plus_assoc x (opp x) y).
      + exact (req_trans (plus (plus x (opp x)) y) (plus zero y) y
                 (req_plus_compat (plus x (opp x)) zero y y
                   (plus_opp x) (req_refl y))
                 (req_plus_zero_l y)). }
  assert (Htail1 : real_eq (plus (plus (real_metric (plus x y) x)
                                    (real_metric x zero))
                             eps)
                       (plus (plus (abs y) (abs x)) eps)).
  { exact (req_plus_compat (plus (real_metric (plus x y) x) (real_metric x zero))
             (plus (abs y) (abs x)) eps eps
             (req_plus_compat (real_metric (plus x y) x) (abs y)
                (real_metric x zero) (abs x) Hmy (Hmz x))
             (req_refl eps)). }
  assert (Htail3 : real_eq (plus (abs y) (plus (abs x) eps))
                       (plus (abs x) (plus (abs y) eps))).
  { exact (req_trans (plus (abs y) (plus (abs x) eps))
             (plus (plus (abs y) (abs x)) eps)
             (plus (abs x) (plus (abs y) eps))
             (plus_assoc (abs y) (abs x) eps)
             (req_trans (plus (plus (abs y) (abs x)) eps)
               (plus (plus (abs x) (abs y)) eps)
               (plus (abs x) (plus (abs y) eps))
               (req_plus_compat (plus (abs y) (abs x)) (plus (abs x) (abs y))
                 eps eps (plus_comm (abs y) (abs x)) (req_refl eps))
               (req_sym (plus (abs x) (plus (abs y) eps))
                 (plus (plus (abs x) (abs y)) eps)
                 (plus_assoc (abs x) (abs y) eps)))). }
  apply (le_trans _ (real_metric (plus x y) zero)).
  - exact (le_id_r _ _ _ (req_sym _ _ (Hmz (plus x y)))
             (le_refl (abs (plus x y)))).
  - exact (le_trans _ _ _ HMT
             (le_id_l _ _ _ Htail1
               (le_id_l _ _ _
                 (req_sym (plus (abs y) (plus (abs x) eps))
                   (plus (plus (abs y) (abs x)) eps)
                   (plus_assoc (abs y) (abs x) eps))
                 (le_id_r _ _ _ Htail3
                    (le_refl (plus (abs y) (plus (abs x) eps))))))).
Qed.

(* Main member: the per-eps triangle for the csm_sumf prescription (direct
   supply of the eps form of the abs_sum_le slot of the corresponding rsq
   copy). *)
Definition csm_abs_sum_le_eps : forall (f : S -> Real) (eps : Real),
  real_lt zero eps ->
  real_le (abs (csm_sumf f)) (plus (csm_sumf (fun s : S => abs (f s))) eps)
  := fun f eps Heps => csm_abs_list_le_eps enum f eps Heps.

End CsmSumOver.

(* ============ Assumption-face evidence: the new members have zero external unproven
   assumptions (all Closed, premises = explicit arguments) ============ *)
Print Assumptions csm_sum_eq_list.
Print Assumptions csm_sum_ext.
Print Assumptions csm_sum_linear.
Print Assumptions csm_sum_add.
Print Assumptions csm_sum_le.
Print Assumptions csm_sum_zero_nonneg.
Print Assumptions csm_abs_pair_tri_eps.
Print Assumptions csm_abs_list_le_eps.
Print Assumptions csm_abs_sum_le_eps.
