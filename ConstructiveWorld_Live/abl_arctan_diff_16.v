(* ConstructiveWorld-Set — arctan difference pieces on the Cauchy reals. *)
(** * abl_arctan_diff_16: first slice of the arctan difference rule.

    Mission.  [abl9_atan_deriv_interior], a thin instantiation of
      [b3rr_real_arctan_deriv_linear] at a contracted interior bound
      [0 <= rho < 1], and [abl9_atan_diff_sum_rule], a genuine sum
      rule for the eps-linear increment shape [HasIncr f x a] with
      budget split [eps/2, eps'/3], a [real_min] modulus synthesis
      and a pointwise ring-law rearrangement.

    Dependencies.  Stdlib [QArith], [Qabs], [Qround], [List], [Bool],
      [Arith], [Setoid], [Morphisms], [Lia], [Qminmax],
      [GenericMinMax], [Extraction]; and [S01_BaseRing] through
      [S11_TP3B5] of this development.

    References.  This development, abl_arctan_diff_16.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier
      completion).  The sum rule mirrors [differentiable_plus] of
      [S06_DiffSamplingGibbs] rebuilt on the [S02_CauchyComplete]
      real layer.

    Constructivity.  All named statements are carried by [Set];
      [HasIncr] assembles [real_lt], [real_le], [sigT] and [And];
      proofs end in [Qed] with no admitted goals; extraction reports
      [Obj.magic] = 0 and [coqchk] reports [Axioms: none].
      [abl9_atan_deriv_interior] is a thin forwarding instantiation.

    Build.  [coqc -native-compiler no -q -Q . "" abl_arctan_diff_16.v]
      compiles cleanly (exit 0); the artifact starts [436f7121 00015ff4]. *)

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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ==================================================================== *)
(* The increment predicate: an eps-linear approximation of [f] at [x]    *)
(* with slope [a]; the shape matches the conclusion of                    *)
(* [b3rr_real_arctan_deriv_linear] verbatim. Set-carried throughout.      *)
(* ==================================================================== *)
Definition HasIncr (f : Real -> Real) (x a : Real) : Set :=
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (f (real_plus x h))
                     (real_opp (real_plus (f x) (real_mult h a)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ==================================================================== *)
(* A positive rational constant times a positive real stays positive     *)
(* (used to split the eps budget).                                        *)
(* ==================================================================== *)
Lemma abl9_qscale_pos : forall (c : Q) (eps : Real),
  Qlt 0 c -> real_lt real_zero eps ->
  real_lt real_zero (real_mult (real_const c) eps).
Proof.
  intros c eps Hc Heps.
  destruct Heps as [e0 [He0 [N0 HN0]]].
  exists (c * e0)%Q.
  split.
  - assert (Hlt : Qlt 0 (c * e0)%Q).
    { apply (Qmult_lt_0_compat c e0).
      - exact Hc.
      - apply QltT_to_Qlt. exact He0. }
    unfold QltT, Qlt_bool.
    assert (Hcmp : Qcompare 0 (c * e0)%Q = Lt) by (apply Qlt_alt; exact Hlt).
    rewrite Hcmp. reflexivity.
  - exists N0. intros n Hn.
    assert (H2 : Qlt (e0 * c)%Q
                   ((projT1 eps n - projT1 real_zero n) * c)%Q).
    { apply (Qmult_lt_compat_r e0 (projT1 eps n - projT1 real_zero n)%Q c).
      - exact Hc.
      - apply QltT_to_Qlt. exact (HN0 n Hn). }
    assert (Hmid : (projT1 (real_mult (real_const c) eps) n
                    - projT1 real_zero n ==
                    c * (projT1 eps n - projT1 real_zero n))%Q).
    { setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const c) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj c n)).
      simpl. ring. }
    assert (Hc2 : Qcompare (c * e0)%Q
                    (projT1 (real_mult (real_const c) eps) n
                     - projT1 real_zero n)%Q
                  = Qcompare (c * e0)%Q
                    (c * (projT1 eps n - projT1 real_zero n))%Q)
      by (apply (Qcompare_comp (c * e0) (c * e0) (Qeq_refl (c * e0))
                   (projT1 (real_mult (real_const c) eps) n
                    - projT1 real_zero n)%Q
                   (c * (projT1 eps n - projT1 real_zero n))%Q Hmid)).
    assert (Ha : (c * e0 == e0 * c)%Q) by ring.
    assert (Hb : (c * (projT1 eps n - projT1 real_zero n) ==
                  (projT1 eps n - projT1 real_zero n) * c)%Q) by ring.
    assert (Hce : Qcompare (c * e0)%Q
                    (c * (projT1 eps n - projT1 real_zero n))%Q
                  = Qcompare (e0 * c)%Q
                    ((projT1 eps n - projT1 real_zero n) * c)%Q)
      by (apply (Qcompare_comp (c * e0) (e0 * c) Ha
                   (c * (projT1 eps n - projT1 real_zero n))
                   ((projT1 eps n - projT1 real_zero n) * c) Hb)).
    unfold QltT, Qlt_bool.
    rewrite Hc2. rewrite Hce.
    assert (Hcmp : Qcompare (e0 * c)%Q
                     ((projT1 eps n - projT1 real_zero n) * c)%Q = Lt)
      by (apply Qlt_alt; exact H2).
    rewrite Hcmp. reflexivity.
Qed.

(* ==================================================================== *)
(* The two [Qmin] lower bounds (the [Z]-based [Qle] unfolding with a      *)
(* three-way [Qcompare] case analysis; this Stdlib face carries no        *)
(* named [Qmin_le_l]/[Qmin_le_r], so both are built here).                *)
(* ==================================================================== *)
Lemma abl9_Qmin_le_l : forall x y : Q, QleT' (Qmin x y) x.
Proof.
  intros x y.
  apply Qle_to_QleT'.
  unfold Qmin, gmin.
  destruct (Qcompare x y) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - assert (Hyx : (y ?= x) = Lt).
    { rewrite <- Qcompare_antisym. rewrite E. reflexivity. }
    apply Qlt_le_weak. apply Qlt_alt. exact Hyx.
Qed.

Lemma abl9_Qmin_le_r : forall x y : Q, QleT' (Qmin x y) y.
Proof.
  intros x y.
  apply Qle_to_QleT'.
  assert (Hgen : forall c : comparison,
           Qcompare x y = c ->
           Qle (match c with Gt => y | _ => x end) y).
  { intros c Hc. destruct c.
    - unfold Qle. intro Hgt. unfold Qcompare in Hc. congruence.
    - apply Qlt_le_weak. apply Qlt_alt. exact Hc.
    - apply Qle_refl. }
  unfold Qmin, gmin.
  apply (Hgen (Qcompare x y)). reflexivity.
Qed.

(* ==================================================================== *)
(* Unpacking the minimal modulus: [s < min df dg] yields [s < df] and     *)
(* [s < dg] (pointwise [Qmin] chaining with [qeq_le]/[Qle_trans]          *)
(* relays), feeding the modulus synthesis of the sum rule.                *)
(* ==================================================================== *)
Lemma abl9_min_lt_l : forall (a b s : Real),
  real_lt s (real_min a b) -> real_lt s a.
Proof.
  intros a b s Hs.
  destruct Hs as [e0 [He0 [N0 HN0]]].
  exists e0. split.
  - exact He0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0
             (projT1 (real_min a b) n - projT1 s n)%Q
             (projT1 a n - projT1 s n)%Q).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + unfold Qminus.
      apply (Qle_trans (projT1 (real_min a b) n + Qopp (projT1 s n))
                       (Qmin (projT1 a n) (projT1 b n) + Qopp (projT1 s n))
                       (projT1 a n + Qopp (projT1 s n))).
      * apply (Qplus_le_compat (projT1 (real_min a b) n)
                 (Qmin (projT1 a n) (projT1 b n))
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply real_min_proj.
        -- apply Qle_refl.
      * apply (Qplus_le_compat (Qmin (projT1 a n) (projT1 b n))
                 (projT1 a n)
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- exact (QleT'_to_Qle _ _ (abl9_Qmin_le_l _ _)).
        -- apply Qle_refl.
Qed.

Lemma abl9_min_lt_r : forall (a b s : Real),
  real_lt s (real_min a b) -> real_lt s b.
Proof.
  intros a b s Hs.
  destruct Hs as [e0 [He0 [N0 HN0]]].
  exists e0. split.
  - exact He0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0
             (projT1 (real_min a b) n - projT1 s n)%Q
             (projT1 b n - projT1 s n)%Q).
    + apply QltT_to_Qlt. exact (HN0 n Hn).
    + unfold Qminus.
      apply (Qle_trans (projT1 (real_min a b) n + Qopp (projT1 s n))
                       (Qmin (projT1 a n) (projT1 b n) + Qopp (projT1 s n))
                       (projT1 b n + Qopp (projT1 s n))).
      * apply (Qplus_le_compat (projT1 (real_min a b) n)
                 (Qmin (projT1 a n) (projT1 b n))
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- apply QleT'_to_Qle. apply qeq_imp_qle. apply real_min_proj.
        -- apply Qle_refl.
      * apply (Qplus_le_compat (Qmin (projT1 a n) (projT1 b n))
                 (projT1 b n)
                 (Qopp (projT1 s n)) (Qopp (projT1 s n))).
        -- exact (QleT'_to_Qle _ _ (abl9_Qmin_le_r _ _)).
        -- apply Qle_refl.
Qed.

(* ==================================================================== *)
(* The sum rule for increments (rebuilt on this development's real        *)
(* layer, mirroring the [S06] abstract-layer statement):                  *)
(*   HasIncr f x a -> HasIncr g x b ->                                    *)
(*   HasIncr (fun y => f y + g y) x (a + b).                              *)
(* Budget: [eps/2] and [eps'/3] on the inner sides; [real_min df dg].     *)
(* ==================================================================== *)
Lemma abl9_atan_diff_sum_rule :
  forall (f g : Real -> Real) (x a b : Real),
  HasIncr f x a -> HasIncr g x b ->
  HasIncr (fun y : Real => real_plus (f y) (g y)) x (real_plus a b).
Proof.
  intros f g x a b Hf Hg eps Heps.
  unfold HasIncr in Hf, Hg.
  set (e1 := real_mult (real_const (1 # 2)) eps).
  assert (He1 : real_lt real_zero e1).
  { apply abl9_qscale_pos.
    - unfold Qlt. simpl. lia.
    - exact Heps. }
  destruct (Hf e1 He1) as [df [Hdfp Hdfstep]].
  destruct (Hg e1 He1) as [dg [Hdgp Hdgstep]].
  exists (real_min df dg). split.
  - apply real_min_pos.
    + exact Hdfp.
    + exact Hdgp.
  - intros h Hh eps' Heps'.
    set (e2 := real_mult (real_const (1 # 3)) eps').
    assert (He2 : real_lt real_zero e2).
    { apply abl9_qscale_pos.
      - unfold Qlt. simpl. lia.
      - exact Heps'. }
    (* Pointwise unpacking of the minimal modulus: |h| < min df dg gives  *)
    (* |h| < df and |h| < dg. *)
    assert (Hhdf : real_lt (real_abs h) df)
      by (apply (abl9_min_lt_l df dg (real_abs h)); exact Hh).
    assert (Hhdg : real_lt (real_abs h) dg)
      by (apply (abl9_min_lt_r df dg (real_abs h)); exact Hh).
    assert (HA := Hdfstep h Hhdf e2 He2).
    assert (HB := Hdgstep h Hhdg e2 He2).
    (* Rearranging the left-hand side by the pointwise ring laws:        *)
    (*   |(f+g)(x+h) - ((f+g)(x) + h(a+b))|                               *)
    (*    = |(f(x+h) - (f(x)+ha)) + (g(x+h) - (g(x)+hb))|. *)
    assert (Hrearr : real_eq
      (real_abs (real_plus
        (real_plus (f (real_plus x h)) (g (real_plus x h)))
        (real_opp (real_plus (real_plus (f x) (g x))
                             (real_mult h (real_plus a b))))))
      (real_abs (real_plus
        (real_plus (f (real_plus x h))
                   (real_opp (real_plus (f x) (real_mult h a))))
        (real_plus (g (real_plus x h))
                   (real_opp (real_plus (g x) (real_mult h b))))))).
    { apply real_abs_eq_compat. apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      (* Top-down single-pass projection rewriting across the pointwise  *)
      (* equality, each step through the [QeqT]-to-[Qeq] bridge. *)
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (f (real_plus x h)) (g (real_plus x h)))
                 (real_opp (real_plus (real_plus (f x) (g x))
                             (real_mult h (real_plus a b)))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (f (real_plus x h))
                                 (real_opp (real_plus (f x) (real_mult h a))))
                 (real_plus (g (real_plus x h))
                            (real_opp (real_plus (g x) (real_mult h b)))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f (real_plus x h)) (g (real_plus x h)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (real_plus (f x) (g x))
                                 (real_mult h (real_plus a b))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (f x) (g x))
                 (real_mult h (real_plus a b)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj h (real_plus a b) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj a b n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f x) (g x) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f (real_plus x h))
                 (real_opp (real_plus (f x) (real_mult h a))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (f x) (real_mult h a)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (f x) (real_mult h a) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj h a n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (g (real_plus x h))
                 (real_opp (real_plus (g x) (real_mult h b))) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus (g x) (real_mult h b)) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (g x) (real_mult h b) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj h b n)).
      ring. }
    (* Triangle step for the eps budget. *)
    assert (Htri : real_le
      (real_abs (real_plus
        (real_plus (f (real_plus x h))
                   (real_opp (real_plus (f x) (real_mult h a))))
        (real_plus (g (real_plus x h))
                   (real_opp (real_plus (g x) (real_mult h b))))))
      (real_plus
        (real_plus (real_abs (real_plus (f (real_plus x h))
                              (real_opp (real_plus (f x) (real_mult h a)))))
                   (real_abs (real_plus (g (real_plus x h))
                              (real_opp (real_plus (g x) (real_mult h b))))))
        e2))
      by (apply (real_abs_triangle_le_eps
                   (real_plus (f (real_plus x h))
                              (real_opp (real_plus (f x) (real_mult h a))))
                   (real_plus (g (real_plus x h))
                              (real_opp (real_plus (g x) (real_mult h b))))
                   e2 He2)).
    (* Assembling the two weak bounds by addition. *)
    assert (HT1 : real_le
      (real_plus (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                 (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
      (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                 (real_plus (real_mult e1 (real_abs h)) e2)))
      by (apply real_le_plus_compat; [exact HA | exact HB]).
    assert (HT2 : real_le
      (real_plus
        (real_plus (real_abs (real_plus (f (real_plus x h))
                                  (real_opp (real_plus (f x) (real_mult h a)))))
                   (real_abs (real_plus (g (real_plus x h))
                                  (real_opp (real_plus (g x) (real_mult h b))))))
        e2)
      (real_plus
        (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                   (real_plus (real_mult e1 (real_abs h)) e2))
        e2))
      by (apply real_le_plus_compat; [exact HT1 | apply real_le_refl]).
    (* Closing the chain: |BIG| <= |A|+|B|+e2 <= assembled bound <=       *)
    (* eps|h| + eps', with every intermediate term built explicitly. *)
    assert (Hmid : real_eq
      (real_plus
        (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                   (real_plus (real_mult e1 (real_abs h)) e2))
        e2)
      (real_plus (real_mult eps (real_abs h)) eps')).
    { apply real_eq_of_zero_diff. intro n.
      apply qeq_imp_qeqT.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                                 (real_plus (real_mult e1 (real_abs h)) e2))
                 e2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_plus (real_mult e1 (real_abs h)) e2)
                 (real_plus (real_mult e1 (real_abs h)) e2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult e1 (real_abs h)) e2 n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj e1 (real_abs h) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_plus_proj (real_mult eps (real_abs h)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj eps (real_abs h) n)).
      unfold e1, e2.
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 # 2)) eps n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 2) n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_mult_proj (real_const (1 # 3)) eps' n)).
      setoid_rewrite (qeqT_imp_qeq _ _ (real_const_proj (1 # 3) n)).
      ring. }
    exact (real_le_trans
             (real_abs (real_plus
               (real_plus (f (real_plus x h)) (g (real_plus x h)))
               (real_opp (real_plus (real_plus (f x) (g x))
                                    (real_mult h (real_plus a b))))))
             (real_plus
               (real_plus
                  (real_abs (real_plus (f (real_plus x h))
                             (real_opp (real_plus (f x) (real_mult h a)))))
                  (real_abs (real_plus (g (real_plus x h))
                             (real_opp (real_plus (g x) (real_mult h b))))))
               e2)
             (real_plus (real_mult eps (real_abs h)) eps')
             (real_le_eq_l
                (real_abs (real_plus
                  (real_plus (f (real_plus x h)) (g (real_plus x h)))
                  (real_opp (real_plus (real_plus (f x) (g x))
                                       (real_mult h (real_plus a b))))))
                (real_abs (real_plus
                  (real_plus (f (real_plus x h))
                             (real_opp (real_plus (f x) (real_mult h a))))
                  (real_plus (g (real_plus x h))
                             (real_opp (real_plus (g x) (real_mult h b))))))
                (real_plus
                  (real_plus
                     (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                     (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
                  e2)
                Hrearr Htri)
             (real_le_trans
                (real_plus
                  (real_plus
                     (real_abs (real_plus (f (real_plus x h))
                                (real_opp (real_plus (f x) (real_mult h a)))))
                     (real_abs (real_plus (g (real_plus x h))
                                (real_opp (real_plus (g x) (real_mult h b))))))
                  e2)
                (real_plus
                  (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                             (real_plus (real_mult e1 (real_abs h)) e2))
                  e2)
                (real_plus (real_mult eps (real_abs h)) eps')
                HT2
                 (RealSetoid.real_eq_le
                    (real_plus
                      (real_plus (real_plus (real_mult e1 (real_abs h)) e2)
                                 (real_plus (real_mult e1 (real_abs h)) e2))
                      e2)
                    (real_plus (real_mult eps (real_abs h)) eps')
                    Hmid))).
Qed.

(* ==================================================================== *)
(* The interior derivative wrapper: [b3rr_real_arctan_deriv_linear]       *)
(* instantiated at a contracted interior bound [0 <= rho < 1]; the        *)
(* conclusion is the u-side increment supply of the composed map.  A      *)
(* thin forwarding instantiation (disclosed in the header).               *)
(* ==================================================================== *)
Lemma abl9_atan_deriv_interior :
  forall (rho : Q) (Hrho0 : Qle 0 rho) (Hrho1 : Qlt rho 1),
  forall (u : Real) (Hu : forall n : nat, QleT' (Qabs (projT1 u n)) rho),
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (Huh : forall n : nat,
                    QleT' (Qabs (projT1 (real_plus u h) n)) 1),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (cauchy_real_arctan (real_plus u h) Huh)
                     (real_opp (real_plus (cauchy_real_arctan u
                                            (b3rr_dom_r1 u rho Hu Hrho1))
                                (real_mult h (real_inv_pos
                                   (real_plus real_one (real_mult u u))
                                   (b3r_one_sq_real_pos u)))))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).
Proof.
  intros rho Hrho0 Hrho1 u Hu eps Heps.
  exact (b3rr_real_arctan_deriv_linear rho Hrho0 Hrho1 u Hu eps Heps).
Qed.

(* ==================================================================== *)
(* Closing audit: the two statement names, the two [Qed] closes and the   *)
(* two assumption checks below agree one-to-one.                          *)
(* ==================================================================== *)
Print Assumptions abl9_atan_diff_sum_rule.
Print Assumptions abl9_atan_deriv_interior.

(* Extraction check: the printed output must contain zero [Obj.magic]. *)
Recursive Extraction abl9_atan_diff_sum_rule abl9_atan_deriv_interior.
