(* ConstructiveWorld-Set — Bishop-style order instantiation of the Gibbs family and a finite route to the Gibbs equality condition. *)

(** * UpReqGibbsE2: Bishop-order Gibbs family and finite equality condition.

    Mission.  (1) The Bishop-style order ([real_le_b]) instantiation of
      the Gibbs inequality family: order algebra primitives, the
      pointwise Gibbs tangent, KL non-negativity, and the cross-entropy
      decomposition (pointwise identity [H(p,q) == S[p] + KL(p||q)]).
      (2) A finite concrete route to the Gibbs equality condition:
      rational halving helpers and the antisymmetry core
      [gibbe2_le_b_antisym].

    Dependencies.  Stdlib [QArith], [Lia], [List].  Requires
      [S01_BaseRing] through [S15_TailFEPUp] and [UpRealLeB] of this
      development.

    References.  [UpReqGibbsE2] in ConstructiveWorld-Main, the baseline
      module whose statement names are carried over verbatim.  The
      premise [dist_log_le_linear] (standing premise of [UpReqDist])
      is discharged at its use site by [real_log_le_linear_B] of
      [UpRealLeB].

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id]); no
      classical axioms; the equality condition goes through finite
      eps witnesses; statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -Q . "" UpReqGibbsE2.v];
      artifact magic [436f7121 00015ff4]. *)

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
Require Import UpRealLeB.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 1. Bishop order algebra primitives (opp, scalar multiple and transfer on real_le_b). *)
(* ============================================================ *)

(* A1. Shift of the right end of lt from -eps to +eps (foundation for the opp reversal lemma). *)
Lemma gibbsd_lt_add_opp_r : forall x y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus x (real_opp e)) y ->
  real_lt x (real_plus y e).
Proof.
  intros x y e Heps Hlt.
  apply (RealSetoid.real_lt_compat
           (real_plus e (real_plus x (real_opp e))) x
           (real_plus e y) (real_plus y e)).
  - apply real_eq_sym.
    apply (real_eq_trans x (real_plus x (real_plus (real_opp e) e))
                         (real_plus e (real_plus x (real_opp e)))).
    + apply (real_eq_trans x (real_plus x real_zero)
                           (real_plus x (real_plus (real_opp e) e))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat x real_zero x
                 (real_plus (real_opp e) e)).
        -- apply real_eq_refl.
        -- apply (real_eq_trans real_zero (real_plus e (real_opp e))
                     (real_plus (real_opp e) e)).
           ++ apply real_eq_sym. apply real_plus_opp.
           ++ apply real_plus_comm.
    + apply (real_eq_trans (real_plus x (real_plus (real_opp e) e))
                           (real_plus (real_plus x (real_opp e)) e)
                           (real_plus e (real_plus x (real_opp e)))).
      * apply real_plus_assoc.
      * apply real_plus_comm.
  - apply real_plus_comm.
  - exact (real_lt_plus_translate e (real_plus x (real_opp e)) y Hlt).
Qed.

(* A2. Bishop order reversal under opp (the real_le_b counterpart of opp_le_compat at the req layer). *)
Lemma gibbsd_le_b_opp : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply gibbsd_lt_add_opp_r.
  - exact Heps.
  - apply (RealSetoid.real_lt_compat
             (real_opp (real_plus b eps))
             (real_plus (real_opp b) (real_opp eps))
             (real_opp a) (real_opp a)).
    + exact (real_opp_plus b eps).
    + apply real_eq_refl.
    + exact (real_opp_lt_compat a (real_plus b eps) (H eps Heps)).
Qed.

(* A3. Replacement of the left end of the Bishop order by a real_eq identity (the real_le_b counterpart of le_id_l at the req layer). *)
Lemma gibbsd_le_b_id_l : forall a b c : Real,
  real_eq a b -> real_le_b b c -> real_le_b a c.
Proof.
  intros a b c Hab H eps Heps. unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat b a (real_plus c eps) (real_plus c eps)
           (real_eq_sym a b Hab) (real_eq_refl (real_plus c eps))
           (H eps Heps)).
Qed.

(* A5. Minus flip identity: -(a - b) == b - a (the counterpart of reqd_minus_one_flip at the req layer). *)
Lemma gibbsd_minus_flip : forall a b : Real,
  real_eq (real_opp (real_plus a (real_opp b)))
          (real_plus b (real_opp a)).
Proof.
  intros a b.
  apply (real_eq_trans (real_opp (real_plus a (real_opp b)))
                       (real_plus (real_opp a) (real_opp (real_opp b)))
                       (real_plus b (real_opp a))).
  - exact (real_opp_plus a (real_opp b)).
  - apply (real_eq_trans (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus (real_opp (real_opp b)) (real_opp a))
             (real_plus b (real_opp a))).
    + apply real_plus_comm.
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp (real_opp b)) (real_opp a)
               b (real_opp a)
               (real_opp_opp b) (real_eq_refl (real_opp a))).
Qed.

(* A4. Bishop order preserved under right multiplication by a positive scalar (the real_le_b counterpart of req_le_mult_compat_r at the req layer). *)
Lemma gibbsd_le_b_mult_pos_r : forall c a b : Real,
  real_lt real_zero c -> real_le_b a b ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc H eps Heps. unfold real_le_b in H.
  set (e0 := real_mult eps (real_inv_pos c Hc)).
  assert (Hpos0 : real_lt real_zero e0).
  { exact (real_mult_positive eps (real_inv_pos c Hc) Heps
             (real_inv_pos_pos c Hc)). }
  apply (RealSetoid.real_lt_compat
           (real_mult c a) (real_mult c a)
           (real_mult c (real_plus b e0))
           (real_plus (real_mult c b) eps)).
  - apply real_eq_refl.
  - apply (real_eq_trans
             (real_mult c (real_plus b e0))
             (real_plus (real_mult c b) (real_mult c e0))
             (real_plus (real_mult c b) eps)).
    + exact (real_distrib c b e0).
    + exact (RealSetoid.real_eq_plus_compat (real_mult c b) (real_mult c e0)
               (real_mult c b) eps
               (real_eq_refl (real_mult c b))
               (real_eq_trans
                  (real_mult c e0)
                  (real_mult eps (real_mult c (real_inv_pos c Hc))) eps
                  (real_eq_trans
                     (real_mult c e0)
                     (real_mult (real_mult eps c) (real_inv_pos c Hc))
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_eq_trans
                        (real_mult c e0)
                        (real_mult (real_mult c eps) (real_inv_pos c Hc))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc c eps (real_inv_pos c Hc))
                        (RealSetoid.real_eq_mult_compat
                           (real_mult c eps) (real_inv_pos c Hc)
                           (real_mult eps c) (real_inv_pos c Hc)
                           (real_mult_comm c eps)
                           (real_eq_refl (real_inv_pos c Hc))))
                     (real_eq_sym
                        (real_mult eps (real_mult c (real_inv_pos c Hc)))
                        (real_mult (real_mult eps c) (real_inv_pos c Hc))
                        (real_mult_assoc eps c (real_inv_pos c Hc))))
                  (real_eq_trans
                     (real_mult eps (real_mult c (real_inv_pos c Hc)))
                     (real_mult eps real_one) eps
                     (RealSetoid.real_eq_mult_compat eps
                        (real_mult c (real_inv_pos c Hc)) eps real_one
                        (real_eq_refl eps) (real_inv_pos_correct c Hc))
                     (real_mult_one eps)))).
  - exact (real_mult_lt_compat_l a (real_plus b e0) c (H e0 Hpos0) Hc).
Qed.

(* ============================================================ *)
(* Part 2. Pointwise identities preceding the premise discharge (equality layer). *)
(* ============================================================ *)

(* B0. p * (q / p) == q (fraction cancellation via associativity, commutativity and the inv_correct chain). *)
Lemma gibbsd_p_mult_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_mult q (real_inv_pos p Hp)))
           (real_mult q (real_mult p (real_inv_pos p Hp))) q).
  - apply (real_eq_trans
             (real_mult p (real_mult q (real_inv_pos p Hp)))
             (real_mult (real_mult p q) (real_inv_pos p Hp))
             (real_mult q (real_mult p (real_inv_pos p Hp)))).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans
               (real_mult (real_mult p q) (real_inv_pos p Hp))
               (real_mult (real_mult q p) (real_inv_pos p Hp))
               (real_mult q (real_mult p (real_inv_pos p Hp)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q)
                 (real_inv_pos p Hp) (real_mult q p) (real_inv_pos p Hp)
                 (real_mult_comm p q) (real_eq_refl (real_inv_pos p Hp))).
      * apply real_eq_sym.
        exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans
             (real_mult q (real_mult p (real_inv_pos p Hp)))
             (real_mult q real_one) q).
    + apply (RealSetoid.real_eq_mult_compat q
               (real_mult p (real_inv_pos p Hp)) q real_one
               (real_eq_refl q) (real_inv_pos_correct p Hp)).
    + exact (real_mult_one q).
Qed.

(* B1. p * (1 - q / p) == p - q (the Real counterpart of reqd_p_minus_ratio at the req layer). *)
Lemma gibbsd_p_minus_ratio : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_plus real_one
                         (real_opp (real_mult q (real_inv_pos p Hp)))))
          (real_plus p (real_opp q)).
Proof.
  intros p q Hp.
  apply (real_eq_trans
           (real_mult p (real_plus real_one
                      (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus (real_mult p real_one)
                      (real_mult p (real_opp (real_mult q (real_inv_pos p Hp)))))
           (real_plus p (real_opp q))).
  - exact (real_distrib p real_one
             (real_opp (real_mult q (real_inv_pos p Hp)))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult p real_one)
             (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
             p (real_opp q)).
    + exact (real_mult_one p).
    + apply (real_eq_trans
               (real_mult p (real_opp (real_mult q (real_inv_pos p Hp))))
               (real_opp (real_mult p (real_mult q (real_inv_pos p Hp))))
               (real_opp q)).
      * apply real_eq_sym.
        exact (real_opp_mult p (real_mult q (real_inv_pos p Hp))).
      * apply (RealSetoid.real_eq_opp_compat
                 (real_mult p (real_mult q (real_inv_pos p Hp))) q
                 (gibbsd_p_mult_ratio p q Hp)).
Qed.

(* ============================================================ *)
(* Part 3. Bishop summation layer (lifting pointwise facts to sums over real_list_sum). *)
(* ============================================================ *)

Lemma gibbsd_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.

Definition gibbsd_half : Real :=
  real_inv_pos (real_plus real_one real_one) gibbsd_two_pos.

Lemma gibbsd_half_pos : real_lt real_zero gibbsd_half.
Proof.
  exact (real_inv_pos_pos (real_plus real_one real_one) gibbsd_two_pos).
Qed.

(* Half-distribution: e * h + e * h == e (the identity under halving eps). *)
Lemma gibbsd_half_sum : forall e : Real,
  real_eq (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half)) e.
Proof.
  intro e.
  apply (real_eq_trans
           (real_plus (real_mult e gibbsd_half) (real_mult e gibbsd_half))
           (real_mult e (real_plus gibbsd_half gibbsd_half)) e).
  - apply real_eq_sym.
    exact (real_distrib e gibbsd_half gibbsd_half).
  - apply (real_eq_trans
             (real_mult e (real_plus gibbsd_half gibbsd_half))
             (real_mult e real_one) e).
    + apply (RealSetoid.real_eq_mult_compat e
               (real_plus gibbsd_half gibbsd_half) e real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans (real_plus gibbsd_half gibbsd_half)
                 (real_mult (real_plus real_one real_one) gibbsd_half)
                 real_one).
        -- apply real_eq_sym.
           apply (real_eq_trans
                    (real_mult (real_plus real_one real_one) gibbsd_half)
                    (real_plus (real_mult real_one gibbsd_half)
                               (real_mult real_one gibbsd_half))
                    (real_plus gibbsd_half gibbsd_half)).
           ++ exact (real_eq_sym
                       (real_plus (real_mult real_one gibbsd_half)
                                  (real_mult real_one gibbsd_half))
                       (real_mult (real_plus real_one real_one) gibbsd_half)
                       (real_distrib_r_local real_one real_one gibbsd_half)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult real_one gibbsd_half)
                       (real_mult real_one gibbsd_half)
                       gibbsd_half gibbsd_half).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
              ** exact (real_eq_trans (real_mult real_one gibbsd_half)
                          (real_mult gibbsd_half real_one) gibbsd_half
                          (real_mult_comm real_one gibbsd_half)
                          (real_mult_one gibbsd_half)).
        -- exact (real_inv_pos_correct (real_plus real_one real_one)
                    gibbsd_two_pos).
    + exact (real_mult_one e).
Qed.

(* C3. Pointwise le_b implies summed le_b (the Bishop counterpart of
   fsum_le at the req layer; the induction halves eps into e/2 + e/2
   and the nil remainder uses real_lt_plus_r_zero). *)
Lemma gibbsd_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall s : X, real_le_b (f s) (g s)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l Hpt.
  unfold real_le_b.
  induction l as [| w l IH].
  - intros eps Heps. simpl.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - intros eps Heps. simpl.
    assert (Hpos : real_lt real_zero (real_mult eps gibbsd_half)).
    { exact (real_mult_positive eps gibbsd_half Heps gibbsd_half_pos). }
    assert (Ha : real_lt (f w)
                   (real_plus (g w) (real_mult eps gibbsd_half))).
    { exact (Hpt w (real_mult eps gibbsd_half) Hpos). }
    assert (Ht : real_lt (real_list_sum X f l)
                   (real_plus (real_list_sum X g l)
                              (real_mult eps gibbsd_half))).
    { exact (IH (real_mult eps gibbsd_half) Hpos). }
    apply (RealSetoid.real_lt_compat
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (f w) (real_list_sum X f l))
             (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                        (real_plus (real_list_sum X g l)
                                   (real_mult eps gibbsd_half)))
             (real_plus (real_plus (g w) (real_list_sum X g l)) eps)).
    + apply real_eq_refl.
    + exact (real_eq_trans
               (real_plus (real_plus (g w) (real_mult eps gibbsd_half))
                          (real_plus (real_list_sum X g l)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l))
                          (real_plus (real_mult eps gibbsd_half)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (g w) (real_list_sum X g l)) eps)
               (real_plus_swap_mid (g w) (real_mult eps gibbsd_half)
                                   (real_list_sum X g l)
                                   (real_mult eps gibbsd_half))
               (RealSetoid.real_eq_plus_compat
                  (real_plus (g w) (real_list_sum X g l))
                  (real_plus (real_mult eps gibbsd_half)
                             (real_mult eps gibbsd_half))
                  (real_plus (g w) (real_list_sum X g l))
                  eps
                  (real_eq_refl (real_plus (g w) (real_list_sum X g l)))
                  (gibbsd_half_sum eps))).
    + exact (real_lt_plus_compat _ _ _ _ Ha Ht).
Qed.

(* C4. The sum of (p - q) equals the difference of the sums (the Real counterpart of fsum_minus at the req layer). *)
Lemma gibbsd_list_sum_minus : forall (X : Type) (p q : X -> Real) (l : list X),
  real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
          (real_plus (real_list_sum X p l)
                     (real_opp (real_list_sum X q l))).
Proof.
  intros X p q l.
  apply (real_eq_trans
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_plus (real_list_sum X p l)
                      (real_list_sum X (fun s => real_opp (q s)) l))
           (real_plus (real_list_sum X p l)
                      (real_opp (real_list_sum X q l)))).
  - exact (real_list_sum_add X p (fun s => real_opp (q s)) l).
  - apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
             (real_list_sum X (fun s => real_opp (q s)) l)
             (real_list_sum X p l)
             (real_opp (real_list_sum X q l))).
    + apply real_eq_refl.
    + exact (real_list_sum_opp X q l).
Qed.

(* ============================================================ *)
(* Part 4. Pointwise resolution main body. *)
(* ============================================================ *)

(* D0 (premise discharge at the premise slot): the pointwise
   Gibbs tangent p - q <=_B p * (-log(q/p)).  The standing premise
   [dist_log_le_linear] (ten downstream
   consumers) is discharged here unconditionally by one explicit
   application of real_log_le_linear_B (UpRealLeB).  Chain:
   log(q/p) <=_B q/p - 1 at the use site, reversal by opp,
   transfer to 1 - q/p, order preserved under left multiplication
   by p, closed by the transfer p * (1 - q/p) == p - q. *)
Lemma gibbsd_gibbs_pointwise_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b (real_plus (p s) (real_opp (q s)))
            (real_kl_term (p s) (q s) Hps Hqs).
Proof.
  intros X p q s Hps Hqs.
  unfold real_kl_term, real_le_b. intros eps Heps.
  set (Rqp := real_mult (q s) (real_inv_pos (p s) Hps)).
  set (Hr := real_mult_positive (q s) (real_inv_pos (p s) Hps) Hqs
               (real_inv_pos_pos (p s) Hps)).
  (* Premise discharge at the premise slot: explicit application of the direct-form engine at the dist_log_le_linear use site. *)
  assert (Hlin : real_le_b (real_log Rqp Hr)
                           (real_plus Rqp (real_opp real_one))).
  { exact (real_log_le_linear_B Rqp Hr). }
  assert (Hstep2 : real_le_b (real_plus real_one (real_opp Rqp))
                             (real_opp (real_log Rqp Hr))).
  { exact (gibbsd_le_b_id_l _ _ _
             (real_eq_sym _ _ (gibbsd_minus_flip Rqp real_one))
             (gibbsd_le_b_opp _ _ Hlin)). }
  assert (Hstep3 : real_le_b
                     (real_mult (p s)
                        (real_plus real_one (real_opp Rqp)))
                     (real_mult (p s) (real_opp (real_log Rqp Hr)))).
  { exact (gibbsd_le_b_mult_pos_r (p s) _ _ Hps Hstep2). }
  exact (gibbsd_le_b_id_l _ _ _
           (real_eq_sym _ _ (gibbsd_p_minus_ratio (p s) (q s) Hps))
           Hstep3 eps Heps).
Qed.

(* D1 (main lemma): Real instantiation of the Gibbs inequality,
   0 <=_B the sum of KL(p s || q s) over s.  This resolves the Real
   instantiation of req_gibbs_inequality (UpReqDist; the premise
   dist_log_le_linear carries ten downstream consumers): the
   normalization premises mirror the req layer in real_eq form, the
   summation layer runs on the real_list_sum machine with order
   real_le_b, and the premise slot is filled by the pointwise lemma D0.
   The statement has the same shape as E.13 real_gibbs_inequality_B:
   E.13 takes the eps completion route while this lemma replays the
   log-tangent premise discharge, so the two routes cross-check. *)
Theorem gibbsd_gibbs_inequality :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (Hnormp : real_eq (real_list_sum X p l) real_one)
    (Hnormq : real_eq (real_list_sum X q l) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Proof.
  intros X l p q Hp Hq Hnormp Hnormq.
  assert (Hle : real_le_b
                  (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                  (real_list_sum X
                     (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
  { apply gibbsd_list_sum_le_b.
    intro s. exact (gibbsd_gibbs_pointwise_B X p q s (Hp s) (Hq s)). }
  assert (Hz : real_eq
                 (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
                 real_zero).
  { apply (real_eq_trans
             (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
             (real_plus (real_list_sum X p l)
                        (real_opp (real_list_sum X q l)))
             real_zero).
    - exact (gibbsd_list_sum_minus X p q l).
    - apply (real_eq_trans
               (real_plus (real_list_sum X p l)
                          (real_opp (real_list_sum X q l)))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p l)
                 (real_opp (real_list_sum X q l)) real_one
                 (real_opp real_one)).
        * exact Hnormp.
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X q l) real_one
                   Hnormq).
      + exact (real_plus_opp real_one).
  }
  exact (gibbsd_le_b_id_l real_zero
           (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) l)
           (real_list_sum X
              (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)
           (real_eq_sym _ _ Hz) Hle).
Qed.

(* ============================================================ *)
(* Part 5. Main lemma: the first cascade layer cross_entropy_decomp
   resolved the same way (Real instantiation counterpart of
   req_cross_entropy_decomp at UpReqDist; the pointwise identity
   closes toward q == p * (q / p) through the multiplicative
   decomposition of the log, with no log inverse eliminated). *)
(* ============================================================ *)

Theorem gibbsd_cross_entropy_decomp :
  forall (X : Type) (l : list X) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s)),
  real_eq
    (real_list_sum X
       (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
    (real_plus
       (real_list_sum X
          (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
       (real_list_sum X
          (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l)).
Proof.
  intros X l p q Hp Hq.
  apply (real_eq_trans
           (real_list_sum X
              (fun s : X => real_mult (p s) (real_opp (real_log (q s) (Hq s)))) l)
           (real_list_sum X
              (fun s : X => real_plus
                            (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
                            (real_kl_term (p s) (q s) (Hp s) (Hq s))) l)
           (real_plus
              (real_list_sum X
                 (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) l)
              (real_list_sum X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l))).
  - apply real_list_sum_ext. intro s0.
    unfold real_kl_term.
    set (Rqp := real_mult (q s0) (real_inv_pos (p s0) (Hp s0))).
    set (Hr := real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0)) (Hq s0)
                 (real_inv_pos_pos (p s0) (Hp s0))).
    set (Hpm := real_mult_positive (p s0) Rqp (Hp s0) Hr).
    assert (Hlogsplit : real_eq (real_log (q s0) (Hq s0))
                          (real_plus (real_log (p s0) (Hp s0))
                                     (real_log Rqp Hr))).
    { apply (real_eq_trans (real_log (q s0) (Hq s0))
                           (real_log (real_mult (p s0) Rqp) Hpm)
                           (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr))).
      - exact (real_log_wd (q s0) (real_mult (p s0) Rqp) (Hq s0) Hpm
                  (real_eq_sym _ _
                     (gibbsd_p_mult_ratio (p s0) (q s0) (Hp s0)))).
      - exact (real_log_mult (p s0) Rqp (Hp s0) Hr).
    }
    apply (real_eq_trans
             (real_mult (p s0) (real_opp (real_log (q s0) (Hq s0))))
             (real_mult (p s0)
                (real_plus (real_opp (real_log (p s0) (Hp s0)))
                           (real_opp (real_log Rqp Hr))))
             (real_plus (real_mult (p s0) (real_opp (real_log (p s0) (Hp s0))))
                        (real_mult (p s0) (real_opp (real_log Rqp Hr))))).
    + apply (RealSetoid.real_eq_mult_compat (p s0)
               (real_opp (real_log (q s0) (Hq s0))) (p s0)
               (real_plus (real_opp (real_log (p s0) (Hp s0)))
                          (real_opp (real_log Rqp Hr)))).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_opp (real_log (q s0) (Hq s0)))
                 (real_opp (real_plus (real_log (p s0) (Hp s0))
                                      (real_log Rqp Hr)))
                 (real_plus (real_opp (real_log (p s0) (Hp s0)))
                            (real_opp (real_log Rqp Hr)))).
        -- exact (RealSetoid.real_eq_opp_compat (real_log (q s0) (Hq s0))
                     (real_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr))
                     Hlogsplit).
        -- exact (real_opp_plus (real_log (p s0) (Hp s0)) (real_log Rqp Hr)).
    + exact (real_distrib (p s0) (real_opp (real_log (p s0) (Hp s0)))
               (real_opp (real_log Rqp Hr))).
  - exact (real_list_sum_add X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s))))
             (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)) l).
Qed.

(* ============================================================ *)
(*   Summary banner.  Bishop order algebra five-lemma family:
   gibbsd_lt_add_opp_r / gibbsd_le_b_opp / gibbsd_le_b_id_l /
   gibbsd_minus_flip / gibbsd_le_b_mult_pos_r, the real_le_b
   counterparts of opp_le_compat / le_id_l / req_le_mult_compat_r at
   the req layer (that layer has no such form; these fill the gap for
   the explicit application of the direct-form engine).
   gibbsd_p_mult_ratio / gibbsd_p_minus_ratio: two equality identities.
   gibbsd_two_pos / gibbsd_half / gibbsd_half_pos / gibbsd_half_sum
   + gibbsd_list_sum_le_b / gibbsd_list_sum_minus: six summation-layer
   lemmas (Bishop counterparts of fsum_le / fsum_minus; the eps-halving
   induction avoids division).
   gibbsd_gibbs_pointwise_B: premise discharge at the premise slot
   position (explicit application of dist_log_le_linear).
   gibbsd_cross_entropy_decomp: main lemma of the first cascade layer.
   Direction note: the section assumption in the req layer cannot be
   discharged unconditionally by the direct-form engine, so this file
   applies it explicitly in the form of a Real instantiation theorem
   (see the opening note of Part 4).  The companion Bishop order
   algebra primitives and summation machinery are in Parts 1 and 3. *)



(* ============================================================ *)

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
Require Import UpRealLeB.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qround
               Arith.Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ============================================================ *)
(* Part 6. Q-layer halving helpers. *)
(* ============================================================ *)

Lemma gibbe2_Q_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 (eps * (1#2))%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply (Qmult_lt_0_compat eps (1#2)).
  - apply QltT_to_Qlt. exact Heps.
  - reflexivity.
Qed.

Lemma gibbe2_Q_half_lt : forall eps : Q, QltT 0 eps -> QltT (eps * (1#2))%Q eps.
Proof.
  intros eps Heps.
  assert (H1 : Qlt ((1#2) * eps) (1 * eps)).
  { apply (Qmult_lt_compat_r (1#2) 1 eps).
    - apply QltT_to_Qlt. exact Heps.
    - reflexivity. }
  rewrite Qmult_1_l in H1.
  rewrite (Qmult_comm (1#2) eps) in H1.
  apply Qlt_to_QltT. exact H1.
Qed.

(* ============================================================ *)
(* Part 7. Supplementary le_b order machinery. *)
(* ============================================================ *)

(* B1. Transfer of the right end of le_b by an equality. *)
Lemma gibbe2_le_b_id_r : forall a b c : Real,
  real_le_b a b -> real_eq b c -> real_le_b a c.
Proof.
  intros a b c H Hbc eps Heps.
  unfold real_le_b in H.
  exact (RealSetoid.real_lt_compat a a (real_plus b eps) (real_plus c eps)           (real_eq_refl a)           (RealSetoid.real_eq_plus_compat b eps c eps Hbc (real_eq_refl eps))           (H eps Heps)).
Qed.

(* B2. Right-addition shift of le_b. *)
Lemma gibbe2_le_b_translate_r : forall x y z : Real,
  real_le_b x y -> real_le_b (real_plus x z) (real_plus y z).
Proof.
  intros x y z H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus z x) (real_plus x z)
           (real_plus z (real_plus y eps)) (real_plus (real_plus y z) eps)).
  - apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z y) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus z y) eps
               (real_plus y z) eps
               (real_plus_comm z y) (real_eq_refl eps)).
  - exact (real_lt_plus_translate z x (real_plus y eps) (H eps Heps)).
Qed.

(* B3：le_b a b ⟹ le_b 0 (b−a) *)
Lemma gibbe2_le_b_nonneg_diff : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H eps Heps. unfold real_le_b in H.
  apply (RealSetoid.real_lt_compat (real_plus (real_opp a) a)
           real_zero
           (real_plus (real_opp a) (real_plus b eps))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply (real_eq_trans _ (real_plus a (real_opp a)) _).
    + apply real_plus_comm.
    + exact (real_plus_opp a).
  - apply (real_eq_trans _ (real_plus (real_plus (real_opp a) b) eps) _).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp a) b) eps
               (real_plus b (real_opp a)) eps
               (real_plus_comm (real_opp a) b) (real_eq_refl eps)).
  - exact (real_lt_plus_translate (real_opp a) a (real_plus b eps) (H eps Heps)).
Qed.

(* B4 (core new lemma): antisymmetry of the Bishop order le_b (constructed pointwise in n, no Or elimination and no LPO). *)
Lemma gibbe2_le_b_antisym : forall a b : Real,
  real_le_b a b -> real_le_b b a -> real_eq a b.
Proof.
  intros a b H1 H2 eps Heps.
  assert (He2pos : real_lt real_zero (real_const (eps * (1#2))%Q))
    by (apply real_const_pos; apply gibbe2_Q_half_pos; exact Heps).
  assert (Hhe : Qlt (eps * (1#2))%Q eps)
    by (apply QltT_to_Qlt; apply gibbe2_Q_half_lt; exact Heps).
  destruct (H1 _ He2pos) as [g1 [Hg1pos [N1 HN1]]].
  destruct (H2 _ He2pos) as [g2 [Hg2pos [N2 HN2]]].
  exists (max N1 N2).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (max N1 N2);
      [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  assert (Hp1 : forall k : nat,
           projT1 (real_plus b (real_const (eps * (1#2))%Q)) k
           == projT1 b k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hp2 : forall k : nat,
           projT1 (real_plus a (real_const (eps * (1#2))%Q)) k
           == projT1 a k + projT1 (real_const (eps * (1#2))%Q) k)
    by (intro k; apply qeqT_imp_qeq; apply real_plus_proj).
  assert (Hcst : forall (c : Q) (k : nat), projT1 (real_const c) k == c)
    by (intros c k; apply qeqT_imp_qeq; apply real_const_proj).
  rewrite (Hp1 n) in HN1. rewrite (Hcst (eps * (1#2))%Q n) in HN1.
  rewrite (Hp2 n) in HN2. rewrite (Hcst (eps * (1#2))%Q n) in HN2.
  set (x := projT1 a n - projT1 b n).
  set (h := (eps * (1#2))%Q).
  assert (Hg1q : 0 < g1) by (apply QltT_to_Qlt; exact Hg1pos).
  assert (Hg2q : 0 < g2) by (apply QltT_to_Qlt; exact Hg2pos).
  (* Upper side: x < h where x is a n - b n (ring normalization plus lia). *)
  assert (Hstep1 : projT1 a n - projT1 b n + g1
                   < projT1 a n - projT1 b n
                     + (projT1 b n + eps * (1#2) - projT1 a n)).
  { exact (proj2 (Qplus_lt_r g1 (projT1 b n + eps * (1#2) - projT1 a n)
                   (projT1 a n - projT1 b n)) HN1). }
  assert (Hring1 : projT1 a n - projT1 b n
                   + (projT1 b n + eps * (1#2) - projT1 a n)
                   == eps * (1#2)) by ring.
  rewrite Hring1 in Hstep1.
  assert (Hub : projT1 a n - projT1 b n < eps * (1#2)).
  { apply (Qle_lt_trans _ (projT1 a n - projT1 b n + g1) _).
    - rewrite <- (Qplus_0_r (projT1 a n - projT1 b n)) at 1.
      apply (proj2 (Qplus_le_r 0 g1 (projT1 a n - projT1 b n))).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g1 Hg1pos)).
    - exact Hstep1. }
  (* Lower side: -x < h. *)
  assert (Hstep2 : - (projT1 a n - projT1 b n) + g2
                   < - (projT1 a n - projT1 b n)
                     + (projT1 a n + eps * (1#2) - projT1 b n)).
  { exact (proj2 (Qplus_lt_r g2 (projT1 a n + eps * (1#2) - projT1 b n)
                   (- (projT1 a n - projT1 b n))%Q) HN2). }
  assert (Hring2 : - (projT1 a n - projT1 b n)
                   + (projT1 a n + eps * (1#2) - projT1 b n)
                   == eps * (1#2)) by ring.
  rewrite Hring2 in Hstep2.
  assert (Hdn : (- (projT1 a n - projT1 b n))%Q < eps * (1#2)).
  { apply (Qle_lt_trans _ ((- (projT1 a n - projT1 b n))%Q + g2) _).
    - rewrite <- (Qplus_0_r (- (projT1 a n - projT1 b n))%Q) at 1.
      apply (proj2 (Qplus_le_r 0 g2 (- (projT1 a n - projT1 b n))%Q)).
      exact (QleT'_to_Qle _ _ (b5dH_q_pos_le g2 Hg2pos)).
    - exact Hstep2. }
  (* Final step: the absolute value of x is below eps (two sign cases, decidable over Q, no trichotomy). *)
  unfold x, h.
  apply Qlt_to_QltT.
  destruct (Qlt_le_dec 0 (projT1 a n - projT1 b n)) as [Hsx | Hsx].
  - rewrite (Qabs_pos (projT1 a n - projT1 b n) (Qlt_le_weak _ _ Hsx)).
    apply (Qlt_le_trans _ (eps * (1#2)) eps Hub).
    exact (Qlt_le_weak _ _ Hhe).
  - rewrite (Qabs_neg (projT1 a n - projT1 b n) Hsx).
    apply (Qlt_le_trans (- (projT1 a n - projT1 b n))%Q (eps * (1#2)) eps Hdn).
    exact (Qlt_le_weak _ _ Hhe).
Qed.

(* ============================================================ *)
(* Part 8. Termwise clamp-to-zero family. *)
(* ============================================================ *)

(* C1. A two-term vanishing sum implies the first term is zero. *)
Lemma gibbe2_clamp_head : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero a.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_le_b_antisym real_zero a Ha).
  apply (gibbe2_le_b_id_r a (real_plus b a) real_zero).
  - apply (gibbsd_le_b_id_l a (real_plus real_zero a) (real_plus b a)
             (real_eq_trans a (real_plus a real_zero) (real_plus real_zero a)
                (real_eq_sym _ _ (real_plus_zero a)) (real_plus_comm a real_zero))
             (gibbe2_le_b_translate_r real_zero b a Hb)).
  - apply (real_eq_trans (real_plus b a) (real_plus a b) real_zero
             (real_plus_comm b a) Hsum).
Qed.

(* C2. A two-term vanishing sum implies the second term is zero (commutativity variant). *)
Lemma gibbe2_clamp_head_r : forall a b : Real,
  real_le_b real_zero a -> real_le_b real_zero b ->
  real_eq (real_plus a b) real_zero -> real_eq real_zero b.
Proof.
  intros a b Ha Hb Hsum.
  apply (gibbe2_clamp_head b a Hb Ha).
  apply (real_eq_trans _ (real_plus a b) _).
  - apply real_plus_comm.
  - exact Hsum.
Qed.

(* C3 (main lemma): termwise sum-zero extraction over the finite concrete carrier [true; false]. *)
Lemma gibbe2_list_sum_zero_extract_bool :
  forall (f : bool -> Real),
    (forall s : bool, real_le_b real_zero (f s)) ->
    real_eq (real_list_sum bool f [true; false]) real_zero ->
    forall s : bool, real_eq real_zero (f s).
Proof.
  intros f Hpt Hsum s. destruct s; simpl in Hsum.
  - exact (gibbe2_clamp_head (f true) (real_plus (f false) real_zero)
             (Hpt true)
             (gibbe2_le_b_id_r real_zero (f false)
                (real_plus (f false) real_zero)
                (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
             Hsum).
  - apply (real_eq_trans real_zero (real_plus (f false) real_zero) (f false)).
    + exact (gibbe2_clamp_head_r (f true) (real_plus (f false) real_zero)
               (Hpt true)
               (gibbe2_le_b_id_r real_zero (f false)
                  (real_plus (f false) real_zero)
                  (Hpt false) (real_eq_sym _ _ (real_plus_zero (f false))))
               Hsum).
    + exact (real_plus_zero (f false)).
Qed.

(* ============================================================ *)

(* ============================================================ *)

(* D0. A vanishing sum implies term identity. *)
Lemma gibbe2_kl_eq_of_w_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq)
                     (real_opp (real_plus p (real_opp q)))) real_zero ->
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)).
Proof.
  intros p q Hp Hq H.
  set (X := real_plus p (real_opp q)).
  set (K := real_kl_term p q Hp Hq).
  set (NX := real_opp X).
  (* kl == (kl + −X) + X *)
  apply (real_eq_trans K (real_plus (real_plus K NX) X) X).
  - apply (real_eq_trans K (real_plus K real_zero) (real_plus (real_plus K NX) X)).
    + exact (real_eq_sym (real_plus K real_zero) K (real_plus_zero K)).
    + apply (real_eq_trans (real_plus K real_zero)
               (real_plus K (real_plus NX X))
               (real_plus (real_plus K NX) X)).
      * apply (RealSetoid.real_eq_plus_compat K real_zero K
                 (real_plus NX X)
                 (real_eq_refl K)
                 (real_eq_trans real_zero (real_plus X NX) (real_plus NX X)
                    (real_eq_sym (real_plus X NX) real_zero (real_plus_opp X))
                    (real_plus_comm X NX))).
      * exact (real_plus_assoc K NX X).
  - (* (kl + −X) + X == 0 + X == X *)
    apply (real_eq_trans (real_plus (real_plus K NX) X)
             (real_plus real_zero X) X).
    + exact (RealSetoid.real_eq_plus_compat (real_plus K NX) X real_zero X
               H (real_eq_refl X)).
    + apply (real_eq_trans (real_plus real_zero X)
               (real_plus X real_zero) X
               (real_plus_comm real_zero X)
               (real_plus_zero X)).
Qed.


Lemma gibbe2_tangent_eq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq) (real_plus p (real_opp q)) ->
  real_eq (real_log (real_mult q (real_inv_pos p Hp))
                    (real_mult_positive q (real_inv_pos p Hp) Hq
                       (real_inv_pos_pos p Hp)))
          (real_plus (real_mult q (real_inv_pos p Hp))
                     (real_opp real_one)).
Proof.
  intros p q Hp Hq H.
  set (u := real_mult q (real_inv_pos p Hp)).
  set (Hu := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log u Hu).
  (* H : p·(−L) == p + −q *)
  (* Step 1: p * L == q + -p (apply opp to both sides). *)
  assert (Hs1 : real_eq (real_mult p L) (real_plus q (real_opp p))).
  { apply (real_eq_trans (real_mult p L)
             (real_opp (real_mult p (real_opp L)))
             (real_plus q (real_opp p))).
    - apply (real_eq_sym (real_opp (real_mult p (real_opp L)))
               (real_mult p L)
               (real_eq_trans (real_opp (real_mult p (real_opp L)))
                  (real_mult p (real_opp (real_opp L)))
                  (real_mult p L)
                  (real_opp_mult p (real_opp L))
                  (RealSetoid.real_eq_mult_compat p
                     (real_opp (real_opp L)) p L
                     (real_eq_refl p) (real_opp_opp L)))).
    - apply (real_eq_trans (real_opp (real_mult p (real_opp L)))
               (real_opp (real_plus p (real_opp q)))
               (real_plus q (real_opp p))
               (RealSetoid.real_eq_opp_compat (real_mult p (real_opp L))
                  (real_plus p (real_opp q)) H)
               (gibbsd_minus_flip p q)).
  }
  (* Step 2: L == (q - p) * inv p. *)
  assert (Hs2 : real_eq L (real_mult (real_plus q (real_opp p))
                                        (real_inv_pos p Hp))).
  { apply (real_eq_trans L
             (real_mult (real_mult p L) (real_inv_pos p Hp))
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))).
    - apply (real_eq_trans L (real_mult L real_one)
               (real_mult (real_mult p L) (real_inv_pos p Hp))).
      + apply (real_eq_sym (real_mult L real_one) L (real_mult_one L)).
      + apply (real_eq_trans (real_mult L real_one)
                 (real_mult L (real_mult p (real_inv_pos p Hp)))
                 (real_mult (real_mult p L) (real_inv_pos p Hp))).
        * apply (RealSetoid.real_eq_mult_compat L real_one
                   L (real_mult p (real_inv_pos p Hp))
                   (real_eq_refl L)
                   (real_eq_sym (real_mult p (real_inv_pos p Hp)) real_one
                      (real_inv_pos_correct p Hp))).
        * apply (real_eq_trans
                   (real_mult L (real_mult p (real_inv_pos p Hp)))
                   (real_mult (real_mult L p) (real_inv_pos p Hp))
                   (real_mult (real_mult p L) (real_inv_pos p Hp))).
          -- exact (real_mult_assoc L p (real_inv_pos p Hp)).
          -- apply (RealSetoid.real_eq_mult_compat (real_mult L p)
                     (real_inv_pos p Hp) (real_mult p L) (real_inv_pos p Hp)
                     (real_mult_comm L p) (real_eq_refl _)).
    - apply (RealSetoid.real_eq_mult_compat (real_mult p L)
               (real_inv_pos p Hp) (real_plus q (real_opp p))
               (real_inv_pos p Hp) Hs1 (real_eq_refl _)).
  }
  (* Step 3: (q - p) * inv p == q * inv p + -1 == u + -1. *)
  assert (Hs3 : real_eq (real_mult (real_plus q (real_opp p))
                                   (real_inv_pos p Hp))
                        (real_plus u (real_opp real_one))).
  { apply (real_eq_trans
             (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
             (real_plus (real_mult (real_inv_pos p Hp) q)
                        (real_mult (real_inv_pos p Hp) (real_opp p)))
             (real_plus u (real_opp real_one))).
    - apply (real_eq_trans
               (real_mult (real_plus q (real_opp p)) (real_inv_pos p Hp))
               (real_mult (real_inv_pos p Hp) (real_plus q (real_opp p)))
               (real_plus (real_mult (real_inv_pos p Hp) q)
                          (real_mult (real_inv_pos p Hp) (real_opp p)))).
      + apply (real_mult_comm (real_plus q (real_opp p)) (real_inv_pos p Hp)).
      + exact (real_distrib (real_inv_pos p Hp) q (real_opp p)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (real_inv_pos p Hp) q)
               (real_mult (real_inv_pos p Hp) (real_opp p))
               (real_mult q (real_inv_pos p Hp)) (real_opp real_one)).
      + apply (real_mult_comm (real_inv_pos p Hp) q).
      + apply (real_eq_trans (real_mult (real_inv_pos p Hp) (real_opp p))
                   (real_opp (real_mult (real_inv_pos p Hp) p))
                   (real_opp real_one)).
        * apply (real_eq_sym _ _ (real_opp_mult (real_inv_pos p Hp) p)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (real_inv_pos p Hp) p) real_one).
          apply (real_eq_trans (real_mult (real_inv_pos p Hp) p)
                     (real_mult p (real_inv_pos p Hp)) real_one).
          -- apply (real_mult_comm (real_inv_pos p Hp) p).
          -- exact (real_inv_pos_correct p Hp).
  }
  exact (real_eq_trans L _ _ Hs2 Hs3).
Qed.


Lemma gibbe2_kl_zero_tangent_eq :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  forall s : bool,
    real_eq (real_log (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                      (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                         (Hq s) (real_inv_pos_pos (p s) (Hp s))))
            (real_plus (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                       (real_opp real_one)).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl.
  set (K := fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : bool => real_plus (p s) (real_opp (q s))).
  set (D := fun s : bool => real_plus (K s) (real_opp (G s))).
  (* 1. Σ(p−q) == 0 *)
  assert (HsumG0 : real_eq (real_list_sum bool G [true; false]) real_zero).
  { apply (real_eq_trans
             (real_list_sum bool G [true; false])
             (real_plus (real_list_sum bool p [true; false])
                        (real_opp (real_list_sum bool q [true; false])))
             real_zero).
    - exact (gibbsd_list_sum_minus bool p q [true; false]).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool p [true; false])
                          (real_opp (real_list_sum bool q [true; false])))
               (real_plus real_one (real_opp real_one)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool p [true; false])
                 (real_opp (real_list_sum bool q [true; false]))
                 real_one (real_opp real_one) Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool q [true; false]) real_one Hnq)).
      + exact (real_plus_opp real_one).
  }
  (* 2. ΣD == 0 *)
  assert (HsumD : real_eq (real_list_sum bool D [true; false]) real_zero).
  { unfold D.
    apply (real_eq_trans
             (real_list_sum bool
                (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
             (real_plus (real_list_sum bool K [true; false])
                        (real_opp (real_list_sum bool G [true; false])))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum bool
                  (fun s : bool => real_plus (K s) (real_opp (G s))) [true; false])
               (real_plus (real_list_sum bool K [true; false])
                          (real_list_sum bool
                             (fun s : bool => real_opp (G s)) [true; false]))
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))).
      + exact (real_list_sum_add bool K (fun s : bool => real_opp (G s))
                   [true; false]).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_list_sum bool (fun s : bool => real_opp (G s)) [true; false])
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 (real_eq_refl _)
                 (real_list_sum_opp bool G [true; false])).
    - apply (real_eq_trans
               (real_plus (real_list_sum bool K [true; false])
                          (real_opp (real_list_sum bool G [true; false])))
               (real_plus real_zero (real_opp real_zero)) real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum bool K [true; false])
                 (real_opp (real_list_sum bool G [true; false]))
                 real_zero (real_opp real_zero) Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum bool G [true; false]) real_zero HsumG0)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero) real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero (real_opp real_zero)
                   real_zero real_zero (real_eq_refl _) (real_opp_zero)).
        * exact (real_plus_zero real_zero).
  }
  (* 3. Pointwise clamp: D s == 0. *)
  assert (Hclamp : forall s : bool, real_eq (D s) real_zero).
  { intro s. apply (real_eq_sym _ _).
    apply (gibbe2_list_sum_zero_extract_bool D).
    - intro s0. exact (gibbe2_le_b_nonneg_diff _ _
                         (gibbsd_gibbs_pointwise_B bool p q s0 (Hp s0) (Hq s0))).
    - exact HsumD. }
  (* 4. Pointwise: K s == G s implies the tangency equation. *)
  intro s. apply gibbe2_tangent_eq.
  apply gibbe2_kl_eq_of_w_zero.
  exact (Hclamp s).
Qed.

(* ============================================================ *)
(* Part 9. Main lemma: the equality lemma with explicit injection of the eq-linear bridge. *)
(* ============================================================ *)

Theorem gibbe2_gibbs_equality_bool :
  forall (p q : bool -> Real)
    (Hp : forall s : bool, real_lt real_zero (p s))
    (Hq : forall s : bool, real_lt real_zero (q s))
    (Hnp : real_eq (real_list_sum bool p [true; false]) real_one)
    (Hnq : real_eq (real_list_sum bool q [true; false]) real_one),
  real_eq (real_list_sum bool
             (fun s : bool => real_kl_term (p s) (q s) (Hp s) (Hq s))
             [true; false])
          real_zero ->
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq (real_log u Hu) (real_plus u (real_opp real_one)) ->
     real_eq u real_one) ->
  forall s : bool, real_eq (p s) (q s).
Proof.
  intros p q Hp Hq Hnp Hnq Hkl Heqlin s.
  assert (Htan := gibbe2_kl_zero_tangent_eq p q Hp Hq Hnp Hnq Hkl s).
  assert (Hu1 : real_eq (real_mult (q s) (real_inv_pos (p s) (Hp s))) real_one).
  { apply (Heqlin (real_mult (q s) (real_inv_pos (p s) (Hp s)))
             (real_mult_positive (q s) (real_inv_pos (p s) (Hp s))
                (Hq s) (real_inv_pos_pos (p s) (Hp s)))).
    exact Htan. }
  apply (real_eq_trans (p s)
           (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))
           (q s)).
  - apply (real_eq_trans (p s) (real_mult (p s) real_one)
             (real_mult (p s) (real_mult (q s) (real_inv_pos (p s) (Hp s))))).
    + apply (real_eq_sym (real_mult (p s) real_one) (p s)
               (real_mult_one (p s))).
    + apply (RealSetoid.real_eq_mult_compat (p s) real_one (p s)
               (real_mult (q s) (real_inv_pos (p s) (Hp s)))
               (real_eq_refl (p s))
               (real_eq_sym (real_mult (q s) (real_inv_pos (p s) (Hp s)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s) (q s) (Hp s)).
Qed.

(* ============================================================ *)
(* Tail check: Print Assumptions (zero-axiom witness). *)
(* ============================================================ *)

Print Assumptions gibbe2_le_b_antisym.
Print Assumptions gibbe2_clamp_head.
Print Assumptions gibbe2_list_sum_zero_extract_bool.
Print Assumptions gibbe2_kl_zero_tangent_eq.
Print Assumptions gibbe2_gibbs_equality_bool.

Print Assumptions gibbe2_le_b_id_r.
