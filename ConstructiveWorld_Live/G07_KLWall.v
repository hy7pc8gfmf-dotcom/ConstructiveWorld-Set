(* ConstructiveWorld-Set -- G07_KLWall: the KL-wall merged group (five segments:
   strict tangents, convexity, power forms, Jensen, energy). *)
(** * G07_KLWall: strict positivity of the KL divergence and real-inequality
    families, carried on Set.

    Mission.  A finite merged group of five member pieces: strict
      exponential/logarithmic tangents, the KL convexity family, power-form
      bounds, Jensen's inequality, and KL energy estimates. Members are merged
      verbatim; old same-group Require names are stripped (the old library
      names are ablated; downstream files Require this group directly).

    Dependencies.  [S01_BaseRing] .. [S15_TailFEPUp] and [CW220_Extensions]
      of this development; [UpRealLeB]/[UpRealLeB2] (carried by the PowB
      segment); Stdlib [QArith.Qring], [QArith.Qfield], [List], [Lia].

    References.  ConstructiveWorld-Main [G07_KLWall]; member pieces
      [UpReqKLStrict], [UpReqKLCvx], [UpReqPowB], [UpReqJensen],
      [UpReqKLEnergy] with statement names carried over verbatim.

    Constructivity.  No axioms, nothing left open, fully closed, no
      classical logic; everything on [Set]; every proof ends in [Qed] and
      [Print Assumptions] reports Closed ([real_lt] is a [sigT] witness-valued
      relation). The twelve Q-level stations carry [QltT]/[QleT']/[QeqT]
      conclusions (S02 carriers); [Qlt]/[Qle] appear only in premise slots.
      Statement-name census: 69 declarations.

    Build.  [rocq c -native-compiler no -q -Q . "" G07_KLWall.v] compiles
      cleanly (exit 0); the first eight bytes of the artifact are
      [436f7121 00015ff4]. *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
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
Import ListNotations.

(* ============================================================ *)
(* Part A: Q-level second-order partial-sum lower bound (the gap source for the strict tangents) *)
(* ============================================================ *)

Lemma klst_ep_two_terms : forall (m : nat) (x : Q),
  Qle 0 x ->
  QleT' (1 + x + x * x * (1#2))
        (exp_partial (Datatypes.S (Datatypes.S m)) x).
Proof.
  intros m x Hx.
  apply Qle_to_QleT'.
  induction m as [| m IH].
  - apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT.
    cbn [exp_partial q_pow q_fact].
    unfold Qdiv, Qminus.
    simpl.
    field.
  - assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) x ==
                    exp_partial (Datatypes.S (Datatypes.S m)) x +
                    q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                    q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))).
    { cbn [exp_partial]. reflexivity. }
    setoid_rewrite Hstep.
    (* Qle A (B + T): split via Qle_trans into Qle A B (IH) and Qle B (B + T); *)
    (* the latter passes through (B + 0) via Qle_trans again (qeq_le ring transport kills the +0 mismatch) *)
    (* plus proj1 of Qplus_le_r 0 T B (the forward iff direction) to supply the 0 <= T entry. *)
    apply (Qle_trans (1 + x + x * x * (1#2))
                     (exp_partial (Datatypes.S (Datatypes.S m)) x)
                     (exp_partial (Datatypes.S (Datatypes.S m)) x +
                      q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                      q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))).
    + exact IH.
    + apply (Qle_trans (exp_partial (Datatypes.S (Datatypes.S m)) x)
                       (exp_partial (Datatypes.S (Datatypes.S m)) x + 0)%Q
                       (exp_partial (Datatypes.S (Datatypes.S m)) x +
                        q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                        q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))).
      * apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT.
        ring.
      * apply (proj2 (Qplus_le_r 0%Q
                        (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                         q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
                        (exp_partial (Datatypes.S (Datatypes.S m)) x))).
        apply QleT'_to_Qle.
        apply (q_pow_fact_nonneg x (Datatypes.S (Datatypes.S (Datatypes.S m))) (Qle_to_QleT' _ _ Hx)).
Qed.

(* ============================================================ *)
(* Part B: strict exponential/logarithmic tangents (positive-argument branch) *)
(* ============================================================ *)

Lemma klst_exp_tangent_pos : forall w : Real,
  real_lt real_zero w ->
  real_lt (real_plus real_one w) (cauchy_real_exp w).
Proof.
  intros [u Hu] Hw.
  destruct Hw as [eps [Heps [N0 HN0]]].
  exists (eps * eps * (1#2)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (eps * eps) (1#2)).
    + apply (Qmult_lt_0_compat eps eps).
      * apply QltT_to_Qlt. exact Heps.
      * apply QltT_to_Qlt. exact Heps.
    + unfold Qlt. simpl. lia.
  - exists (Nat.max N0 2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hmax : (Nat.max N0 2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (Hn2 : (2 <= n)%nat) by lia.
    destruct n as [| [| m]]; [ lia | lia | ].
    (* The HN0 conclusion has the shape QltT eps (u k - 0): QltT is an Id on bools and cannot be unfolded into directly, *)
    (* so go through b5a_QltT_eq_r (x==y -> QltT a y -> QltT a x) plus Q-ring transport to remove the -0. *)
    assert (Hun0m : QltT eps (u (Datatypes.S (Datatypes.S m)) - 0))
      by (apply (HN0 (Datatypes.S (Datatypes.S m))); apply NatLe_lift; exact HnN0).
    assert (HunT : QltT eps (u (Datatypes.S (Datatypes.S m))))
      by (apply (b5a_QltT_eq_r eps (u (Datatypes.S (Datatypes.S m))) (u (Datatypes.S (Datatypes.S m)) - 0));
          [ ring | exact Hun0m ]).
    assert (HunQ : Qlt eps (u (Datatypes.S (Datatypes.S m)))) by (apply QltT_to_Qlt; exact HunT).
    assert (Hun0 : Qle 0 (u (Datatypes.S (Datatypes.S m)))).
    { apply (Qle_trans 0 eps (u (Datatypes.S (Datatypes.S m)))).
      - apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
      - apply (Qlt_le_weak eps (u (Datatypes.S (Datatypes.S m)))). exact HunQ. }
    assert (Htwo : Qle (1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                       (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m)))))
      by exact (QleT'_to_Qle _ _
             (klst_ep_two_terms m (u (Datatypes.S (Datatypes.S m))) Hun0)).
    assert (Hsq : Qlt (eps * eps) (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)))).
    { apply (Qmult_lt_compat_nonneg eps (u (Datatypes.S (Datatypes.S m))) eps (u (Datatypes.S (Datatypes.S m)))).
      - split.
        + apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        + exact HunQ.
      - split.
        + apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        + exact HunQ. }
    assert (Hhalf : Qlt 0 (1#2)) by (unfold Qlt; simpl; lia).
    assert (Hscale : Qlt (eps * eps * (1#2))
                         (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2)))
      by exact (Qmult_lt_compat_r (eps * eps) (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m))) (1#2)
                                  Hhalf Hsq).
    assert (Hproj : (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) (Datatypes.S (Datatypes.S m))
                     - projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) (Datatypes.S (Datatypes.S m))) ==
                    (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) (Datatypes.S (Datatypes.S m)))).
      cbn [projT1 cauchy_real_exp real_one].
      unfold Qminus. ring. }
    rewrite Hproj.
    (* Closing: Hscale (strict) + left-multiplicative shift of Htwo (nested Qplus_le_compat, shapes aligned pointwise) *)
    apply (Qlt_le_trans (eps * eps * (1#2))
                        (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                        (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
    + exact Hscale.
    + apply (Qle_trans (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                       ((1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                          + (- 1) + (- u (Datatypes.S (Datatypes.S m))))
                       (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
      * apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT. ring.
      * apply (Qplus_le_compat
                 ((1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2)) + (- 1))
                 (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1))
                 (- u (Datatypes.S (Datatypes.S m))) (- u (Datatypes.S (Datatypes.S m)))).
        -- apply (Qplus_le_compat (1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                                 (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))))
                                 (- 1) (- 1)).
           ++ exact Htwo.
           ++ apply Qle_refl.
        -- apply Qle_refl.
Qed.

Lemma klst_log_tangent_pos : forall (x : Real)
  (Hx : real_lt real_zero x) (H1x : real_lt real_one x),
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx H1x.
  assert (Hu : real_lt real_zero (real_log x Hx)).
  { apply (RealSetoid.real_lt_id_l real_zero (real_log real_one real_lt_zero_one) (real_log x Hx)).
    - apply real_eq_sym. exact (real_log_one real_lt_zero_one).
    - exact (real_log_lt_mono real_one x real_lt_zero_one Hx H1x). }
  assert (Hexp : real_lt (real_plus real_one (real_log x Hx)) (cauchy_real_exp (real_log x Hx)))
    by exact (klst_exp_tangent_pos (real_log x Hx) Hu).
  assert (Hval : real_eq (cauchy_real_exp (real_log x Hx)) x)
    by exact (cw_log_exp_right x Hx).
  assert (H2 : real_lt (real_plus real_one (real_log x Hx)) x)
    by exact (RealSetoid.real_lt_compat (real_plus real_one (real_log x Hx))
                                        (real_plus real_one (real_log x Hx))
                                        (cauchy_real_exp (real_log x Hx)) x
                                        (real_eq_refl (real_plus real_one (real_log x Hx)))
                                        Hval Hexp).
  apply (RealSetoid.real_lt_compat (real_log x Hx) (real_log x Hx)
                                   (real_plus (real_opp real_one) x)
                                   (real_plus x (real_opp real_one))).
  - apply real_eq_refl.
  - exact (real_plus_comm (real_opp real_one) x).
  - apply (RealSetoid.real_lt_id_l (real_log x Hx)
               (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
               (real_plus (real_opp real_one) x)).
    + apply real_eq_sym.
      apply (real_eq_trans _ (real_plus (real_plus (real_opp real_one) real_one) (real_log x Hx)) _).
      * apply real_plus_assoc.
      * apply (real_eq_trans _ (real_plus real_zero (real_log x Hx)) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp real_one) real_one)
                                                (real_log x Hx)
                                                real_zero (real_log x Hx)).
           ++ apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
              ** apply real_plus_comm.
              ** apply real_plus_opp.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans _ (real_plus (real_log x Hx) real_zero) _).
           ++ apply real_plus_comm.
           ++ apply real_plus_zero.
    + apply (real_lt_plus_translate (real_opp real_one)
                                    (real_plus real_one (real_log x Hx)) x).
      exact H2.
Qed.

(* ============================================================ *)
(* Part C0: real-level transport micro-helpers (pointwise exact identities, closed in the Q ring) *)
(*   Note: the projection of real_inv_pos carries an if leb branch, so q == p*(q*inv p) is not a pointwise identity, *)
(*   hence the transport for gap_shape must not go through real_eq_of_zero_diff; it must be done at the real level via the *)
(*   assoc/comm/one/inv_pos_correct chain (klst_r_pqx_eq_q). *)
(* ============================================================ *)

Lemma klst_r_mult_distr_l : forall (p a b : Real),
  real_eq (real_mult p (real_plus a b))
          (real_plus (real_mult p a) (real_mult p b)).
Proof.
  intros p a b. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ n)) || rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n))
          || rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ n))).
  unfold Qminus. ring.
Qed.

Lemma klst_r_mult_opp_r : forall (p a : Real),
  real_eq (real_mult p (real_opp a)) (real_opp (real_mult p a)).
Proof.
  intros p a. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ n)) || rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n))
          || rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ n))).
  unfold Qminus. ring.
Qed.

Lemma klst_r_mult_m1_r : forall (p : Real),
  real_eq (real_mult p (real_opp real_one)) (real_opp p).
Proof.
  intro p. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ n)) || rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n))
          || rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ n))).
  cbn [projT1 real_one].
  unfold Qminus. ring.
Qed.

Lemma klst_r_pqx_eq_q : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans _ (real_mult q (real_mult p (real_inv_pos p Hp))) _).
  - apply (real_eq_trans _ (real_mult (real_mult p q) (real_inv_pos p Hp)) _).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans _ (real_mult (real_mult q p) (real_inv_pos p Hp)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q) (real_inv_pos p Hp)
                                             (real_mult q p) (real_inv_pos p Hp)).
        -- exact (real_mult_comm p q).
        -- apply real_eq_refl.
      * apply real_eq_sym. exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans _ (real_mult q real_one) _).
    + apply (RealSetoid.real_eq_mult_compat q (real_mult p (real_inv_pos p Hp))
                                            q real_one).
      * apply real_eq_refl.
      * exact (real_inv_pos_correct p Hp).
    + exact (real_mult_one q).
Qed.

Lemma klst_r_opp_minus : forall (a b : Real),
  real_eq (real_plus b (real_opp a)) (real_opp (real_plus a (real_opp b))).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  apply qeq_imp_qeqT.
  repeat (rewrite (qeqT_imp_qeq _ _ (real_mult_proj _ _ n)) || rewrite (qeqT_imp_qeq _ _ (real_plus_proj _ _ n))
          || rewrite (qeqT_imp_qeq _ _ (real_opp_proj _ n))).
  unfold Qminus. ring.
Qed.

(* Strict + weak-order addition: 0 < x and 0 <= y imply 0 < x + y
   (the conclusion of real_lt_plus_compat_lt_le carries (0+0); transport via real_lt_id_l + real_plus_zero) *)
Lemma klst_r_lt_plus_le : forall (x y : Real),
  real_lt real_zero x -> real_le real_zero y -> real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero) (real_plus x y)).
  - apply real_eq_sym. exact (real_plus_zero real_zero).
  - exact (real_lt_plus_compat_lt_le real_zero x real_zero y Hx Hy).
Qed.

(* ============================================================ *)
(* Part C: the strict Gibbs pointwise kernel (q>p branch) + degenerate companion *)
(* ============================================================ *)



Lemma klst_gap_shape : forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
          (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                                  (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                      (real_mult_positive q (real_inv_pos p Hp) Hq
                                                        (real_inv_pos_pos p Hp)))))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  apply (real_eq_trans
           _ (real_plus (real_opp (real_mult p L))
                        (real_plus (real_mult p X) (real_opp p))) _).
  - (* Left shape: p*(-L) + (q + -p) -> -(p*L) + (p*X + -p) *)
    apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp L))
                                          (real_plus q (real_opp p))
                                          (real_opp (real_mult p L))
                                          (real_plus (real_mult p X) (real_opp p))).
    + exact (klst_r_mult_opp_r p L).
    + apply (RealSetoid.real_eq_plus_compat q (real_opp p) (real_mult p X) (real_opp p)).
      * apply real_eq_sym. exact (klst_r_pqx_eq_q p q Hp).
      * apply real_eq_refl.
  - (* Right shape: p*((X + -1) + -L) -> (p*(X+-1)) + p*(-L) -> (p*X + -p) + -(p*L), then swap to confluence *)
    apply real_eq_sym.
    apply (real_eq_trans
             _ (real_plus (real_mult p (real_plus X (real_opp real_one)))
                          (real_mult p (real_opp L))) _).
    + exact (klst_r_mult_distr_l p (real_plus X (real_opp real_one)) (real_opp L)).
    + apply (real_eq_trans
               _ (real_plus (real_plus (real_mult p X) (real_opp p))
                            (real_opp (real_mult p L))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult p (real_plus X (real_opp real_one)))
                 (real_mult p (real_opp L))
                 (real_plus (real_mult p X) (real_opp p))
                 (real_opp (real_mult p L))).
        -- apply (real_eq_trans
                    _ (real_plus (real_mult p X) (real_mult p (real_opp real_one))) _).
           ++ exact (klst_r_mult_distr_l p X (real_opp real_one)).
           ++ apply (RealSetoid.real_eq_plus_compat (real_mult p X)
                       (real_mult p (real_opp real_one)) (real_mult p X) (real_opp p)).
              ** apply real_eq_refl.
              ** exact (klst_r_mult_m1_r p).
        -- exact (klst_r_mult_opp_r p L).
      * apply real_plus_comm.
Qed.

Lemma klst_gibbs_core_strict : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_lt p q),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hpq.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hx1 : real_lt real_one X).
  { apply (RealSetoid.real_lt_id_l real_one (real_mult p (real_inv_pos p Hp)) X).
    - apply real_eq_sym. exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat p q (real_inv_pos p Hp) Hpq (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_pos X HX Hx1).
  assert (Hgap : real_lt real_zero (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* Degenerate companion: p == q implies kl_term(p,q) + (q - p) == 0 (paired with the strict lemma). *)
Lemma klst_gibbs_core_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) real_zero.
Proof.
  intros p q Hp Hq Hpq.
  unfold real_kl_term.
  set (x := real_mult q (real_inv_pos p Hp)).
  set (Hx := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  (* x == 1: p==q transport of inv (inv_pos_ext) + inv_pos_correct *)
  assert (Hx1 : real_eq x real_one).
  { unfold x.
    apply (real_eq_trans _ (real_mult q (real_inv_pos q Hq)) _).
    - apply (RealSetoid.real_eq_mult_compat q (real_inv_pos p Hp) q (real_inv_pos q Hq)).
      + apply real_eq_refl.
      + exact (real_inv_pos_ext p q Hp Hq Hpq).
    - exact (real_inv_pos_correct q Hq). }
  
  assert (Hlog0 : real_eq (real_log x Hx) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd x real_one Hx real_lt_zero_one Hx1).
    - exact (real_log_one real_lt_zero_one). }
  (* Real-level transport chain: g == p*(-log x) + q - p == p*(-log 1) + q - p
     == p*0 + q - p == q - p == q - q == 0 *)
  apply (real_eq_trans
           _ (real_plus (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
                        (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat
             (real_mult p (real_opp (real_log x Hx)))
             (real_plus q (real_opp p))
             (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
             (real_plus q (real_opp p))).
    - apply (RealSetoid.real_eq_mult_compat p (real_opp (real_log x Hx))
                                            p (real_opp (real_log real_one real_lt_zero_one))).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_opp_compat _ _).
        exact (real_log_wd x real_one Hx real_lt_zero_one Hx1).
    - apply real_eq_refl. }
  apply (real_eq_trans
           _ (real_plus (real_mult p (real_opp real_zero)) (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat
             (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
             (real_plus q (real_opp p))
             (real_mult p (real_opp real_zero))
             (real_plus q (real_opp p))).
    - apply (RealSetoid.real_eq_mult_compat p (real_opp (real_log real_one real_lt_zero_one))
                                            p (real_opp real_zero)).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_opp_compat _ _). exact (real_log_one real_lt_zero_one).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_plus real_zero (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp real_zero))
                                         (real_plus q (real_opp p))
                                         real_zero (real_plus q (real_opp p))).
    - apply (real_eq_trans _ (real_mult p real_zero) _).
      + apply (RealSetoid.real_eq_mult_compat p (real_opp real_zero) p real_zero).
        * apply real_eq_refl.
        * exact real_opp_zero.
      + exact (real_mult_zero p).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_plus q (real_opp p)) _).
  { apply (real_eq_trans _ (real_plus (real_plus q (real_opp p)) real_zero) _).
    - apply real_plus_comm.
    - apply real_plus_zero. }
  apply (real_eq_trans _ (real_plus q (real_opp q)) _).
  { apply (RealSetoid.real_eq_plus_compat q (real_opp p) q (real_opp q)).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat p q). exact Hpq. }
  apply real_plus_opp.
Qed.

(* ============================================================ *)
(* Part D: the strict KL sum main piece (weak-order p<=q branch) *)
(* ============================================================ *)

Lemma klst_list_sum_app : forall (X : Type) (f : X -> Real) (l₁ l₂ : list X),
  real_eq (real_list_sum X f (l₁ ++ l₂))
          (real_plus (real_list_sum X f l₁) (real_list_sum X f l₂)).
Proof.
  intros X f l₁ l₂.
  induction l₁ as [| w rest IH]; cbn [app real_list_sum].
  - apply (real_eq_sym _ _).
    apply (real_eq_trans _ (real_plus (real_list_sum X f l₂) real_zero) _).
    + apply real_plus_comm.
    + apply real_plus_zero.
  - apply (real_eq_trans
             _ (real_plus (f w) (real_plus (real_list_sum X f rest) (real_list_sum X f l₂))) _).
    + apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum X f (rest ++ l₂))
                                            (f w) (real_plus (real_list_sum X f rest) (real_list_sum X f l₂))).
      * apply real_eq_refl.
      * exact IH.
    + apply real_plus_assoc.
Qed.

(* Strict KL positivity main piece: per-term positivity + double normalization + per-term p<=q (weak order, excluding the q>p branch)
   + strict separation witness at s0 (p s0 < q s0) imply 0 < sum_s kl_term. *)
Lemma klst_kl_sum_strict : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, real_le (p s) (q s))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : real_lt (p s₀) (q s₀)),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  set (L := l₁ ++ s₀ :: l₂).
  set (KL := fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : X => real_plus (KL s) (real_plus (q s) (real_opp (p s)))).
  (* 1. per-term g >= 0 (two weak-order branches: the strict branch C / the degenerate equality branch) *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hlt | Heq].
    - unfold real_le. left.
      exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
    - unfold real_le. right. apply real_eq_sym.
      exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq). }
  (* 2. sum kl L == sum G L (normalization zero-sum cancellation, same pattern as gibbs_inequality_eps) *)
  assert (Hzero : real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L) real_zero).
  { apply (real_eq_trans _ (real_plus (real_list_sum X p L) (real_list_sum X (fun s => real_opp (q s)) L)) _).
    - apply (real_list_sum_add X p (fun s => real_opp (q s)) L).
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p L)
                                             (real_list_sum X (fun s => real_opp (q s)) L)
                                             real_one (real_opp real_one)).
        * exact Hnormp.
        * apply (real_eq_trans _ (real_opp (real_list_sum X q L)) _).
          -- apply (real_list_sum_opp X q L).
          -- apply (RealSetoid.real_eq_opp_compat (real_list_sum X q L) real_one).
             exact Hnormq.
      + apply real_plus_opp. }
  assert (Hqp : real_eq (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L) real_zero).
  { apply (real_eq_trans _ (real_list_sum X (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L) _).
    - apply (real_list_sum_ext X (fun s => real_plus (q s) (real_opp (p s)))
                               (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L).
      intro s. exact (klst_r_opp_minus (p s) (q s)).
    - apply (real_eq_trans _ (real_opp (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)) _).
      + apply (real_list_sum_opp X (fun s => real_plus (p s) (real_opp (q s))) L).
      + apply (real_eq_trans _ (real_opp real_zero) _).
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)
                                               real_zero).
          exact Hzero.
        * exact real_opp_zero. }
  assert (HsumG : real_eq (real_list_sum X KL L) (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_list_sum X KL L)
                          (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)) _).
    - apply (real_eq_trans _ (real_plus (real_list_sum X KL L) real_zero) _).
      + apply real_eq_sym. apply real_plus_zero.
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X KL L) real_zero
                                              (real_list_sum X KL L)
                                              (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)).
        * apply real_eq_refl.
        * apply real_eq_sym. exact Hqp.
    - apply (real_eq_sym _ _). unfold G.
      apply (real_list_sum_add X KL (fun s => real_plus (q s) (real_opp (p s))) L). }
  (* 3. sum G L == G s0 + sum G l1 + sum G l2 (app split + assoc + comm) *)
  assert (Hsplit : real_eq (real_list_sum X G L)
                           (real_plus (real_plus (G s₀) (real_list_sum X G l₁))
                                      (real_list_sum X G l₂))).
  { unfold L.
    apply (real_eq_trans _ (real_plus (real_list_sum X G l₁)
                                      (real_plus (G s₀) (real_list_sum X G l₂))) _).
    - exact (klst_list_sum_app X G l₁ (s₀ :: l₂)).
    - apply (real_eq_trans
               _ (real_plus (real_plus (real_list_sum X G l₁) (G s₀)) (real_list_sum X G l₂)) _).
      + apply real_plus_assoc.
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_list_sum X G l₁) (G s₀))
                                             (real_list_sum X G l₂)
                                             (real_plus (G s₀) (real_list_sum X G l₁))
                                             (real_list_sum X G l₂)).
        * apply real_plus_comm.
        * apply real_eq_refl. }
  (* 4. tail sum >= 0 + one strict term imply 0 < sum G L imply 0 < sum kl L *)
  assert (Htail : real_le real_zero (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
  { apply (RealSetoid.real_le_id_r real_zero (real_list_sum X G (l₁ ++ l₂))
                                   (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - exact (klst_list_sum_app X G l₁ l₂).
    - exact (real_list_sum_nonneg X G (l₁ ++ l₂) Hgnonneg). }
  assert (Hmain : real_lt real_zero (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))).
  { apply (klst_r_lt_plus_le (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - unfold G. unfold KL.
      exact (klst_gibbs_core_strict (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hdiv).
    - exact Htail. }
  assert (Hfin : real_eq (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
                         (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_plus (G s₀) (real_list_sum X G l₁)) (real_list_sum X G l₂)) _).
    - apply real_plus_assoc.
    - apply real_eq_sym. exact Hsplit. }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
           (real_list_sum X KL L)).
  - apply (real_eq_trans _ (real_list_sum X G L) _).
    + exact Hfin.
    + apply real_eq_sym. exact HsumG.
  - exact Hmain.
Qed.

(* ============================================================ *)
(* Closed proofs (Print Assumptions must be fully Closed) *)
(* ============================================================ *)

Print Assumptions klst_ep_two_terms.
Print Assumptions klst_exp_tangent_pos.
Print Assumptions klst_log_tangent_pos.
Print Assumptions klst_r_mult_distr_l.
Print Assumptions klst_r_mult_opp_r.
Print Assumptions klst_r_mult_m1_r.
Print Assumptions klst_r_pqx_eq_q.
Print Assumptions klst_r_opp_minus.
Print Assumptions klst_r_lt_plus_le.
Print Assumptions klst_gap_shape.
Print Assumptions klst_gibbs_core_strict.
Print Assumptions klst_gibbs_core_zero.
Print Assumptions klst_list_sum_app.
Print Assumptions klst_kl_sum_strict.

(* ============================================================ *)
(* Endnote (adjudication registry) *)
(*   Adjudication 1 (whole positive-branch chain green): the strict exponential/logarithmic tangent positive branches + the strict Gibbs kernel q>p branch + *)
(*     the degenerate companion + the strict KL sum (weak-order p<=q branch) are all Qed with zero premise slots -- *)
(*     "non-constant energy implies KL>0" is fully closed on the p<=q side. *)
(*     Implementation notes (four steps): (1) the Part A stepping case passes through (B+0) via Qle_trans *)
(*     (qeq_le ring transport + Qplus_le_r 0 T B proj1), resolving the A+0 mismatch; *)
(*     (2) the real_eq_of_zero_diff route for gap_shape was falsified (the real_inv_pos projection carries *)
(*     an if leb branch, so q == p*q*inv p is not a pointwise identity); replaced by the real-level chain *)
(*     (the five C0 pieces: distr_l / mult_opp_r / mult_m1_r / pqx_eq_q / *)
(*     opp_minus; the first four via assoc/comm/one/inv_pos_correct, *)
(*     opp_minus pointwise exact); (3) the two (-1)+1 / 0+x shape sites in the klst_log_tangent_pos transport chain *)
(*     are reordered via comm+opp / comm+zero; (4) the Part D sum splits and *)
(*     shifts bridge sum(q-p)==0 via real_list_sum_ext + real_opp_zero, *)
(*     and the s0 strict term is injected directly into gibbs_core_strict (Hdiv is its Hpq argument). *)
(*   Adjudication 2 (precise blocking verdict for the negative branch): the per-term g>=0 of the q<p branch needs the negative-argument strict exponential *)
(*     tangent e^{-t} > 1-t (t>0); equivalently: the logarithmic lower tangent log y > 1-1/y (y>1) *)
(*     equals the x<1 side of the logarithmic upper tangent. Its Q-level gap source needs the four-term alternating partial-sum lower bound *)
(*     1-t+t^2/2-t^3/6 <= ep_n(-t); the existing exp_partial family is only first-order *)
(*     (exp_partial_ge_plus_x, L34891) plus the non-strict sign-split pieces *)
(*     (odd/even_ge_minus, L40707/L40814, serving the eps-shaped non-strict form), *)
(*     with no positive-gap witness field, hence a single-lemma gap; once it is filled, swapping the per-term premise of Part D to the universal weak order *)
(*     yields the unconditional piece (temperature bridge: beta2<beta1 and E0<E1 imply strict separation of the ratio; *)
(*     the strict monotonicity of cauchy_real_exp_mono is already in place, and the exp_neg sign-flip transport goes through throughout). *)
(*   Adjudication 3 (relation to the eps-shaped engine): this piece does not depend on the real_le_b closing combinator -- at the strict level *)
(*     real_lt is a sigT positive statement, with no Or equality-branch extraction obstacle; the obstacle is the missing library-side tangent *)
(*     fields (real_exp_ge_linear_eps / real_log_le_linear_eps are both *)
(*     eps-shaped Or encodings), same origin as but distinct from the known limitation recorded in the UpRealLeB endnote. *)
(* ============================================================ *)

(* ======== G07_KLWall member piece: UpReqKLCvx (merged verbatim, carries its own Requires) ======== *)
(* ============================================================ *)
(* UpReqKLCvx.v -- the KL convexity family closing module (closing 7 gap items) *)
(*   Template: UpReqGeomD.v; engine: the CW_ConstructiveWorld_219 root + everything on disk *)
(* ---------------------------------------------------------------- *)
(* Item-by-item adjudication (7 items, per the actual source read): *)
(*   [SKIP] UpReqAlign:430 req_step_kl_eta_bound -- the step_kl main piece *)
(*     is already proven by UpReqGeomD.geod_step_kl_eta_bound_eps (interface-shaped eps-le); *)
(*     a plain-le closure would be an exact Or-shape closure = a redline violation (adjudicated in the GeomD honesty-boundary *)
(*     section); to avoid duplication it is not rebuilt. *)
(*   [BLOCKED adjudication] UpReqAlign:434 req_backward_kl_identity (req equation) *)
(*     and UpReqAlign:630 req_policy_improvement_mono (plain le) -- *)
(*     both belong to the UpReqAlign softmax-KL alignment deep chain (the file's own comments record *)
(*     "req re-proof pending"): they need the log-mult full-field bridge of relative_entropy_req/pi_next_req *)
(*     eliminated via Z_align^eta -- the GeomD header item (3) already judged *)
(*     "the interface fields have no log-mult full field, hence outside their scope"; the same-origin gap is not *)
(*     crossed by this file (the constructive engine is not on disk and not buildable within a timebox); precise blocking phrase: *)
(*     the softmax-KL deep-chain log-mult interface-field gap. *)
(*   [PROVED] UpReqAttnGibbs:2146 exp_neg_geo_break -- the Archimedean N *)
(*     construction: root exp_lower_q (exists N>=2 with e^{-N}<y) + real_arch + *)
(*     cauchy_real_exp_mono all on disk; this file assembles the chain -> klcx_exp_neg_geo_break. *)
(*   [PROVED] UpReqAlignRestB:1569 req_boltzmann_diff_bridge -- the exp *)
(*     Lipschitz bridge: the root P1 main lemma real_exp_neg_diff_bound@53903 *)
(*     is verbatim the same shape as the slot statement (req_epos=exp_neg composed with opp -> Real-level epos transport) *)
(*     -> klcx_boltzmann_diff_bridge (a pure projection + eq transport proof). *)
(*   [PROVED] UpReqCauchy:221 r_arch_pow / UpReqAttnIter:163 *)
(*     arch_pow_i -- the geometric-breakdown Archimedean piece (Bernoulli + inverse chain) *)
(*     -> the unified klcx_geo_pow_break + two slot copies instantiated. *)
(* ---------------------------------------------------------------- *)
(* Landing layer: Real-instantiated theorems (the carrier is Real; real_le/real_lt are exactly the le/lt fields of the interface *)
(* RealEnhancedReal -- the iface projection pieces give the @le/@lt syntax *)
(* exports). One Or-shape plain-le closure not done (adjudication above); the redline is not crossed. *)
(* Redline: zero Prop leakage on Set-level statements; all Qed; existing files untouched. *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
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
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* K-A ring helper pieces (zero-name dependencies, zero-diff ring transport; the same technique as GeomD) *)
(* ============================================================ *)

Lemma klcx_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma klcx_const_one_eq : real_eq (real_const (1 # 1)) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Lemma klcx_const_two_eq : real_eq (real_const (2 # 1))
                                 (real_plus real_one real_one).
Proof.
  apply real_eq_of_zero_diff. intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

(* Right multiplication by a positive factor preserves strict order (the right-slot shape of real_lt_mult_compat, comm transport) *)
Lemma klcx_lt_mult_r : forall a b c : Real,
  real_lt real_zero c -> real_lt a b ->
  real_lt (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hc Hab.
  apply (real_lt_eq_lt (real_mult a c) (real_mult c b) (real_mult b c)).
  - apply (real_eq_lt_lt (real_mult a c) (real_mult c a) (real_mult c b)).
    + apply real_mult_comm.
    + exact (real_lt_mult_compat a b c Hc Hab).
  - apply real_mult_comm.
Qed.

(* ============================================================ *)
(* K-B proof piece 1: req_boltzmann_diff_bridge (UpReqAlignRestB:1569) *)
(*   Slot shape: |e^{-u}-e^{-v}| <= e^{-v}*(|u-v|*epos(|u-v|)+eps), *)
(*   epos := exp_neg composed with opp (the Real-level copy of the req-level req_epos). *)
(*   Certificate chain = given in one stroke by the root P1 main lemma real_exp_neg_diff_bound. *)
(* ============================================================ *)

Definition klcx_epos (t : Real) : Real := real_exp_neg (real_opp t).

Lemma klcx_epos_correct : forall t : Real,
  real_eq (klcx_epos t) (cauchy_real_exp t).
Proof.
  intro t. unfold klcx_epos, real_exp_neg.
  apply cauchy_real_exp_wd.
  (* Inline 1: body of klcx_opp_opp inlined wholesale (destruct + zero-diff + ring) *)
  destruct t as [u Hu]. apply real_eq_of_zero_diff.
  intro n. apply qeq_imp_qeqT. simpl. ring.
Qed.

Theorem klcx_boltzmann_diff_bridge : forall (u v eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
          (real_mult (real_exp_neg v)
                     (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                           (klcx_epos (real_abs (real_plus u (real_opp v)))))
                                eps)).
Proof.
  intros u v eps Heps.
  apply (real_le_eq_r _
           (real_mult (real_exp_neg v)
                      (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                            (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                                 eps))).
  - exact (real_exp_neg_diff_bound u v eps Heps).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
    apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (klcx_epos_correct _))).
    + apply real_eq_refl.
Qed.

(* Interface-syntax projection exports (@le/@lt are the RealEnhancedReal fields, same bodies as *)
(* real_le/real_lt -- the Real-instance syntax version of the Or-shape le at argument positions) *)
Theorem klcx_boltzmann_diff_bridge_iface : forall (u v eps : Real),
  real_lt real_zero eps ->
  real_le
     (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
     (real_mult (real_exp_neg v)
                (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                      (klcx_epos (real_abs (real_plus u (real_opp v)))))
                           eps)).
Proof.
  exact (fun u v eps => klcx_boltzmann_diff_bridge u v eps).
Qed.

(* ============================================================ *)
(* K-C proof piece 2: exp_neg_geo_break (UpReqAttnGibbs:2146) *)
(*   Slot shape: d>0 implies there exists N with e^{-2^N*d} <= eps (req_r_pow(1+1) N -> carrier *)
(*   klcx_r_pow, the copy of req_r_pow, pointwise definitional). *)
(*   Certificate chain: root exp_lower_q (e^{-N0}<eps, N0>=2) + real_arch *)
(*   (N0/d < m#1) + 2^m>m (nat + real_const_lt) + exp monotonicity. *)
(* ============================================================ *)

(* Carrier: the copy req_r_pow (1 / x*x^k pointwise), Real level *)
Fixpoint klcx_r_pow (x : Real) (n : nat) : Real :=
  match n with
  | Datatypes.O => real_one
  | Datatypes.S k => real_mult x (klcx_r_pow x k)
  end.

Lemma klcx_nat_lt_two_pow : forall n : nat,
  QltT (Z.of_nat n # 1) (Z.of_nat (Nat.pow 2 n) # 1).
Proof.
  intro n.
  apply Qlt_to_QltT.
  assert (Hnat : (n < Nat.pow 2 n)%nat) by (induction n; simpl; lia).
  assert (Hz : (Z.of_nat n < Z.of_nat (Nat.pow 2 n))%Z)
    by (apply Nat2Z.inj_lt; exact Hnat).
  unfold Qlt. cbn [Qnum Qden]. rewrite !Zmult_1_r. exact Hz.
Qed.

Lemma klcx_const_rpow_eq : forall n : nat,
  real_eq (real_const (Z.of_nat (Nat.pow 2 n) # 1))
          (klcx_r_pow (real_plus real_one real_one) n).
Proof.
  induction n as [| k IH].
  - simpl. exact klcx_const_one_eq.
  - change (Nat.pow 2 (Datatypes.S k)) with (2 * Nat.pow 2 k)%nat.
    rewrite (Nat2Z.inj_mul 2 (Nat.pow 2 k)).
    apply (real_eq_trans _
             (real_mult (real_const (2 # 1))
                        (real_const (Z.of_nat (Nat.pow 2 k) # 1)))).
    + apply real_eq_sym. apply b5j_real_const_mult_eq.
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _
               klcx_const_two_eq IH).
Qed.

Lemma klcx_exp_neg_opp_const_eq : forall n : nat,
  real_eq (cauchy_real_exp (real_opp (real_const (Z.of_nat n # 1))))
          (cauchy_real_exp (real_const (Qopp (Z.of_nat n # 1)))).
Proof.
  intro n. apply cauchy_real_exp_wd. apply real_eq_of_zero_diff.
  intro m. apply qeq_imp_qeqT.
  assert (Hp : projT1 (real_const (Qopp (Z.of_nat n # 1))) m
               == Qopp (Z.of_nat n # 1))
    by (apply (qeqT_imp_qeq _ _ (real_const_proj (Qopp (Z.of_nat n # 1)) m))).
  assert (Hq0 : projT1 (real_const (Z.of_nat n # 1)) m == Z.of_nat n # 1)
    by (apply (qeqT_imp_qeq _ _ (real_const_proj (Z.of_nat n # 1) m))).
  assert (Hq : projT1 (real_opp (real_const (Z.of_nat n # 1))) m
               == Qopp (Z.of_nat n # 1)).
  { rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_const (Z.of_nat n # 1)) m)).
    apply (Qopp_comp _ _ Hq0). }
  rewrite Hp. rewrite Hq. unfold Qminus. ring.
Qed.

Theorem klcx_exp_neg_geo_break : forall (d eps : Real),
  real_lt real_zero d -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_le (real_exp_neg
               (real_mult (klcx_r_pow (real_plus real_one real_one) N) d))
            eps).
Proof.
  intros d eps Hd Heps.
  destruct (exp_lower_q eps Heps) as [N0 [HN02 Hlt0]].
  set (N0R := real_const (Z.of_nat N0 # 1)).
  destruct (real_arch (real_mult N0R (real_inv_pos d Hd)))
    as [m [Hm2 Harch]].
  set (mR := real_const (Z.of_nat m # 1)).
  (* m > N0/d implies N0 < m*d (positive-d right multiplication + inv absorption) *)
  assert (Hstep : real_lt (real_mult (real_mult N0R (real_inv_pos d Hd)) d)
                          (real_mult mR d))
    by (apply (klcx_lt_mult_r _ _ d Hd Harch)).
  assert (Heq : real_eq (real_mult (real_mult N0R (real_inv_pos d Hd)) d) N0R).
  { apply (real_eq_trans _
             (real_mult N0R (real_mult (real_inv_pos d Hd) d))).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply (real_eq_trans _
               (real_mult N0R real_one)).
      + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
        apply (real_eq_trans (real_mult (real_inv_pos d Hd) d)
                             (real_mult d (real_inv_pos d Hd))).
        * apply real_mult_comm.
        * exact (real_inv_pos_correct d Hd).
      + apply real_mult_one. }
  assert (Hlt1 : real_lt N0R (real_mult mR d))
    by (exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ Heq) Hstep)).
  (* m#1 < 2^m (Q-level nat fact + real_const_lt + carrier transport) *)
  assert (Hlt2 : real_lt mR (klcx_r_pow (real_plus real_one real_one) m)).
  { apply (real_lt_eq_lt _ (real_const (Z.of_nat (Nat.pow 2 m) # 1)) _).
    - exact (real_const_lt _ _ (klcx_nat_lt_two_pow m)).
    - exact (klcx_const_rpow_eq m). }
  assert (Hlt3 : real_lt (real_mult mR d)
                         (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
    by (apply (klcx_lt_mult_r _ _ d Hd Hlt2)).
  assert (Hlt4 : real_lt N0R
                   (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
    by (exact (real_lt_trans _ _ _ Hlt1 Hlt3)).
  (* Negation + exp monotonicity + Qopp constant transport + exp_lower_q closure *)
  assert (Hlt5 : real_lt
                   (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
                   (real_opp N0R))
    by (apply (real_opp_lt_compat _ _ Hlt4)).
  assert (Hlt6 : real_lt (cauchy_real_exp
                            (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d)))
                         (cauchy_real_exp (real_opp N0R)))
    by (apply (cauchy_real_exp_mono _ _ Hlt5)).
  assert (Hlt7 : real_lt (cauchy_real_exp
                            (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d)))
                         (cauchy_real_exp (real_const (Qopp (Z.of_nat N0 # 1)))))
    by (exact (real_lt_eq_lt _ _ _ Hlt6 (klcx_exp_neg_opp_const_eq N0))).
  exists m. exact (inl (real_lt_trans _ _ _ Hlt7 Hlt0)).
Qed.

(* Interface-syntax projection export (sigT + @le; the Real-instance syntax version of the slot statement) *)
Theorem klcx_exp_neg_geo_break_iface : forall (d eps : Real),
  real_lt real_zero d ->
  real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_le
        (real_exp_neg
           (real_mult (klcx_r_pow (real_plus real_one real_one) N) d))
        eps).
Proof.
  exact (fun d eps => klcx_exp_neg_geo_break d eps).
Qed.

(* ============================================================ *)
(* K-D proof piece 3: r_arch_pow (UpReqCauchy:221) + arch_pow_i *)
(*   (UpReqAttnIter:163) unified piece + two slot copies instantiated *)
(*   Certificate chain = CW220_Extensions.BudgetReal.r_arch_pow_real (an on-disk *)
(*   piece: real_arch + Bernoulli + inverse chain; its .vo passed the same-track four checks) given *)
(*   in one stroke; klcx_r_pow and BudgetReal.real_pow have the same Fixpoint body pointwise *)
(*   (delta transparent; klcx_r_pow_pow_eq registered explicitly). *)
(* ============================================================ *)

Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.

(* Carrier transparency registration: klcx_r_pow x n is definitionally real_pow x n (the same recursive body) *)
Lemma klcx_r_pow_pow_eq : forall (x : Real) (n : nat),
  real_eq (klcx_r_pow x n) (real_pow x n).
Proof.
  intros x n. exact (real_eq_refl (klcx_r_pow x n)).
Qed.

(* Unified piece: geometric-breakdown Archimedes (0<k<1 implies there exists N with a*k^N < eps) --
   the same-shape kernel of the r_arch_pow slot (UpReqCauchy:221 Variable position) and the arch_pow_i slot
   (UpReqAttnIter:163 Variable position, base k := 1-delta) *)
Theorem klcx_geo_pow_break : forall (k a eps : Real),
  real_lt real_zero k -> real_lt k real_one ->
  real_lt real_zero a -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a (klcx_r_pow k N)) eps).
Proof.
  intros k a eps Hk1 Hk2 Ha Heps.
  exact (r_arch_pow_real k Hk1 Hk2 a Ha eps Heps).
Qed.

(* Slot copy 1: r_arch_pow (UpReqCauchy:221) interface-syntax projection export
   (k corresponds to the section variable kappa; the 0<k<1 premise slot rides along as an explicit slot argument) *)
Theorem klcx_r_arch_pow_iface : forall (k a eps : Real),
  real_lt real_zero k ->
  real_lt k real_one ->
  real_lt real_zero a ->
  real_lt real_zero eps ->
  sigT (fun n : nat =>
    real_lt (real_mult a (klcx_r_pow k n)) eps).
Proof.
  exact (fun k a eps => klcx_geo_pow_break k a eps).
Qed.

(* Slot copy 2: arch_pow_i (UpReqAttnIter:163) interface-syntax projection export
   (base := 1-delta; the two premise slots 0<delta and delta<1 correspond to the in-section omd positivity conditions) *)
Theorem klcx_arch_pow_omd_iface : forall (delta a eps : Real),
  real_lt real_zero delta ->
  real_lt delta real_one ->
  real_lt real_zero a ->
  real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt
        (real_mult a (klcx_r_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta a eps Hd1 Hd2 Ha Heps.
  apply (klcx_geo_pow_break (real_plus real_one (real_opp delta)) a eps).
  - exact (one_minus_delta_pos_real delta Hd2).
  - exact (one_minus_delta_lt_one_real delta Hd1).
  - exact Ha.
  - exact Heps.
Qed.

Print Assumptions klcx_boltzmann_diff_bridge.
Print Assumptions klcx_exp_neg_geo_break.
Print Assumptions klcx_geo_pow_break.
Print Assumptions klcx_r_arch_pow_iface.
Print Assumptions klcx_arch_pow_omd_iface.

(* ======== G07_KLWall member piece: UpReqPowB (merged verbatim, carries its own Requires) ======== *)
(* ============================================================ *)
(* UpReqPowB.v -- the power le_b/Bishop-order construction module (generalized main chain, Theorem 4.8 *)
(*   one of the two key Bishop-form lemmas: the power-law skeleton) *)
(*                                                              *)
(* Main results (all Set-level, zero Prop leakage, zero new axioms, zero Or branches in the monotonicity face): *)
(*   0. powb_pow: the nat-exponent power carrier (a Real-level Fixpoint, O maps to one, *)
(*      S m maps to mult base (powb_pow base m); an independent replica of the CW220_Extensions real_pow shape, *)
(*      zero upstream changes). *)
(*   1. powb_le_b_refl: the <=_B reflexivity degenerate piece (given directly term-wise by real_lt_plus_r_zero). *)
(*   2. powb_pos_lt: powers of a positive base are strictly positive (induction + the real_mult_positive engine piece). *)
(*   3. powb_pos (companion piece 2): the Bishop-form positivity 0 <=_B base^t of a power of a positive base *)
(*      (per eps: strict positivity + plus_r_zero transitivity, closed in one step). *)
(*   4. powb_sub_one (main piece 2): 0 < base <= 1 implies base^{S n} <=_B base^n *)
(*      (non-increasing at every step; witness e0 := eps*inv(base^n); from base <=_B 1 (one-way bridge *)
(*      transport) take e0 and multiply by the positive factor base^n: closed by the transport (1+e0)*u == u+eps; *)
(*      the lt branch right-multiplies the positive factor via real_mult_lt_compat; the eq branch transports + trivial shift; *)
(*      the proof body has zero Or branches -- monotonicity never uses exact comparison). *)
(*   5. powb_le_one_pow (main piece): 0 < base <= 1 and t:nat imply base^t <=_B 1 *)
(*      (a power never exceeds one; induction + sub_one + the <=_B transitivity combinator chain close it). *)
(*   6. powb_mono_dec (companion piece): NatLe n m and 0 < base <= 1 imply *)
(*      base^m <=_B base^n (Bishop-form power antitonicity; the order bound is the Set-level NatLe *)
(*      (base Id(leb) encoding, a library-wide precedent); direct induction proof -- each step of the le derivation chain uses *)
(*      sub_one + real_le_b_trans (the eps-halving combinator) transitively, zero Or branches, *)
(*      zero exact comparison). *)
(*   7. Main theorem (the direct entry of the Theorem 4.8 power law): the Bishop form of (1-eta)^t -- *)
(*      powb_one_minus_eta_pos: 0<eta<1 implies 0<1-eta (shift + opp transport); *)
(*      powb_one_minus_eta_base_le_one: 0<eta implies 1-eta <= 1 (adding eta transports to =1); *)
(*      powb_one_minus_eta_le_one: (1-eta)^t <=_B 1; *)
(*      powb_one_minus_eta_mono_dec: NatLe t t1 implies (1-eta)^{t1} <=_B *)
(*      (1-eta)^t -- the full entry of the geometric-contraction power law. *)
(*   Honesty-boundary adjudication: at the closed-interval upper end eta=1 the strict positivity certificate of 1-eta is constructively undecidable *)
(*   (1-eta==0 and 1-eta>0 are indistinguishable); the closed-end version would need a separate zero-degenerate branch -- the corresponding explicitly-hypothesized piece is not built; *)
(*   the open-interval (0,1) version already covers the Theorem 4.8 contraction entry (eta, a contraction rate, is always <1). *)
(*                                                              *)
(* Engine dependencies: UpRealLeB (real_le_b / the one-way bridge real_le_to_le_b / the lt-shift base module *)
(* real_lt_plus_r_zero) + UpRealLeB2 (real_le_b_trans, the <=_B transitivity combinator, *)
(* eps-halving). Base: CW_ConstructiveWorld_219 (the Real-level algebra and order engine pieces). *)
(* Redline: zero axioms, zero unclosed proofs (G1 forbidden words all zero); all statements Set-level (order bounds NatLe, *)
(* real_le_b, real_lt/real_le all Set-valued, zero sigT-witness-shaped statements); existing files *)
(* untouched; pure term-mode explicit assembly (real_eq is not Id, rewrite forbidden, the whole chain via *)
(* real_eq_trans/compat); all closed with Qed; the new pieces' Print Assumptions all *)
(* Closed (ten at the end of the file). *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
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
Require Import UpRealLeB2.

(* ============================================================ *)
(* 0. Carrier + degenerate pieces *)
(* ============================================================ *)

(* nat-exponent power (a Real-level Fixpoint; same shape as CW220_Extensions real_pow, independently named to avoid collisions) *)
Fixpoint powb_pow (base : Real) (t : nat) : Real :=
  match t with
  | O => real_one
  | Datatypes.S m => real_mult base (powb_pow base m)
  end.

(* <=_B reflexivity (the degenerate form of the one closing combinator; given directly term-wise by real_lt_plus_r_zero) *)
Lemma powb_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. unfold real_le_b. intros eps Heps.
  exact (real_lt_plus_r_zero x eps Heps).
Qed.

(* ============================================================ *)
(* 1. Strict-positivity induction + companion piece 2 powb_pos *)
(* ============================================================ *)

(* Powers of a positive base are strictly positive (induction; the multiplicative positivity engine piece real_mult_positive) *)
Lemma powb_pos_lt : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_lt real_zero (powb_pow base t).
Proof.
  intros base t Hb. induction t as [| m IH].
  - exact real_lt_zero_one.
  - cbn [powb_pow].
    exact (real_mult_positive base (powb_pow base m) Hb IH).
Qed.

(* Companion piece 2: the Bishop-form positivity 0 <=_B base^t of a power of a positive base (closed per eps) *)
Lemma powb_pos : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le_b real_zero (powb_pow base t).
Proof.
  intros base t Hb. unfold real_le_b. intros eps Heps.
  apply (real_lt_trans real_zero (powb_pow base t)
           (real_plus (powb_pow base t) eps)).
  - exact (powb_pos_lt base t Hb).
  - exact (real_lt_plus_r_zero (powb_pow base t) eps Heps).
Qed.

(* ============================================================ *)
(* 2. Main piece 2 powb_sub_one: base^{S n} <=_B base^n (non-increasing at every step) *)
(* ============================================================ *)

Lemma powb_sub_one : forall (base : Real) (n : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base (Datatypes.S n)) (powb_pow base n).
Proof.
  intros base n Hb Hle.
  pose proof (real_le_to_le_b base real_one Hle) as Hleb.
  pose proof (powb_pos_lt base n Hb) as Hu.
  pose proof (real_inv_pos_pos (powb_pow base n) Hu) as Hinv.
  unfold real_le_b. intros eps Heps. cbn [powb_pow].
  pose proof (real_mult_positive eps (real_inv_pos (powb_pow base n) Hu)
                Heps Hinv) as He0.
  (* Transport base module: (1 + e0)*u == u + eps (e0 := eps*inv u) *)
  assert (Hshape : real_eq
    (real_mult (real_plus real_one
                  (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
               (powb_pow base n))
    (real_plus (powb_pow base n) eps)).
  { apply (real_eq_trans _
             (real_mult (powb_pow base n)
                (real_plus real_one
                   (real_mult eps (real_inv_pos (powb_pow base n) Hu)))) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult (powb_pow base n) real_one)
                          (real_mult (powb_pow base n)
                             (real_mult eps
                                (real_inv_pos (powb_pow base n) Hu)))) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (powb_pow base n) real_one)
                 (real_mult (powb_pow base n)
                    (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
                 (powb_pow base n)
                 eps).
        * apply real_mult_one.
        * (* u*(eps*inv u) == eps *)
          apply (real_eq_trans _
                     (real_mult
                        (real_mult eps (real_inv_pos (powb_pow base n) Hu))
                        (powb_pow base n)) _).
          -- apply real_mult_comm.
          -- apply (real_eq_trans _
                       (real_mult eps
                          (real_mult (real_inv_pos (powb_pow base n) Hu)
                                     (powb_pow base n))) _).
             ++ apply real_eq_sym. apply real_mult_assoc.
             ++ apply (real_eq_trans _ (real_mult eps real_one) _).
                ** apply (RealSetoid.real_eq_mult_compat eps
                             (real_mult (real_inv_pos (powb_pow base n) Hu)
                                        (powb_pow base n))
                             eps real_one).
                   { apply real_eq_refl. }
                   { apply (real_eq_trans _
                                (real_mult (powb_pow base n)
                                   (real_inv_pos (powb_pow base n) Hu)) _).
                     - apply real_mult_comm.
                     - apply real_inv_pos_correct. }
                ** apply real_mult_one. }
  (* base <=_B 1 taken at e0: yields the strict bound base < 1+e0 directly (the le_b
     result is real_lt witness-shaped; single-branch closure, zero Or branches) *)
  pose proof (Hleb (real_mult eps (real_inv_pos (powb_pow base n) Hu)) He0)
    as Hlt.
  apply (RealSetoid.real_lt_id_r
             (real_mult base (powb_pow base n))
             (real_mult (real_plus real_one
                           (real_mult eps
                              (real_inv_pos (powb_pow base n) Hu)))
                        (powb_pow base n))
             (real_plus (powb_pow base n) eps)).
  - exact Hshape.
  - exact (real_mult_lt_compat base
               (real_plus real_one
                  (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
               (powb_pow base n) Hlt Hu).
Qed.

(* ============================================================ *)
(* 3. Main piece powb_le_one_pow: base^t <=_B 1 (a power never exceeds one) *)
(* ============================================================ *)

Lemma powb_le_one_pow : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base t) real_one.
Proof.
  intros base t Hb Hle. induction t as [| m IH].
  - exact (powb_le_b_refl real_one).
  - apply (real_le_b_trans (powb_pow base (Datatypes.S m))
             (powb_pow base m) real_one).
    + exact (powb_sub_one base m Hb Hle).
    + exact IH.
Qed.

(* ============================================================ *)
(* 4. Companion piece powb_mono_dec: base^m <=_B base^n (power antitonicity, Set-level order bound) *)
(*    (the order bound is the Set-level NatLe (base Id(leb) encoding, a library-wide precedent); direct induction proof -- *)
(*      induction on m + case analysis on n + a single boolean fork (leb (S n1) m); the Prop side only goes through *)
(*      Nat.leb_le/lift, leb_gt/antisymm for equational rewrites; zero Or elimination into Set, *)
(*      zero exact comparison; the monotone chain uses sub_one + real_le_b_trans transitivity throughout.) *)
(* ============================================================ *)

Lemma powb_mono_dec : forall (base : Real) (m : nat),
  real_lt real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (powb_pow base m) (powb_pow base n).
Proof.
  intros base m Hb Hle. induction m as [| m IH]; intros n Hnm.
  - destruct n as [| n1].
    + exact (powb_le_b_refl (powb_pow base 0)).
    + (* NatLe (S n1) 0 is Id false true; zero case explosion *)
      destruct (id_false_true Hnm).
  - destruct n as [| n1].
    + exact (powb_le_one_pow base (Datatypes.S m) Hb Hle).
    + destruct (Nat.leb (Datatypes.S n1) m) eqn:E2.
      * (* S n1 <= m: the sub_one + IH transitivity chain *)
        apply (real_le_b_trans (powb_pow base (Datatypes.S m))
                 (powb_pow base m) (powb_pow base (Datatypes.S n1))).
        -- exact (powb_sub_one base m Hb Hle).
        -- apply IH.
           apply (NatLe_lift (Datatypes.S n1) m).
           apply (proj1 (Nat.leb_le (Datatypes.S n1) m)). exact E2.
      * (* not (S n1 <= m) and n1 <= m imply n1 = m: derive the equality via antisymmetry, then reflexivity *)
        pose proof (proj1 (Nat.leb_gt (Datatypes.S n1) m) E2) as Hgt.
        pose proof (NatLe_drop n1 m Hnm) as Hn1m.
        pose proof (Nat.le_antisymm n1 m Hn1m
                     (proj1 (Nat.lt_succ_r m n1) Hgt)) as Heq.
        rewrite Heq.
        exact (powb_le_b_refl (powb_pow base (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* 5. Main theorem: the Bishop form of (1-eta)^t (the direct entry of the Theorem 4.8 power law) *)
(*    (1-eta is carried literally as real_plus real_one (real_opp eta), the same shape as the root-level *)
(*      real_pow_pos dependency face) *)
(* ============================================================ *)

(* 1-eta strictly positive (0<eta<1: shift + opp transport, zero branches) *)
Lemma powb_one_minus_eta_pos : forall eta : Real,
  real_lt real_zero eta -> real_lt eta real_one ->
  real_lt real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hpos Hlt.
  pose proof (real_lt_plus_translate (real_opp eta) eta real_one Hlt) as Htr.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus (real_opp eta) eta)
           (real_plus real_one (real_opp eta))).
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus eta (real_opp eta)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
  - apply (RealSetoid.real_lt_id_r
             (real_plus (real_opp eta) eta)
             (real_plus (real_opp eta) real_one)
             (real_plus real_one (real_opp eta))).
    + apply real_plus_comm.
    + exact Htr.
Qed.

(* 1-eta <= 1 (0<eta: (1-eta)+eta transports to =1; zero branches) *)
Lemma powb_one_minus_eta_base_le_one : forall eta : Real,
  real_lt real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
  assert (Heqsum : real_eq
    (real_plus (real_plus real_one (real_opp eta)) eta) real_one).
  { apply (real_eq_trans _
             (real_plus real_one (real_plus (real_opp eta) eta)) _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _
               (real_plus real_one (real_plus eta (real_opp eta))) _).
      + apply (RealSetoid.real_eq_plus_compat real_one
                 (real_plus (real_opp eta) eta) real_one
                 (real_plus eta (real_opp eta))).
        * apply real_eq_refl.
        * apply real_plus_comm.
      + apply (real_eq_trans _ (real_plus real_one real_zero) _).
        * apply (RealSetoid.real_eq_plus_compat real_one
                   (real_plus eta (real_opp eta)) real_one real_zero).
          -- apply real_eq_refl.
          -- apply real_plus_opp.
        * apply real_plus_zero. }
  pose proof (real_lt_plus_r_zero (real_plus real_one (real_opp eta)) eta
                Hpos) as Hlt0.
  pose proof (real_lt_eq_lt
    (real_plus real_one (real_opp eta))
    (real_plus (real_plus real_one (real_opp eta)) eta)
    real_one Hlt0 Heqsum) as Hlt1.
  exact (RealSetoid.real_lt_le_iff_req (real_plus real_one (real_opp eta))
           real_one (inl Hlt1)).
Qed.

(* Main upper bound: (1-eta)^t <=_B 1 *)
Lemma powb_one_minus_eta_le_one : forall (eta : Real) (t : nat),
  real_lt real_zero eta -> real_lt eta real_one ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t) real_one.
Proof.
  intros eta t Hpos Hlt.
  apply (powb_le_one_pow (real_plus real_one (real_opp eta)) t).
  - exact (powb_one_minus_eta_pos eta Hpos Hlt).
  - exact (powb_one_minus_eta_base_le_one eta Hpos).
Qed.

(* Main monotonicity: (1-eta)^{t1} <=_B (1-eta)^t (t <= t1; the geometric-contraction power law) *)
Theorem powb_one_minus_eta_mono_dec : forall (eta : Real) (t t1 : nat),
  real_lt real_zero eta -> real_lt eta real_one -> NatLe t t1 ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
            (powb_pow (real_plus real_one (real_opp eta)) t).
Proof.
  intros eta t t1 Hpos Hlt Hle.
  apply (powb_mono_dec (real_plus real_one (real_opp eta)) t1
           (powb_one_minus_eta_pos eta Hpos Hlt)
           (powb_one_minus_eta_base_le_one eta Hpos) t Hle).
Qed.

(* ============================================================ *)
(* Endnote: the honesty registry (adjudications cited by the paper side and the four-check reports) *)
(* [Adjudication P1 - carrier] powb_pow is an independent same-shape replica of CW220_Extensions real_pow -- zero upstream *)
(*   dependencies (only the root and the two LeB engine libraries are Required); consumers can dock with real_pow *)
(*   by transport as needed (an eq_compat-level docking piece is not built; outside this file's redline). *)
(* [Adjudication P2 - monotonicity with zero Or branches] the powb_mono_dec direct induction proof stands -- after the order bound is *)
(*   taken as NatLe (the Set-level Id(leb) encoding), every step of the le derivation chain closes through sub_one + <=_B transitivity *)
(*   combinator chains; the whole chain has no real_le premise-position Or branches and no exact comparison. *)
(* [Adjudication P3 - the sub_one witness shape] e0 := eps*inv(base^n): the Bishop multiplicative closure *)
(*   standard form (same family as the UpRealLeB closing lemma e0 := eps'*inv(2D)); the lt/eq branches close *)
(*   respectively by right-multiplying the order-preserving positive factor / equational transport + trivial shift. *)
(* [Adjudication P4 - the closed-end explicit-premise case] at eta=1 the strict positivity certificate of 1-eta is constructively undecidable (1-eta==0 and *)
(*   1-eta>0 are indistinguishable); the closed-end version over 0<eta<=1 would need a separate zero-degenerate-branch route -- the corresponding explicitly-hypothesized piece is not built; *)
(*   the open-interval (0,1) version is the proper entry for the Theorem 4.8 contraction-rate scenario. *)
(* [Check record] four-check evidence: G1 forbidden words all zero; G2 EXIT=0 + ten Print *)
(*   Assumptions Closed; G3 extraction check Obj.magic=0; G4 coqchk passed *)
(*   (logs in the _powb_* series). *)
(* ============================================================ *)

Print Assumptions powb_le_b_refl.
Print Assumptions powb_pos_lt.
Print Assumptions powb_pos.
Print Assumptions powb_sub_one.
Print Assumptions powb_le_one_pow.
Print Assumptions powb_mono_dec.
Print Assumptions powb_one_minus_eta_pos.
Print Assumptions powb_one_minus_eta_base_le_one.
Print Assumptions powb_one_minus_eta_le_one.
Print Assumptions powb_one_minus_eta_mono_dec.

(* ======== G07_KLWall member piece: UpReqJensen (merged verbatim, carries its own Requires) ======== *)
(* ============================================================ *)
(* UpReqJensen.v -- the Theorem 4.8 key-lemma module: log-sum-exp convexity in Bishop form *)
(*   (the jens_ prefix; generalized main chain, le_b proof module) *)
(*                                                                *)
(* Mathematical goals (constructive, the le_b/eps language, Set-level, zero Prop): *)
(*   (1) jens_exp_tangent: 1 - x <= exp(-x) (per-eps and le_b dual forms) *)
(*      -- the tangent lower bound, the seed of exp convexity (the specialization of CW_ConstructiveWorld_219 real_exp_ge_linear_eps *)
(*      at t := -x + the Bishop closure). *)
(*   (2) jens_two_point: exp((1-eta)x+eta y) <= (1-eta) exp x + eta exp y *)
(*      (per-eps and le_b dual forms; the eta-shape main piece + the w-shape companion theorem). *)
(*   (3) jens_weighted_n_point (main piece): the weighted n-point Jensen *)
(*      exp(sum w_i*x_i) <=_B sum w_i*exp(x_i)                        *)
(*      (w_i >= 0, sum w_i == 1; an arbitrary index-type list X). *)
(*      Route = pointwise tangent cone (the subtraction-free Varberg cone shape): *)
(*        exp(x_i) >= exp(z)*(1 + x_i - z) (the tangent at z := sum w_i x_i) *)
(*        multiply pointwise by the non-negative coefficients E*w_i (E := exp z > 0; the positivity certificate is an existing tested piece) *)
(*        sum + normalization collapse sum w_i*(1+x_i-z) == 1 *)
(*        imply sum w_i*exp(x_i) >= exp(z)*1 == exp(z). *)
(*      Error absorption goes through real_le_closure_b (the D := E > 0 closing combinator), *)
(*      zero division, zero bisection, zero trichotomy. *)
(*   (4) jens_partition (main): Z = sum pi_t^{1-eta}*pi*^eta <=_B 1 *)
(*      (pointwise AM-GM + the error weighted by eps*pi_t with normalized absorption; *)
(*        a generalization of CW_ConstructiveWorld_219 real_interp_Z_le_one_eps to arbitrary index types *)
(*        (nat-seq -> list X) + the le_b closure -- *)
(*        the mathematical kernel of Theorem 4.8 step_kl_eta_bound). *)
(*                                                                *)
(* ---------------------------------------------------------------- *)
(* Direction-correction note (4) (following the CW220_Extensions M0.1 precedent): *)
(*   the original task statement had the direction of "sum w_i*exp(-x_i) <= exp(-sum w_i*x_i) + eps" reversed: *)
(*   exp is convex, so Jensen gives exp(weighted average) <= the weighted sum of exp (the reverse is generally false; *)
(*   numerical counterexample w=(1/2,1/2), x=(-1,1): LHS approx 1.543 > 1 = RHS). *)
(*   This file states the true direction: exp(sum w_i x_i) <= sum w_i exp(x_i) + eps *)
(*   (the equivalent negative-argument form exp(-sum w x) <= sum w exp(-x) + eps). *)
(*   That direction is exactly the feasible route to the Hoelder/interpolation Z <= (sum pi)^{1-eta}(sum pi* )^eta = 1 *)
(*   (pointwise convexity + normalized summation), consistent with main item (4) -- the goal after the correction is unchanged. *)
(*   Also: interface note -- the exp of CW_ConstructiveWorld_219 is usable at all arguments (real_exp_ge_linear_eps *)
(*   covers all t with its three branches); the exp_neg naming in the interface record is a field name, not a restriction; *)
(*   every statement in this file uses cauchy_real_exp at arbitrary real arguments, zero sign-flipping burden. *)
(*                                                                *)
(* Reconnaissance conclusions (all by actual sed/grep reads): *)
(*   Seed: real_exp_ge_linear_eps@CW_ConstructiveWorld_219:40962 (1+t <= exp t + eps, *)
(*   per-eps construction); two-point kernel: real_exp_two_point_cvx_eps@CW_ConstructiveWorld_219:112669 *)
(*   (the Varberg cone); AM-GM: real_amgm_pointwise_eps@CW_ConstructiveWorld_219:112817; *)
(*   summation engine: the five real_list_sum pieces@CW_ConstructiveWorld_219:41491-41666 (ext/add/ *)
(*   linear/linear_r/le); closing combinators: real_le_closure_b@UpRealLeB *)
(*   + closure_b_one@UpRealLeB:373 + the non-negative-coefficient piece@UpRealLeB2:102; *)
(*   transport face: real_opp_le_compat/real_opp_opp/real_distrib/ *)
(*   cauchy_real_exp_plus@34782/cauchy_real_exp_wd@35117/            *)
(*   the cauchy_real_exp_pos@13376 area. *)
(*   Absence check: jensen / weighted n-point exp inequalities have zero hits library-wide -- the main piece is a genuine increment; *)
(*   the jens_ prefix has zero occupancy library-wide (grep-tested before construction). *)
(*                                                                *)
(* Redline: zero axioms, zero unclosed proofs (G1 forbidden words all zero); Set-level statements (real_le_b *)
(*   is a Set-valued forall type; conclusions have zero Prop leakage); all closed with Qed; *)
(*   existing files untouched. *)
(* ============================================================ *)

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
Require Import UpRealLeB.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A: the ring-transport base modules (real_eq chain pieces, pure term-mode assembly) *)
(* ============================================================ *)

(* A.1: z + (x + (-z)) == x (the kernel identity of the tangent-cone collapse) *)
Lemma jens_ring_z_cancel : forall z x : Real,
  real_eq (real_plus z (real_plus x (real_opp z))) x.
Proof.
  intros z x.
  apply (real_eq_trans _ (real_plus z (real_plus (real_opp z) x)) _).
  - apply (RealSetoid.real_eq_plus_compat z (real_plus x (real_opp z))
             z (real_plus (real_opp z) x)).
    + apply real_eq_refl.
    + apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z (real_opp z)) x) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero x) _).
      * apply (RealSetoid.real_eq_plus_compat (real_plus z (real_opp z)) x
                 real_zero x).
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply sf_real_plus_zero_l.
Qed.

(* A.2: 1 - (1 - w) == w (the direction-transport kernel of the w-shape two-point piece) *)
Lemma jens_ring_one_involut : forall w : Real,
  real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) w.
Proof.
  intro w.
  apply (real_eq_trans _
           (real_plus real_one
              (real_plus (real_opp real_one) (real_opp (real_opp w)))) _).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_opp (real_plus real_one (real_opp w))) real_one
             (real_plus (real_opp real_one) (real_opp (real_opp w)))).
    + apply real_eq_refl.
    + apply real_opp_plus.
  - apply (real_eq_trans _
             (real_plus (real_plus real_one (real_opp real_one))
                        (real_opp (real_opp w))) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_opp (real_opp w)) _).
      * apply (real_eq_trans _
                 (real_plus real_zero (real_opp (real_opp w))) _).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus real_one (real_opp real_one))
                     (real_opp (real_opp w)) real_zero (real_opp (real_opp w))).
           ++ apply real_plus_opp.
           ++ apply real_eq_refl.
        -- apply sf_real_plus_zero_l.
      * apply real_opp_opp.
Qed.

(* ============================================================ *)
(* Part B: companion piece 2 -- jens_exp_tangent (the tangent lower bound, dual forms) *)
(*   1 - x <= exp(-x) + eps (per eps); the le_b form closes via the one specialization. *)
(* ============================================================ *)

Lemma jens_exp_tangent_eps : forall (x eps : Real),
  real_lt real_zero eps ->
  real_le (real_plus real_one (real_opp x))
          (real_plus (cauchy_real_exp (real_opp x)) eps).
Proof.
  intros x eps Heps.
  exact (RealInterfaceEnhancedMod.real_exp_ge_linear_eps (real_opp x) eps Heps).
Qed.

Lemma jens_exp_tangent : forall x : Real,
  real_le_b (real_plus real_one (real_opp x))
            (cauchy_real_exp (real_opp x)).
Proof.
  intro x.
  (* Inline 2: the body of the real_le_closure_b_one combinator inlined wholesale (template UpRealLeB.v:381-400,
     the D:=one specialization + the two-step 1*eps ~ eps transport bridge), A/B explicitly instantiated *)
  apply (real_le_closure_b (real_plus real_one (real_opp x))
           (cauchy_real_exp (real_opp x)) real_one real_lt_zero_one).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r (real_plus real_one (real_opp x))
           (real_plus (cauchy_real_exp (real_opp x)) eps)
           (real_plus (cauchy_real_exp (real_opp x)) (real_mult real_one eps))).
  - apply (RealSetoid.real_eq_plus_compat (cauchy_real_exp (real_opp x)) eps
             (cauchy_real_exp (real_opp x)) (real_mult real_one eps)).
    + apply real_eq_refl.
    + apply (real_eq_trans eps (real_mult eps real_one)
               (real_mult real_one eps)).
      * apply real_eq_sym. apply real_mult_one.
      * apply real_mult_comm.
  - exact (jens_exp_tangent_eps x eps Heps).
Qed.

(* ============================================================ *)
(* Part C: companion piece -- jens_two_point (two-point convexity, dual forms + dual argument shapes) *)
(*   True direction (see the direction-correction note (4) above): exp(convex combination) <= the convex combination of exp + eps. *)
(*   The eta-shape main piece connects directly to the CW_ConstructiveWorld_219 Varberg cone kernel; the w-shape companion theorem transports via A.2. *)
(* ============================================================ *)

(* C.1 the eta shape per eps (premise slots copied from the source piece: 0 < eta <= 1) *)
Lemma jens_two_point_eps : forall (eta x y eps : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                      (real_mult eta y)))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                            (cauchy_real_exp x))
                                (real_mult eta (cauchy_real_exp y)))
                     eps).
Proof.
  intros eta x y eps Heta_pos Heta_le Heps.
  exact (real_exp_two_point_cvx_eps x y eta Heta_pos Heta_le eps Heps).
Qed.

(* C.2 the eta-shape Bishop closure (le_b) *)
Lemma jens_two_point : forall (eta x y : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
            (real_plus (real_mult (real_plus real_one (real_opp eta))
                                  (cauchy_real_exp x))
                       (real_mult eta (cauchy_real_exp y))).
Proof.
  intros eta x y Heta_pos Heta_le.
  (* Inline 3: the body of the real_le_closure_b_one combinator inlined wholesale (the same template as Inline 2),
     A:=exp((1-eta)x+eta y), B:=(1-eta) exp x + eta exp y explicitly instantiated *)
  apply (real_le_closure_b
           (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
           (real_plus (real_mult (real_plus real_one (real_opp eta))
                                 (cauchy_real_exp x))
                      (real_mult eta (cauchy_real_exp y)))
           real_one real_lt_zero_one).
  intros eps Heps.
  apply (RealSetoid.real_le_id_r
           (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                             (cauchy_real_exp x))
                                 (real_mult eta (cauchy_real_exp y)))
                      eps)
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                             (cauchy_real_exp x))
                                 (real_mult eta (cauchy_real_exp y)))
                      (real_mult real_one eps))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus (real_mult (real_plus real_one (real_opp eta))
                                    (cauchy_real_exp x))
                        (real_mult eta (cauchy_real_exp y)))
             eps
             (real_plus (real_mult (real_plus real_one (real_opp eta))
                                    (cauchy_real_exp x))
                        (real_mult eta (cauchy_real_exp y)))
             (real_mult real_one eps)).
    + apply real_eq_refl.
    + apply (real_eq_trans eps (real_mult eps real_one)
               (real_mult real_one eps)).
      * apply real_eq_sym. apply real_mult_one.
      * apply real_mult_comm.
  - exact (jens_two_point_eps eta x y eps Heta_pos Heta_le Heps).
Qed.

(* C.3 the w shape per eps (0 <= w, 0 < 1-w) *)
Lemma jens_two_point_w_eps : forall (w x y eps : Real),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (real_opp w)) ->
  real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult w x)
                                      (real_mult (real_plus real_one (real_opp w)) y)))
          (real_plus (real_plus (real_mult w (cauchy_real_exp x))
                                (real_mult (real_plus real_one (real_opp w))
                                           (cauchy_real_exp y)))
                     eps).
Proof.
  intros w x y eps Hw0 Hw1 Heps.
  (* 0 <= w implies -w <= 0 implies 1-w <= 1 (the seed eta <= 1 premise slot) *)
  assert (Hnegw : real_le (real_opp w) real_zero).
  { apply (kl_le_eq_r (real_opp w) (real_opp real_zero) real_zero).
    - exact (real_opp_le_compat real_zero w Hw0).
    - exact real_opp_zero. }
  assert (Hwle1 : real_le (real_plus real_one (real_opp w)) real_one).
  { apply (kl_le_eq_r (real_plus real_one (real_opp w))
             (real_plus real_one real_zero) real_one).
    - exact (real_le_plus_compat real_one real_one (real_opp w) real_zero
                 (real_le_refl real_one) Hnegw).
    - apply real_plus_zero. }
  (* substitute eta := 1-w into the seed, both sides transported along (1-(1-w)) == w *)
  pose proof (jens_two_point_eps (real_plus real_one (real_opp w)) x y eps
                Hw1 Hwle1 Heps) as Hcvx.
  apply (RealSetoid.real_le_compat
           (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) x)
                                       (real_mult (real_plus real_one (real_opp w)) y)))
           (cauchy_real_exp (real_plus (real_mult w x)
                                       (real_mult (real_plus real_one (real_opp w)) y)))
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) (cauchy_real_exp x))
                                 (real_mult (real_plus real_one (real_opp w)) (cauchy_real_exp y)))
                      eps)
           (real_plus (real_plus (real_mult w (cauchy_real_exp x))
                                 (real_mult (real_plus real_one (real_opp w)) (cauchy_real_exp y)))
                      eps)).
  - apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat
               (real_plus real_one (real_opp (real_plus real_one (real_opp w))))
               x w x).
      * exact (jens_ring_one_involut w).
      * apply real_eq_refl.
    + apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus real_one (real_opp (real_plus real_one (real_opp w))))
                 (cauchy_real_exp x) w (cauchy_real_exp x)).
        -- exact (jens_ring_one_involut w).
        -- apply real_eq_refl.
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus real_one (real_opp w)) (cauchy_real_exp y)
                 (real_plus real_one (real_opp w)) (cauchy_real_exp y)).
        -- apply real_eq_refl.
        -- apply real_eq_refl.
    + apply real_eq_refl.
  - exact Hcvx.
Qed.

(* C.4 the w-shape Bishop closure (le_b) *)
Lemma jens_two_point_w : forall (w x y : Real),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (real_opp w)) ->
  real_le_b (cauchy_real_exp (real_plus (real_mult w x)
                                        (real_mult (real_plus real_one (real_opp w)) y)))
            (real_plus (real_mult w (cauchy_real_exp x))
                       (real_mult (real_plus real_one (real_opp w))
                                  (cauchy_real_exp y))).
Proof.
  intros w x y Hw0 Hw1.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_two_point_w_eps w x y eps Hw0 Hw1 Heps).
Qed.

(* ============================================================ *)
(* Part D: the main piece -- jens_weighted_n_point (the weighted n-point Jensen) *)
(*   exp(sum w_i*x_i) <=_B sum w_i*exp(x_i)                           *)
(*   (w_i >= 0, sum w_i == 1; the pointwise tangent-cone route, zero division). *)
(* ============================================================ *)

Theorem jens_weighted_n_point_b : forall (X : Type) (w x : X -> Real) (l : list X),
  (forall a : X, real_le real_zero (w a)) ->
  real_eq (real_list_sum X w l) real_one ->
  real_le_b (cauchy_real_exp (real_list_sum X (fun a : X => real_mult (w a) (x a)) l))
            (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
Proof.
  intros X w x l Hw0 Hnorm.
  unfold real_le_b.
  set (z := real_list_sum X (fun a : X => real_mult (w a) (x a)) l).
  set (E := cauchy_real_exp z).
  set (S := real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
  (* Closing combinator D := E; the positivity certificate exp z > 0 (an existing CW_ConstructiveWorld_219 piece) *)
  apply (real_le_closure_b E S E (cauchy_real_exp_pos z)).
  intros h Hh.
  set (t := fun a : X => real_plus (x a) (real_opp z)).
  (* Kernel transport: E*exp(t a) == exp(x a) *)
  assert (HexpE : forall a : X,
            real_eq (real_mult E (cauchy_real_exp (t a))) (cauchy_real_exp (x a))).
  { intro a.
    apply (real_eq_trans _ (cauchy_real_exp (real_plus z (t a))) _).
    - apply real_eq_sym.
      exact (cauchy_real_exp_plus z (t a)).
    - apply (cauchy_real_exp_wd (real_plus z (t a)) (x a)).
      exact (jens_ring_z_cancel z (x a)). }
  (* Pointwise transport: w a*exp(x a) == E*(w a*exp(t a)) *)
  assert (FT : forall a : X,
            real_eq (real_mult (w a) (cauchy_real_exp (x a)))
                    (real_mult E (real_mult (w a) (cauchy_real_exp (t a))))).
  { intro a.
    apply (real_eq_trans _
             (real_mult (w a) (real_mult E (cauchy_real_exp (t a)))) _).
    - apply (RealSetoid.real_eq_mult_compat (w a) (cauchy_real_exp (x a))
               (w a) (real_mult E (cauchy_real_exp (t a)))).
      + apply real_eq_refl.
      + apply real_eq_sym.
        exact (HexpE a).
    - apply (real_eq_trans _
               (real_mult (real_mult (w a) E) (cauchy_real_exp (t a))) _).
      + apply real_mult_assoc.
      + apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (cauchy_real_exp (t a))) _).
        * apply (RealSetoid.real_eq_mult_compat (real_mult (w a) E)
                   (cauchy_real_exp (t a)) (real_mult E (w a))
                   (cauchy_real_exp (t a))).
          -- apply real_mult_comm.
          -- apply real_eq_refl.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (cauchy_real_exp (t a))).
  }
  (* Normalization-collapse kernel: sum w_i*(x_i - z) == 0 *)
  assert (HN0 : real_eq (real_list_sum X (fun a : X => real_mult (w a) (t a)) l)
                        real_zero).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) (x a)) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (real_opp z)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) (x a))
                                                        (real_mult (w a) (real_opp z))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (real_eq_trans _ (real_plus z (real_opp z)) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply real_eq_refl.
        * apply (real_eq_trans _
                   (real_mult (real_opp z) (real_list_sum X w l)) _).
          -- exact (real_list_sum_linear_r X (real_opp z) w l).
          -- apply (real_eq_trans _ (real_mult (real_opp z) real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat (real_opp z)
                          (real_list_sum X w l) (real_opp z) real_one
                          (real_eq_refl (real_opp z)) Hnorm).
             ++ apply real_mult_one.
      + apply real_plus_opp. }
  (* Normalization collapse: sum w_i*(1 + x_i - z) == 1 *)
  assert (HN1 : real_eq (real_list_sum X (fun a : X => real_mult (w a)
                                            (real_plus real_one (t a))) l)
                        real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) real_one) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (t a)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) real_one)
                                                        (real_mult (w a) (t a))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (real_eq_trans _ (real_plus real_one real_zero) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (real_eq_trans _
                   (real_mult real_one (real_list_sum X w l)) _).
          -- exact (real_list_sum_linear_r X real_one w l).
          -- apply (real_eq_trans _ (real_mult real_one real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat real_one
                          (real_list_sum X w l) real_one real_one
                          (real_eq_refl real_one) Hnorm).
             ++ apply real_mult_one.
        * exact HN0.
      + apply real_plus_zero. }
  (* Pointwise tangent x non-negative coefficients: f a <= g a *)
  assert (Hcpos : forall a : X, real_le real_zero (real_mult E (w a))).
  { intro a. exact (kl_le_mult_weak_swap (w a) E (Hw0 a) (cauchy_real_exp_pos z)). }
  assert (Hpt : forall a : X,
            real_le (real_mult (real_plus real_one (t a)) (real_mult E (w a)))
                    (real_mult (real_plus (cauchy_real_exp (t a)) h)
                               (real_mult E (w a)))).
  { intro a.
    apply real_le_mult_compat_weak.
    - exact (kl_le_mult_weak_swap (w a) E (Hw0 a) (cauchy_real_exp_pos z)).
    - exact (RealInterfaceEnhancedMod.real_exp_ge_linear_eps (t a) h Hh). }
  assert (Hsum : real_le (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l)
                         (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l))
    by exact (real_list_sum_le X _ _ l Hpt).
  (* Left end == E *)
  assert (HL : real_eq (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l) E).
  { apply (real_eq_trans _
             (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (real_plus real_one (t a))) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (real_plus real_one (t a)))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a.
        apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (real_plus real_one (t a))) _).
        * apply real_mult_comm.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (real_plus real_one (t a))).
      + exact (real_list_sum_linear X E
                 (fun a : X => real_mult (w a) (real_plus real_one (t a))) l).
    - apply (real_eq_trans _ (real_mult E real_one) _).
      + apply (RealSetoid.real_eq_mult_compat E
                 (real_list_sum X (fun a : X => real_mult (w a) (real_plus real_one (t a))) l)
                 E real_one (real_eq_refl E) HN1).
      + apply real_mult_one. }
  (* Middle-sum identity: sum w*(exp t + h) == T + h (T := sum w*exp t) *)
  assert (HTsum : real_eq
            (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)
            (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l)
                        (real_list_sum X (fun a : X => real_mult (w a) h) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) (cauchy_real_exp (t a)))
                                                        (real_mult (w a) h)) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      + apply real_eq_refl.
      + apply (real_eq_trans _ (real_mult h (real_list_sum X w l)) _).
        * exact (real_list_sum_linear_r X h w l).
        * apply (real_eq_trans _ (real_mult h real_one) _).
          -- apply (RealSetoid.real_eq_mult_compat h (real_list_sum X w l)
                       h real_one (real_eq_refl h) Hnorm).
          -- apply real_mult_one. }
  (* Right end == S + E*h *)
  assert (HR : real_eq (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l)
                       (real_plus S (real_mult E h))).
  { apply (real_eq_trans _
             (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (real_plus (cauchy_real_exp (t a)) h))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a.
        apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (real_plus (cauchy_real_exp (t a)) h)) _).
        * apply real_mult_comm.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (real_plus (cauchy_real_exp (t a)) h)).
      + exact (real_list_sum_linear X E
                 (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l).
    - apply (real_eq_trans _
               (real_mult E (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)) _).
      + apply (RealSetoid.real_eq_mult_compat E
                 (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)
                 E (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)
                 (real_eq_refl E) HTsum).
      + apply (real_eq_trans _
                 (real_plus (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l))
                            (real_mult E h)) _).
        * apply real_distrib.
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          -- (* E*T == S: via the sum(E*(w*exp t)) bridge (pointwise FT reversed + linear reversed) *)
             apply (real_eq_trans
                      (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l))
                      (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a)))) l)
                      S).
            ++ apply real_eq_sym.
               exact (real_list_sum_linear X E
                        (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l).
            ++ apply (real_eq_trans
                        (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a)))) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l)
                        S).
               ** apply (real_list_sum_ext X
                            (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a))))
                            (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
                  intro a. apply real_eq_sym.
                  exact (FT a).
               ** apply real_eq_refl.
          -- apply real_eq_refl. }
  (* Close up: E == sum f <= sum g == S + E*h, closed per h *)
  apply (kl_le_eq_r E
           (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l)
           (real_plus S (real_mult E h))).
  - apply (kl_le_eq_l
             (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l)
             (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l) E).
    + exact Hsum.
    + exact HL.
  - exact HR.
Qed.

(* D.2 the per-eps form (the specialization of the le_b main piece at a given eps; the inl branch of the one-way Or bridge) *)
Theorem jens_weighted_n_point : forall (X : Type) (w x : X -> Real) (l : list X),
  (forall a : X, real_le real_zero (w a)) ->
  real_eq (real_list_sum X w l) real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_list_sum X (fun a : X => real_mult (w a) (x a)) l))
          (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l) eps).
Proof.
  intros X w x l Hw0 Hnorm eps Heps.
  apply (RealSetoid.real_lt_le_iff_req).
  left.
  exact (jens_weighted_n_point_b X w x l Hw0 Hnorm eps Heps).
Qed.

(* ============================================================ *)
(* Part E: the main theorem -- jens_partition (sum pi^{1-eta}*pi*^eta <=_B 1) *)
(*   The generalization to an arbitrary index-type list X (the CW_ConstructiveWorld_219 nat-seq version -> list X) + the le_b closure. *)
(*   Route: pointwise AM-GM (the error weighted by eps*pi_t, absorbed through normalization with positive weights) *)
(*   imply Z <= (1-eta)*sum pi + eta*sum pi* + eps == 1 + eps. Zero division, zero bisection. *)
(* ============================================================ *)

Theorem jens_partition_eps : forall (X : Type) (pit pist : X -> Real) (l : list X) (eta : Real)
    (Hpit : forall a : X, real_lt real_zero (pit a))
    (Hpist : forall a : X, real_lt real_zero (pist a)),
  real_eq (real_list_sum X pit l) real_one ->
  real_eq (real_list_sum X pist l) real_one ->
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum X
             (fun a : X => real_mult
                (real_pow_pos (pit a) (real_plus real_one (real_opp eta)) (Hpit a))
                (real_pow_pos (pist a) eta (Hpist a)))
             l)
          (real_plus real_one eps).
Proof.
  intros X pit pist l eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  (* Pointwise AM-GM with the error term weighted eps*pit a (positivity: eps>0 times pit a>0) *)
  assert (Hpt : forall a : X,
            real_le (real_mult (real_pow_pos (pit a) m (Hpit a))
                               (real_pow_pos (pist a) eta (Hpist a)))
                    (real_plus (real_plus (real_mult m (pit a))
                                          (real_mult eta (pist a)))
                               (real_mult eps (pit a)))).
  { intro a.
    exact (real_amgm_pointwise_eps (pit a) (pist a) eta (Hpit a) (Hpist a)
             Heta_pos Heta_le (real_mult eps (pit a))
             (real_mult_positive eps (pit a) Heps (Hpit a))). }
  assert (Hsum : real_le
            (real_list_sum X (fun a : X => real_mult
                                (real_pow_pos (pit a) m (Hpit a))
                                (real_pow_pos (pist a) eta (Hpist a))) l)
            (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l))
    by exact (real_list_sum_le X _ _ l Hpt).
  (* Split: sum(f + g) == sum f + sum g *)
  assert (Hsplit : real_eq
            (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l)
            (real_plus (real_list_sum X (fun a : X => real_plus
                                            (real_mult m (pit a))
                                            (real_mult eta (pist a))) l)
                       (real_list_sum X (fun a : X => real_mult eps (pit a)) l)))
    by exact (real_list_sum_add X _ _ l).
  (* sum f == m*sum pit + eta*sum pist == m*1 + eta*1 == m + eta == 1 *)
  assert (Hf : real_eq (real_list_sum X (fun a : X => real_plus
                                            (real_mult m (pit a))
                                            (real_mult eta (pist a))) l)
                       real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult m (pit a)) l)
                        (real_list_sum X (fun a : X => real_mult eta (pist a)) l)) _).
    - exact (real_list_sum_add X _ _ l).
    - apply (real_eq_trans _
                (real_plus (real_mult m (real_list_sum X pit l))
                           (real_mult eta (real_list_sum X pist l))) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * exact (real_list_sum_linear X m pit l).
        * exact (real_list_sum_linear X eta pist l).
      + apply (real_eq_trans _ (real_plus m eta) _).
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          -- apply (real_eq_trans _ (real_mult m real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat m
                          (real_list_sum X pit l) m real_one
                          (real_eq_refl m) Hnormp).
             ++ apply real_mult_one.
          -- apply (real_eq_trans _ (real_mult eta real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat eta
                          (real_list_sum X pist l) eta real_one
                          (real_eq_refl eta) Hnormq).
             ++ apply real_mult_one.
        * exact (kl_ring_m_plus_eta eta). }
  (* sum g == eps*sum pit == eps*1 == eps *)
  assert (Hg : real_eq (real_list_sum X (fun a : X => real_mult eps (pit a)) l) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum X pit l)) _).
    - exact (real_list_sum_linear X eps pit l).
    - exact (real_eq_trans (real_mult eps (real_list_sum X pit l))
               (real_mult eps real_one) eps
               (RealSetoid.real_eq_mult_compat eps (real_list_sum X pit l)
                  eps real_one (real_eq_refl eps) Hnormp)
               (real_mult_one eps)). }
  (* Close up: Z <= sum f + sum g == 1 + eps *)
  exact (kl_le_eq_r
           (real_list_sum X (fun a : X => real_mult
                                (real_pow_pos (pit a) m (Hpit a))
                                (real_pow_pos (pist a) eta (Hpist a))) l)
           (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l)
           (real_plus real_one eps)
           Hsum
           (real_eq_trans _
              (real_plus (real_list_sum X (fun a : X => real_plus
                                              (real_mult m (pit a))
                                              (real_mult eta (pist a))) l)
                         (real_list_sum X (fun a : X => real_mult eps (pit a)) l))
              (real_plus real_one eps)
              Hsplit
              (RealSetoid.real_eq_plus_compat _ _ _ _ Hf Hg))).
Qed.

(* E.2 the main-theorem Bishop closure (le_b): sum pi^{1-eta}*pi*^eta <=_B 1
   -- the mathematical kernel of Theorem 4.8 step_kl_eta_bound (the le_b/eps form; the Or-shape exact
   closure is constructively unprovable; adjudication in the UpRealLeB endnote registry). *)
Theorem jens_partition : forall (X : Type) (pit pist : X -> Real) (l : list X) (eta : Real)
    (Hpit : forall a : X, real_lt real_zero (pit a))
    (Hpist : forall a : X, real_lt real_zero (pist a)),
  real_eq (real_list_sum X pit l) real_one ->
  real_eq (real_list_sum X pist l) real_one ->
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_list_sum X
               (fun a : X => real_mult
                  (real_pow_pos (pit a) (real_plus real_one (real_opp eta)) (Hpit a))
                  (real_pow_pos (pist a) eta (Hpist a)))
               l)
            real_one.
Proof.
  intros X pit pist l eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_partition_eps X pit pist l eta Hpit Hpist Hnormp Hnormq
           Heta_pos Heta_le eps Heps).
Qed.

(* ============================================================ *)
(* Endnote: the increment adjudications of this file *)
(*                                                                *)
(* [Adjudication J1 - direction correction (4)] the original task statement's "sum w exp(-x) <= exp(-sum w x) + eps" *)
(*   is the reverse Jensen, generally false (numerical counterexamples exist); this file states and carries throughout the true direction *)
(*   exp(sum w x) <= sum w exp(x) + eps -- following the CW220_Extensions M0.1 *)
(*   "false-statement correction" precedent; the goal after the correction (the Bishop-form convexity + the main theorem Z <= 1) *)
(*   is unchanged and is exactly the provable direction. *)
(* [Adjudication J2 - the pointwise tangent cone] the main-piece route = the tangent lower bound (companion piece 2) x non-negative coefficients *)
(*   (kl_le_mult_weak_swap) x summation (real_list_sum_le) x normalization collapse *)
(*   (HN0/HN1) x the D-shape closing combinator (D := exp z; the positivity certificate is cauchy-tested): *)
(*   compared with the induction route of "n=1 base case + cons reduction to two points", it avoids the three mountains of subtraction / renormalization / *)
(*   error 1/n splitting; the whole chain has zero division; in the cons-induction route the renormalization *)
(*   division face w_i/(1-w_a) does not arise in this route. *)
(* [Adjudication J3 - the unified per-eps slack] the main-piece closing combinator face instantiates the universal slot at h := eps, *)
(*   same origin as adjudication S1 of the sumb_ family: the slack of the universal face of real_le_b is copyable, no *)
(*   constructive halving needed. *)
(* [Adjudication J4 - the main generalization boundary] CW_ConstructiveWorld_219 real_interp_Z_le_one_eps is the *)
(*   nat-indexed seq 0 n specialization; this file's jens_partition generalizes to an arbitrary index type *)
(*   list X (the real_list_sum engine is generic in X as its first argument anyway; the pointwise/summation/collapse *)
(*   three segments all generalize by direct porting), and is in specialization relation with the UpRealLeB real_interp_Z_le_one_B *)
(*   (E.18) -- E.18 depends on this piece only through the single-step instance X := nat, *)
(*   l := seq 0 n (this file does not modify existing files in return). *)
(* [Adjudication J5 - the two-point increment boundary] the two-point convexity eps-shape kernel already exists in CW_ConstructiveWorld_219 *)
(*   (real_exp_two_point_cvx_eps, the Varberg cone); this file's increments are *)
(*   the le_b closed dual forms (C.2/C.4) + the w-argument companion (C.3/C.4, including *)
(*   the 1-(1-w) == w transport kernel A.2 and the 0 <= w implies 1-w <= 1 chain). *)
(* ============================================================ *)

Print Assumptions jens_exp_tangent_eps.
Print Assumptions jens_exp_tangent.
Print Assumptions jens_two_point_eps.
Print Assumptions jens_two_point.
Print Assumptions jens_two_point_w_eps.
Print Assumptions jens_two_point_w.
Print Assumptions jens_weighted_n_point_b.
Print Assumptions jens_weighted_n_point.
Print Assumptions jens_partition_eps.
Print Assumptions jens_partition.

(* ======== G07_KLWall member piece: UpReqKLEnergy (merged verbatim, carries its own Requires) ======== *)
(* ============================================================ *)
(* UpReqKLEnergy.v -- the KL>0 unconditional closure module (the negative-branch gap of UpReqKLStrict adjudication 2) *)
(*                                                                *)
(* Main results (all Set-level, zero Prop on statement faces, zero new axioms, all 14 pieces Qed): *)
(*   A. klst_q_pair_nonneg (Q): t^k/k! - t^{k+1}/(k+1)! >= 0 *)
(*      (0<=t<=1; the general-exponent version of q_pair2_nonneg, the pairing engine of the four-term lower bound). *)
(*   B. five Q-level sign micro-pieces: klst_q_pow_pos (t>0 implies t^k>0), *)
(*      klst_q_pow_neg_even / klst_q_pow_neg_odd (the signs of the even/odd powers of (-t)), *)
(*      klst_q_lt0_opp / klst_q_div_lt0. *)
(*   C. klst_ep_four_terms (Q): [the gap-closing single lemma] *)
(*        1 - t + t^2/2 - t^3/6 <= exp_partial (S(S(S m))) (-t)        *)
(*      (0 <= t <= 1; i.e. 1-t+t^2/2-t^3/6 <= ep_n(-t) holds for all n>=3.) *)
(*      Truncation-direction adjudication: exp_partial n x is the partial sum of the first n+1 terms (k=0..n); *)
(*      for the lower-side truncation of a negative-argument alternating series take the odd-sign three-term truncation S3; at n=3 the identity *)
(*      enters, and the odd-sign subsequence rises monotonically in two steps (the paired terms = A), even terms = the previous odd term + *)
(*      the positive tail term. Witness: m arbitrary (n=3+m given constructively). *)
(*   D. klst_exp_tangent_neg (Real): w < 0 implies 1 + w < e^w *)
(*      (the negative-argument strict exponential tangent. The branch construction of the separation witness delta: *)
(*      if eps0^2/3 <= 1/(2C) take delta := eps0^2/6, otherwise delta := 1/(2C); *)
(*      the t := -u_n <= 1 branch goes through C; the t > 1 branch: odd terms go through exp_partial_odd_lower *)
(*      (the 1/(2C) positive lower bound, with M/C/m0 supplied by real_norm_bounded / exp_series_arch *)
(*      / exp_partial_tail_small); even terms inherit 1/(2C) through the sign flip of "odd term = even term + *)
(*      the negative tail quotient". Uniform over all n >= max(N0, 2m0+3).) *)
(*   E. klst_log_tangent_neg (Real): 0 < x < 1 implies log x < x - 1 *)
(*      (the x<1 side of the logarithmic upper tangent; w := log x < 0 via D + the e^{log x}==x transport). *)
(*   F. klst_gibbs_core_strict_neg (Real): q < p implies 0 < kl_term+(q-p) *)
(*      (the strict Gibbs pointwise kernel q<p branch; x := q*inv p < 1, closed in the same shape via E + *)
(*      klst_gap_shape -- paired with klst_gibbs_core_strict). *)
(*   G. klst_kl_energy_nonconst (Real, the unconditional main piece): *)
(*        double normalization + per-term universal weak order (two-way comparability p<=q or q<=p) + *)
(*        strict separation at s0 (either direction; the ratio-separation witness of non-constant energy) *)
(*        imply 0 < sum_s kl_term. *)
(*      Relative to UpReqKLStrict.klst_kl_sum_strict: the per-term premise changes from the one-way weak order *)
(*      (p<=q) to the universal two-way weak order; the excluded q>p branch is supplied by F -- both directions of the temperature bridge *)
(*      (beta2<beta1 and E0<E1: the hot end gives p s0 < q s0 and the cold end gives q s0 < p s0) *)
(*      now enter the main piece. The s0 separation premise is carried by a Set-level Or (the real order is undecidable, *)
(*      an honesty-interface slot; concrete Gibbs instances resolve it via the strict monotonicity of cauchy_real_exp_mono *)
(*      resolves it). *)
(*                                                                *)
(* Redline: zero axioms, zero unclosed proofs; Real-level statements all Set (real_lt is sigT); *)
(*   the Q level follows the in-library Q-level precedent (the QltT decision + the Qle stage belief never appear at the Real level); *)
(*   all closed with Qed; Print Assumptions must be fully Closed. *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
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

Import ListNotations.

(* ============================================================ *)
(* Part A: Q-level pairwise non-negativity (the general-exponent version) *)
(* ============================================================ *)

Lemma klst_q_pair_nonneg : forall (t : Q) (k : nat),
  Qle 0 t -> Qle t 1 ->
  QleT' 0 (q_pow t k / q_fact k - q_pow t (Datatypes.S k) / q_fact (Datatypes.S k)).
Proof.
  intros t k Ht0 Ht1.
  apply Qle_to_QleT'.
  apply (proj1 (Qle_minus_iff (q_pow t (Datatypes.S k) / q_fact (Datatypes.S k))
                              (q_pow t k / q_fact k))).
  apply QleT'_to_Qle.
  apply (q_le_div_le (q_pow t (Datatypes.S k)) (q_fact (Datatypes.S k))
                     (q_pow t k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply Qle_to_QleT'.
    assert (Hpow : q_pow t (Datatypes.S k) == t * q_pow t k).
    { apply (qeqT_imp_qeq _ _ (q_pow_succ t k)). }
    setoid_rewrite Hpow.
    setoid_replace (q_fact (Datatypes.S k))
      with ((Z.of_nat (Datatypes.S k) # 1) * q_fact k).
    2: { apply (qeqT_imp_qeq _ _ (q_fact_succ k)). }
    setoid_replace (t * q_pow t k * q_fact k)
      with (t * (q_pow t k * q_fact k)). 2: ring.
    setoid_replace (q_pow t k * ((Z.of_nat (Datatypes.S k) # 1) * q_fact k))
      with ((Z.of_nat (Datatypes.S k) # 1) * (q_pow t k * q_fact k)). 2: ring.
    apply (Qmult_le_compat_r t (Z.of_nat (Datatypes.S k) # 1)
                             (q_pow t k * q_fact k)).
    * apply (Qle_trans _ 1 _).
      + exact Ht1.
      + unfold Qle. simpl. lia.
    * apply Qmult_le_0_compat.
      + apply QleT'_to_Qle. apply q_pow_nonneg. apply Qle_to_QleT'. exact Ht0.
      + apply (Qlt_le_weak 0 (q_fact k)). exact (QltT_to_Qlt _ _ (q_fact_pos k)).
Qed.

Lemma klst_q_pow_pos : forall (t : Q) (k : nat),
  Qlt 0 t -> QltT 0 (q_pow t k).
Proof.
  intros t k Ht.
  apply Qlt_to_QltT.
  induction k as [| k IH].
  - unfold Qlt. simpl. lia.
  - cbn [q_pow].
    apply (Qmult_lt_0_compat t (q_pow t k)).
    + exact Ht.
    + exact IH.
Qed.

Lemma klst_q_pow_neg_even : forall (t : Q) (j : nat),
  QeqT (q_pow (- t) (2 * j)) (q_pow t (2 * j)).
Proof.
  intros t j.
  apply qeq_imp_qeqT.
  induction j as [| j IH].
  - reflexivity.
  - replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    cbn [q_pow].
    setoid_rewrite IH.
    ring.
Qed.

Lemma klst_q_pow_neg_odd : forall (t : Q) (j : nat),
  QeqT (q_pow (- t) (Datatypes.S (2 * j))) (- (q_pow t (Datatypes.S (2 * j)))).
Proof.
  intros t j.
  apply qeq_imp_qeqT.
  cbn [q_pow].
  setoid_rewrite (qeqT_imp_qeq _ _ (klst_q_pow_neg_even t j)).
  ring.
Qed.

Lemma klst_q_pow_neg_odd_lt : forall (t : Q) (j : nat),
  Qlt 0 t -> QltT (q_pow (- t) (Datatypes.S (2 * j))) 0.
Proof.
  intros t j Ht.
  apply Qlt_to_QltT.
  setoid_rewrite (qeqT_imp_qeq _ _ (klst_q_pow_neg_odd t j)).
  apply (proj2 (Qlt_minus_iff (- (q_pow t (Datatypes.S (2 * j)))) 0)).
  assert (Hsh : 0 - (- (q_pow t (Datatypes.S (2 * j)))) == q_pow t (Datatypes.S (2 * j)))
    by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  exact (QltT_to_Qlt _ _ (klst_q_pow_pos t (Datatypes.S (2 * j)) Ht)).
Qed.

Lemma klst_q_lt0_opp : forall a : Q, Qlt a 0 -> QltT 0 (- a).
Proof.
  intros a H.
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff 0 (- a))).
  assert (Hsh : (- a) - 0 == 0 - a) by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  apply (proj1 (Qlt_minus_iff a 0)).
  exact H.
Qed.

Lemma klst_q_div_lt0 : forall (a b : Q),
  Qlt a 0 -> Qlt 0 b -> QltT (a / b) 0.
Proof.
  intros a b Ha Hb.
  apply Qlt_to_QltT.
  unfold Qdiv.
  apply (proj2 (Qlt_minus_iff (a * Qinv b) 0)).
  assert (Hsh : 0 - a * Qinv b == (- a) * Qinv b) by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  apply (Qmult_lt_0_compat (- a) (Qinv b)).
  - exact (QltT_to_Qlt _ _ (klst_q_lt0_opp a Ha)).
  - apply Qinv_lt_0_compat. exact Hb.
Qed.

Lemma klst_ep_four_terms_odd : forall (j : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  QleT' (1 - t + t * t * (1#2) - t * t * t * (1#6))
        (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)).
Proof.
  intros j t Ht0 Ht1.
  apply Qle_to_QleT'.
  induction j as [| j IH].
  - apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT.
    cbn [exp_partial q_pow q_fact].
    unfold Qdiv, Qminus.
    simpl.
    field.
  - assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) (- t) ==
                    exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                    (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                    (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
    { cbn [exp_partial]. reflexivity. }
    replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    setoid_rewrite Hstep.
    apply (Qle_trans (1 - t + t * t * (1#2) - t * t * t * (1#6))
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                     ((exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                       (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))) +
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))).
    + exact IH.
    + apply (Qle_trans
               (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
               (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                 (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))))
               ((exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                 (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))) +
                (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))).
      * apply (Qle_trans
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) + 0)
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                  ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                   (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))))).
        -- apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT. ring.
        -- apply (proj2 (Qplus_le_r 0%Q
                            ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                             (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))
                            (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)))).
           replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
             with (2 * Datatypes.S (Datatypes.S j))%nat by lia.
           setoid_rewrite (qeqT_imp_qeq _ _ (klst_q_pow_neg_even t (Datatypes.S (Datatypes.S j)))).
           setoid_rewrite (qeqT_imp_qeq _ _ (klst_q_pow_neg_odd t (Datatypes.S (Datatypes.S j)))).
           setoid_replace
             ((- q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))
             with
             (- (q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))))
             by (unfold Qdiv; ring).
           assert (Hpair : Qle 0
                     (q_pow t (2 * Datatypes.S (Datatypes.S j)) / q_fact (2 * Datatypes.S (Datatypes.S j)) -
                      q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))))
             by exact (QleT'_to_Qle _ _
                         (klst_q_pair_nonneg t (2 * Datatypes.S (Datatypes.S j)) Ht0 Ht1)).
           apply (Qle_trans 0%Q
                     (q_pow t (2 * Datatypes.S (Datatypes.S j)) / q_fact (2 * Datatypes.S (Datatypes.S j)) -
                      q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))).
           { exact Hpair. }
           { apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT.
             unfold Qminus. reflexivity. }
      * apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT. ring.
Qed.


Lemma klst_ep_four_terms_even : forall (j : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  QleT' (1 - t + t * t * (1#2) - t * t * t * (1#6))
        (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t)).
Proof.
  intros j t Ht0 Ht1.
  apply Qle_to_QleT'.
  assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t) ==
                  exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                  (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
  { cbn [exp_partial]. reflexivity. }
  apply (Qle_trans (1 - t + t * t * (1#2) - t * t * t * (1#6))
                   (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                   (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t))).
  - exact (QleT'_to_Qle _ _ (klst_ep_four_terms_odd j t Ht0 Ht1)).
  - setoid_rewrite Hstep.
    apply (Qle_trans (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) + 0)
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
    + apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT. ring.
    + apply (proj2 (Qplus_le_r 0%Q
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)))).
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
        with (2 * Datatypes.S (Datatypes.S j))%nat by lia.
      setoid_rewrite (qeqT_imp_qeq _ _ (klst_q_pow_neg_even t (Datatypes.S (Datatypes.S j)))).
      apply QleT'_to_Qle.
      apply q_div_nonneg.
      * apply q_pow_nonneg. apply Qle_to_QleT'. exact Ht0.
      * apply q_fact_pos.
Qed.


Lemma klst_ep_four_terms : forall (m : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  QleT' (1 - t + t * t * (1#2) - t * t * t * (1#6))
        (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) (- t)).
Proof.
  intros m t Ht0 Ht1.
  apply Qle_to_QleT'.
  destruct (Nat.even m) eqn:En.
  - apply Nat.even_spec in En. destruct En as [j Hj]. subst m.
    exact (QleT'_to_Qle _ _ (klst_ep_four_terms_odd j t Ht0 Ht1)).
  - assert (Hodd : Nat.odd m = true).
    { destruct (Nat.odd m) eqn:Eo.
      - reflexivity.
      - exfalso.
        rewrite <- Nat.negb_odd in En.
        rewrite Eo in En.
        simpl in En.
        discriminate En. }
    apply Nat.odd_spec in Hodd. destruct Hodd as [j Hj]. subst m.
    replace (2 * j + 1)%nat with (Datatypes.S (2 * j))%nat by lia.
    exact (QleT'_to_Qle _ _ (klst_ep_four_terms_even j t Ht0 Ht1)).
Qed.
Lemma klst_exp_tangent_neg : forall w : Real,
  real_lt w real_zero ->
  real_lt (real_plus real_one w) (cauchy_real_exp w).
Proof.
  intros [u Hu] Hw.
  destruct Hw as [eps0 [Heps0 [N0 HN0]]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  destruct (exp_partial_tail_small M C (qltT_leT' 0 M HMpos) HC1) as [m0 Hm0].
  assert (Heps0Q : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  assert (HC2pos : Qlt 0 (2 * C)).
  { apply (Qmult_lt_0_compat 2 C).
    - unfold Qlt; simpl; lia.
    - apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  assert (HinvC : Qlt 0 (1 / (2 * C))).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat 1 (Qinv (2 * C))).
    - unfold Qlt; simpl; lia.
    - apply Qinv_lt_0_compat. exact HC2pos. }
  assert (Hthird : Qlt 0 (eps0 * eps0 * (1#3))).
  { apply (Qmult_lt_0_compat (eps0 * eps0) (1#3)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - unfold Qlt; simpl; lia. }
  assert (Hsixth : Qlt 0 (eps0 * eps0 * (1#6))).
  { apply (Qmult_lt_0_compat (eps0 * eps0) (1#6)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - unfold Qlt; simpl; lia. }
  assert (Hdstrict : Qlt (eps0 * eps0 * (1#6)) (eps0 * eps0 * (1#3))).
  { apply (proj2 (Qlt_minus_iff (eps0 * eps0 * (1#6)) (eps0 * eps0 * (1#3)))).
    assert (Hsh : (eps0 * eps0 * (1#3)) - (eps0 * eps0 * (1#6)) == eps0 * eps0 * (1#6))
      by ring.
    setoid_rewrite Hsh.
    exact Hsixth. }
  assert (Hmain : forall d : Q,
    Qle d (1 / (2 * C)) ->
    Qlt d (eps0 * eps0 * (1#3)) ->
    forall n : nat, (Nat.max N0 (2 * m0 + 3) <= n)%nat ->
    QltT d (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) n -
            projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) n)).
  { intros d Hd1 Hdlt n Hn.
    apply Qlt_to_QltT.
    assert (Hmax : (Nat.max N0 (2 * m0 + 3) <= n)%nat) by exact Hn.
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (Hnbig : (2 * m0 + 3 <= n)%nat) by lia.
    assert (Hn3 : (3 <= n)%nat) by lia.
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hun0 : QltT eps0 (0 - u n)).
    { apply (b5a_QltT_eq_r eps0 (0 - u n) (projT1 real_zero n - u n)).
      - setoid_rewrite Hzero. reflexivity.
      - exact (HN0 n (NatLe_lift _ _ HnN0)). }
    assert (HtltT : QltT eps0 (- u n))
      by (apply (b5a_QltT_eq_r eps0 (- u n) (0 - u n));
          [ unfold Qminus; ring | exact Hun0 ]).
    assert (Ht0 : Qlt 0 (- u n)).
    { apply (Qlt_trans 0 eps0 (- u n)).
      - exact Heps0Q.
      - exact (QltT_to_Qlt eps0 (- u n) HtltT). }
    assert (Ht0le : Qle 0 (- u n)) by (apply (Qlt_le_weak 0 (- u n)); exact Ht0).
    assert (Hproj : (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) n -
                     projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) n) ==
                    (exp_partial n (u n) - (1 + u n))).
    { rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) n)).
      cbn [projT1 cauchy_real_exp real_one].
      unfold Qminus. ring. }
    setoid_rewrite Hproj.
    assert (Hfin : exp_partial n (u n) - (1 + u n) ==
                   (exp_partial n (u n) + (- u n - 1)))
      by (unfold Qminus; ring).
    setoid_rewrite Hfin.
    destruct n as [| [| [| m]]]; [ exfalso; lia | exfalso; lia | exfalso; lia | ].
    destruct (Qlt_le_dec 1 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
      as [Ht1big | Ht1small].
    - (* t := -u_n > 1: the odd-sign 1/(2C) positive lower bound + the even-sign transfer by sign flip *)
      destruct (Nat.even (Datatypes.S (Datatypes.S (Datatypes.S m)))) eqn:En.
      + apply Nat.even_spec in En. destruct En as [m2 Hm2].
        rewrite Hm2.
        rewrite Hm2 in Hnbig, Ht0, Ht0le, Ht1big.
        assert (Hm2big : (m0 + 2 <= m2)%nat) by lia.
        assert (Hide : (Datatypes.S (2 * m2) = 2 * m2 + 1)%nat) by lia.
        assert (Hgt1 : Qlt (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2)%nat))).
        { apply (QltT_to_Qlt _ _).
          apply (exp_partial_odd_lower M C m0 m2 (u (2 * m2)%nat)
                   (qltT_leT' 0 M HMpos) HC1 HC Hm0).
          - lia.
          - exact (HM (2 * m2)%nat). }
        assert (Hstep : exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat) ==
                        exp_partial (2 * m2)%nat (u (2 * m2)%nat) +
                        q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2)))
          by (cbn [exp_partial]; reflexivity).
        assert (Hquot : Qlt (q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))) 0).
        { apply (QltT_to_Qlt _ _). apply klst_q_div_lt0.
          - assert (Hux : u (2 * m2)%nat == - (- u (2 * m2)%nat)) by ring.
            setoid_rewrite Hux at 1.
            exact (QltT_to_Qlt _ _ (klst_q_pow_neg_odd_lt (- u (2 * m2)%nat) m2 Ht0)).
          - exact (QltT_to_Qlt _ _ (q_fact_pos (Datatypes.S (2 * m2)))). }
        assert (Hdown : Qlt (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))
                            (exp_partial (2 * m2)%nat (u (2 * m2)%nat))).
        { apply (proj2 (Qlt_minus_iff (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))
                                      (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))).
          setoid_rewrite Hstep.
          assert (Hsh : exp_partial (2 * m2)%nat (u (2 * m2)%nat) -
                        (exp_partial (2 * m2)%nat (u (2 * m2)%nat) +
                         q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))) ==
                        - (q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply (QltT_to_Qlt _ _). apply klst_q_lt0_opp. exact Hquot. }
        assert (Hgt1' : Qlt (1 / (2 * C)) (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))).
        { rewrite Hide. exact Hgt1. }
        assert (Hgt : Qlt (1 / (2 * C)) (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))
          by (apply (Qlt_trans _ (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat)));
              [ exact Hgt1' | exact Hdown ]).
        assert (Hmid : Qlt (1 / (2 * C) + (- u (2 * m2)%nat - 1))
                           (exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1))).
        { apply (proj2 (Qlt_minus_iff (1 / (2 * C) + (- u (2 * m2)%nat - 1))
                                      (exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1)))).
          assert (Hsh : exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1) -
                        (1 / (2 * C) + (- u (2 * m2)%nat - 1)) ==
                        exp_partial (2 * m2)%nat (u (2 * m2)%nat) - 1 / (2 * C))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply (proj1 (Qlt_minus_iff (1 / (2 * C)) (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))).
          exact Hgt. }
        apply (Qlt_trans _ (1 / (2 * C) + (- u (2 * m2)%nat - 1))).
        * apply (Qle_lt_trans _ (1 / (2 * C))).
          -- exact Hd1.
          -- apply (proj2 (Qlt_minus_iff (1 / (2 * C)) (1 / (2 * C) + (- u (2 * m2)%nat - 1)))).
             assert (Hsh : (1 / (2 * C) + (- u (2 * m2)%nat - 1)) - 1 / (2 * C) == (- u (2 * m2)%nat - 1))
               by (unfold Qminus; ring).
             setoid_rewrite Hsh.
             apply (proj1 (Qlt_minus_iff 1 (- u (2 * m2)%nat))). exact Ht1big.
        * exact Hmid.
      + assert (Hodd : Nat.odd (Datatypes.S (Datatypes.S (Datatypes.S m))) = true).
        { destruct (Nat.odd (Datatypes.S (Datatypes.S (Datatypes.S m)))) eqn:Eo.
          - reflexivity.
          - exfalso.
            rewrite <- Nat.negb_odd in En.
            rewrite Eo in En.
            simpl in En.
            discriminate En. }
        apply Nat.odd_spec in Hodd. destruct Hodd as [m2 Hm2].
        rewrite Hm2.
        rewrite Hm2 in Hnbig, Ht0, Ht0le, Ht1big.
        assert (Hm2big : (m0 + 1 <= m2)%nat) by lia.
        assert (Hgt : Qlt (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat))).
        { apply (QltT_to_Qlt _ _).
          apply (exp_partial_odd_lower M C m0 m2 (u (2 * m2 + 1)%nat)
                   (qltT_leT' 0 M HMpos) HC1 HC Hm0).
          - lia.
          - exact (HM (2 * m2 + 1)%nat). }
        assert (Hmid : Qlt (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))
                           (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1))).
        { apply (proj2 (Qlt_minus_iff (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))
                                      (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1)))).
          assert (Hsh : exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1) -
                        (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)) ==
                        exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) - 1 / (2 * C))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply (proj1 (Qlt_minus_iff (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat)))).
          exact Hgt. }
        apply (Qlt_trans _ (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))).
        * apply (Qle_lt_trans _ (1 / (2 * C))).
          -- exact Hd1.
          -- apply (proj2 (Qlt_minus_iff (1 / (2 * C)) (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)))).
             assert (Hsh : (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)) - 1 / (2 * C) == (- u (2 * m2 + 1)%nat - 1))
               by (unfold Qminus; ring).
             setoid_rewrite Hsh.
             apply (proj1 (Qlt_minus_iff 1 (- u (2 * m2 + 1)%nat))). exact Ht1big.
        * exact Hmid.
    - (* t := -u_n <= 1: the four-term lower bound (the gap-closing single lemma) enters directly *)
      assert (Hfour : Qle (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                             + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                             - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                          (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
      { apply (Qle_trans _
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                              (- (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))) _).
        - exact (QleT'_to_Qle _ _
                   (klst_ep_four_terms m
                      (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) Ht0le Ht1small)).
        - apply QleT'_to_Qle.
          apply (S02_CauchyComplete.qeq_le _ _).
          apply qeq_imp_qeqT.
          apply (qeqT_imp_qeq _ _).
          apply exp_partial_wd.
          apply qeq_imp_qeqT.
          ring. }
      (* HmidA: CUBIC - (1 - t) <= G_n (Qplus_le_compat + the shift term of the same shape; t := -u_n explicit) *)
      assert (HmidA : Qle (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                             + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                             - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                             + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                          (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))).
      { apply (Qplus_le_compat
                 (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                    + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                    - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                              (u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                 (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                 (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
        - exact Hfour.
        - apply Qle_refl. }
      assert (HshapeA : (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                           + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                           - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                           + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                        == ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                            - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)))
        by ring.
      assert (HshapeB : (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                        == (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                        (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- u (Datatypes.S (Datatypes.S (Datatypes.S m))) - 1)))
        by ring.
      setoid_rewrite HshapeA in HmidA.
      setoid_rewrite HshapeB in HmidA.
      (* (-u)^2*(1/2) - (-u)^3*(1/6) >= eps0^2*(1/3) > d *)
      assert (Hmid1 : Qle (eps0 * eps0 * (1#3))
                          ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                           - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))).
      { assert (HA : Qle (eps0 * eps0)
                         ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * eps0)).
        { apply (Qmult_le_compat_r eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) eps0).
          - exact (Qlt_le_weak eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (QltT_to_Qlt eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) HtltT)).
          - exact (Qlt_le_weak 0 eps0 Heps0Q). }
        assert (HB : Qle (eps0 * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                         ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
        { apply (Qmult_le_compat_r eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))).
          - exact (Qlt_le_weak eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (QltT_to_Qlt eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) HtltT)).
          - exact Ht0le. }
        apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3)) _).
        { apply (Qmult_le_compat_r (eps0 * eps0)
                                   ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))) (1#3)).
          - apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * eps0)).
            + exact HA.
            + apply (Qle_trans _ (eps0 * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
              * apply QleT'_to_Qle. apply (S02_CauchyComplete.qeq_le _ _). apply qeq_imp_qeqT. ring.
              * exact HB.
          - unfold Qle; simpl; lia. }
        apply (proj2 (Qle_minus_iff ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3))
                       ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                        - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)))).
        assert (Hpos : Qle 0 ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                              * (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))))).
        { apply (Qmult_le_0_compat
                   ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                   (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
          + apply (Qmult_le_0_compat
                     ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))) (1#6)).
            * apply (Qmult_le_0_compat (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))).
              -- exact Ht0le.
              -- exact Ht0le.
            * apply (Qlt_le_weak 0 (1#6)). unfold Qlt; simpl; lia.
          + apply (proj1 (Qle_minus_iff (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) 1)). exact Ht1small. }
        assert (Hsh : ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                         - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                      - ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3))
                      == ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                            * (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))))
          by (unfold Qminus; ring).
        setoid_rewrite Hsh.
        exact Hpos. }
      apply (Qlt_le_trans d (eps0 * eps0 * (1#3))).
      + exact Hdlt.
      + apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                            - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))).
        * exact Hmid1.
        * exact HmidA. }
  (* delta branch construction: if 1/(2C) < eps0^2*(1/3) take delta := 1/(2C), otherwise delta := eps0^2*(1/6) (keeping half the gap preserves strictness) *)
  destruct (Qlt_le_dec (1 / (2 * C)) (eps0 * eps0 * (1#3))) as [Hmin | Hmin].
  - exists (1 / (2 * C)).
    split.
    + apply Qlt_to_QltT. exact HinvC.
    + exists (Nat.max N0 (2 * m0 + 3))%nat.
      intros n Hn.
      apply Hmain.
      * apply Qle_refl.
      * exact Hmin.
      * exact (NatLe_drop _ _ Hn).
  - exists (eps0 * eps0 * (1#6)).
    split.
    + apply Qlt_to_QltT. exact Hsixth.
    + exists (Nat.max N0 (2 * m0 + 3))%nat.
      intros n Hn.
      apply Hmain.
      * apply (Qle_trans _ (eps0 * eps0 * (1#3))).
        -- apply (Qlt_le_weak _ _). exact Hdstrict.
        -- exact Hmin.
      * exact Hdstrict.
      * exact (NatLe_drop _ _ Hn).
Qed.

(* ============================================================ *)
(* Part E: the x<1 side of the logarithmic upper tangent (Real level) *)
(*   0 < x < 1 implies log x < x - 1                                  *)
(* ============================================================ *)

Lemma klst_log_tangent_neg : forall (x : Real)
  (Hx : real_lt real_zero x) (Hx1 : real_lt x real_one),
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx Hx1.
  assert (Hlogneg : real_lt (real_log x Hx) real_zero).
  { apply (RealSetoid.real_lt_id_r (real_log x Hx)
             (real_log real_one real_lt_zero_one) real_zero).
    - exact (real_log_one real_lt_zero_one).
    - exact (real_log_lt_mono x real_one Hx real_lt_zero_one Hx1). }
  assert (Htan : real_lt (real_plus real_one (real_log x Hx)) (cauchy_real_exp (real_log x Hx)))
    by exact (klst_exp_tangent_neg (real_log x Hx) Hlogneg).
  assert (Hval : real_eq (cauchy_real_exp (real_log x Hx)) x)
    by exact (cw_log_exp_right x Hx).
  assert (H2 : real_lt (real_plus real_one (real_log x Hx)) x)
    by exact (RealSetoid.real_lt_compat (real_plus real_one (real_log x Hx))
                                        (real_plus real_one (real_log x Hx))
                                        (cauchy_real_exp (real_log x Hx)) x
                                        (real_eq_refl (real_plus real_one (real_log x Hx)))
                                        Hval Htan).
  apply (RealSetoid.real_lt_id_l (real_log x Hx)
               (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
               (real_plus x (real_opp real_one))).
  + apply real_eq_sym.
    apply (real_eq_trans _ (real_plus (real_plus (real_opp real_one) real_one) (real_log x Hx)) _).
    * apply real_plus_assoc.
    * apply (real_eq_trans _ (real_plus real_zero (real_log x Hx)) _).
      -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp real_one) real_one)
                                              (real_log x Hx)
                                              real_zero (real_log x Hx)).
         ++ apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
            ** apply real_plus_comm.
            ** apply real_plus_opp.
         ++ apply real_eq_refl.
      -- apply (real_eq_trans _ (real_plus (real_log x Hx) real_zero) _).
         ++ apply real_plus_comm.
         ++ apply real_plus_zero.
  + apply (RealSetoid.real_lt_id_r
             (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
             (real_plus (real_opp real_one) x)
             (real_plus x (real_opp real_one))).
    * exact (real_plus_comm (real_opp real_one) x).
    * apply (real_lt_plus_translate (real_opp real_one)
                                    (real_plus real_one (real_log x Hx)) x).
      exact H2.
Qed.

(* ============================================================ *)
(* Part F: the strict Gibbs pointwise kernel q<p branch (paired with klst_gibbs_core_strict) *)
(* ============================================================ *)

Lemma klst_gibbs_core_strict_neg : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hqp : real_lt q p),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hqp.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hx1 : real_lt X real_one).
  { apply (RealSetoid.real_lt_id_r X (real_mult p (real_inv_pos p Hp)) real_one).
    - exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat q p (real_inv_pos p Hp) Hqp (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_neg X HX Hx1).
  assert (Hgap : real_lt real_zero (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* ============================================================ *)
(* Part G: the KL strict-sum unconditional main piece (per-term premises changed to the universal two-way weak order) *)
(* ============================================================ *)

(* The unconditional KL>0 main piece: double normalization + per-term two-way comparability (universal weak order: p<=q or q<=p) +
   strict separation at s0 (either direction Or; the ratio-separation witness of non-constant energy)
   imply 0 < sum_s kl_term (the list l1++s0::l2).
   Relative to UpReqKLStrict.klst_kl_sum_strict: the per-term premise real_le (p s) (q s)
   becomes the universal two-way weak order Or (real_le (p s) (q s)) (real_le (q s) (p s)),
   the q>p branch supplied by klst_gibbs_core_strict_neg; the s0 strict separation also becomes a two-way Or,
   so both directions of the temperature bridge enter. *)
Lemma klst_kl_energy_nonconst : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, Or (real_le (p s) (q s)) (real_le (q s) (p s)))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : Or (real_lt (p s₀) (q s₀)) (real_lt (q s₀) (p s₀))),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  set (L := l₁ ++ s₀ :: l₂).
  set (KL := fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : X => real_plus (KL s) (real_plus (q s) (real_opp (p s)))).
  (* 1. per-term g >= 0 (the four branches of the universal two-way weak order: p<q / p==q / q<p / q==p) *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hle | Hle'].
    - destruct Hle as [Hlt | Heq].
      + unfold real_le. left.
        exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
      + unfold real_le. right. apply real_eq_sym.
        exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq).
    - destruct Hle' as [Hlt | Heq].
      + unfold real_le. left.
        exact (klst_gibbs_core_strict_neg (p s) (q s) (Hp s) (Hq s) Hlt).
      + unfold real_le. right. apply real_eq_sym.
        exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s)
                 (real_eq_sym (q s) (p s) Heq)). }
  (* 2. sum kl L == sum G L (normalization zero-sum cancellation, same pattern as gibbs_inequality_eps) *)
  assert (Hzero : real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L) real_zero).
  { apply (real_eq_trans _ (real_plus (real_list_sum X p L) (real_list_sum X (fun s => real_opp (q s)) L)) _).
    - apply (real_list_sum_add X p (fun s => real_opp (q s)) L).
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p L)
                                             (real_list_sum X (fun s => real_opp (q s)) L)
                                             real_one (real_opp real_one)).
        * exact Hnormp.
        * apply (real_eq_trans _ (real_opp (real_list_sum X q L)) _).
          -- apply (real_list_sum_opp X q L).
          -- apply (RealSetoid.real_eq_opp_compat (real_list_sum X q L) real_one).
             exact Hnormq.
      + apply real_plus_opp. }
  assert (Hqp : real_eq (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L) real_zero).
  { apply (real_eq_trans _ (real_list_sum X (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L) _).
    - apply (real_list_sum_ext X (fun s => real_plus (q s) (real_opp (p s)))
                               (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L).
      intro s. exact (klst_r_opp_minus (p s) (q s)).
    - apply (real_eq_trans _ (real_opp (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)) _).
      + apply (real_list_sum_opp X (fun s => real_plus (p s) (real_opp (q s))) L).
      + apply (real_eq_trans _ (real_opp real_zero) _).
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)
                                               real_zero).
          exact Hzero.
        * exact real_opp_zero. }
  assert (HsumG : real_eq (real_list_sum X KL L) (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_list_sum X KL L)
                          (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)) _).
    - apply (real_eq_trans _ (real_plus (real_list_sum X KL L) real_zero) _).
      + apply real_eq_sym. apply real_plus_zero.
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X KL L) real_zero
                                              (real_list_sum X KL L)
                                              (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)).
        * apply real_eq_refl.
        * apply real_eq_sym. exact Hqp.
    - apply (real_eq_sym _ _). unfold G.
      apply (real_list_sum_add X KL (fun s => real_plus (q s) (real_opp (p s))) L). }
  (* 3. sum G L == G s0 + sum G l1 + sum G l2 (app split + assoc + comm) *)
  assert (Hsplit : real_eq (real_list_sum X G L)
                           (real_plus (real_plus (G s₀) (real_list_sum X G l₁))
                                      (real_list_sum X G l₂))).
  { unfold L.
    apply (real_eq_trans _ (real_plus (real_list_sum X G l₁)
                                      (real_plus (G s₀) (real_list_sum X G l₂))) _).
    - exact (klst_list_sum_app X G l₁ (s₀ :: l₂)).
    - apply (real_eq_trans
               _ (real_plus (real_plus (real_list_sum X G l₁) (G s₀)) (real_list_sum X G l₂)) _).
      + apply real_plus_assoc.
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_list_sum X G l₁) (G s₀))
                                             (real_list_sum X G l₂)
                                             (real_plus (G s₀) (real_list_sum X G l₁))
                                             (real_list_sum X G l₂)).
        * apply real_plus_comm.
        * apply real_eq_refl. }
  (* 4. tail sum >= 0 + one strict term imply 0 < sum G L imply 0 < sum kl L *)
  assert (Htail : real_le real_zero (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
  { apply (RealSetoid.real_le_id_r real_zero (real_list_sum X G (l₁ ++ l₂))
                                   (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - exact (klst_list_sum_app X G l₁ l₂).
    - exact (real_list_sum_nonneg X G (l₁ ++ l₂) Hgnonneg). }
  assert (Hmain : real_lt real_zero (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))).
  { apply (klst_r_lt_plus_le (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - unfold G. unfold KL. destruct Hdiv as [Hd | Hd].
      + exact (klst_gibbs_core_strict (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hd).
      + exact (klst_gibbs_core_strict_neg (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hd).
    - exact Htail. }
  assert (Hfin : real_eq (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
                         (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_plus (G s₀) (real_list_sum X G l₁)) (real_list_sum X G l₂)) _).
    - apply real_plus_assoc.
    - apply real_eq_sym. exact Hsplit. }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
           (real_list_sum X KL L)).
  - apply (real_eq_trans _ (real_list_sum X G L) _).
    + exact Hfin.
    + apply real_eq_sym. exact HsumG.
  - exact Hmain.
Qed.

(* ============================================================ *)
(* Closed proofs (Print Assumptions must be fully Closed) *)
(* ============================================================ *)

Print Assumptions klst_q_pair_nonneg.
Print Assumptions klst_q_pow_pos.
Print Assumptions klst_q_pow_neg_even.
Print Assumptions klst_q_pow_neg_odd.
Print Assumptions klst_q_pow_neg_odd_lt.
Print Assumptions klst_q_lt0_opp.
Print Assumptions klst_q_div_lt0.
Print Assumptions klst_ep_four_terms_odd.
Print Assumptions klst_ep_four_terms_even.
Print Assumptions klst_ep_four_terms.
Print Assumptions klst_exp_tangent_neg.
Print Assumptions klst_log_tangent_neg.
Print Assumptions klst_gibbs_core_strict_neg.
Print Assumptions klst_kl_energy_nonconst.

(* ============================================================ *)
(* Endnote (the adjudication registry) *)
(*   Adjudication A (the gap closed by a single lemma): the Q-level four-term alternating partial-sum lower bound *)
(*     1-t+t^2/2-t^3/6 <= ep_n(-t) holds for all 0<=t<=1 and n>=3 (klst_ep_four_terms). *)
(*     Truncation-direction adjudication: exp_partial n x is defined as the partial sum of the first n+1 terms (k=0..n); *)
(*     for the lower-side truncation of a negative-argument alternating series take S3 (the odd-sign three-term truncation); at n=3 *)
(*     the identity exp_partial 3 (-t) identical to S3 enters, and the odd-sign subsequence, through the paired terms *)
(*     t^{2k}/(2k)! - t^{2k+1}/(2k+1)! >= 0 (klst_q_pair_nonneg, *)
(*     the general-exponent version of q_pair2_nonneg), rises monotonically in two steps; even terms = the previous odd term + *)
(*     the positive tail term t^{2j+4}/(2j+4)! >= 0. Witness: n := 3+m given constructively. *)
(*   Adjudication B (the negative-branch tangent): the branch construction of the separation witness delta for w<0 implying 1+w<e^w -- *)
(*     the even-sign lower bound of the t := -u_n > 1 branch is not uniform in t-1 (it fails as t approaches 1 from above); instead go through *)
(*     the "odd term = even term + negative tail quotient" transfer of the 1/(2C) positive lower bound of exp_partial_odd_lower *)
(*     (the M/C/m0 supply chain same as real_exp_ge_linear_eps); *)
(*     the t <= 1 branch gets >= t^2(3-t)/6 >= t^2/3 >= eps0^2/3 from the gap-closing single lemma. *)
(*     The two delta branches of the min choice: if eps0^2/3 <= 1/(2C) take delta := eps0^2/6 (keeping half the gap *)
(*     preserves the QltT strictness), otherwise delta := 1/(2C). *)
(*   Adjudication C (the shape of the unconditional main piece): the per-term real_le real_zero (G s) (Or shape) *)
(*     is not constructively available for arbitrary p,q (equality points are undecidable); the universal weak-order comparability *)
(*     (p<=q or q<=p) must be carried as a premise -- the two-temperature Gibbs family satisfies it (ratio monotonicity; *)
(*     concrete instances resolve it via the strict monotonicity of cauchy_real_exp_mono); the s0 strict separation likewise *)
(*     rides on a two-way Or premise. The per-term Bishop-form (eps slack) no-premise route is carried by the library-side *)
(*     real_gibbs_core_eps / real_gibbs_inequality_eps; its strictification *)
(*     closing combinators (the real_le_b family) await a later module slot. *)
(* ============================================================ *)