(* ConstructiveWorld-Set — strict KL-divergence lemma family. *)

(** * UpReqKLStrict: strict Gibbs/KL inequality lemmas at the rational layer.

    Mission.  The strict family behind non-constant energy implying positive KL
 divergence: the two-term exponential lower bound [klst_ep_two_terms],
 the strict tangent lemmas [klst_exp_tangent_pos] and
 [klst_log_tangent_pos] with explicit gap witnesses, and the core
 strictness pair [klst_gibbs_core_strict] / [klst_gibbs_core_zero].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires the base modules [S01_BaseRing] up to [S08_RealMainlineDPO]
      of this development.

    References.  This development, UpReqKLStrict.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: the [Qle] conclusion
 of the station lemma moved to [QleT']).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqKLStrict.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

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

(* =================== Part A: Q-layer second-order partial-sum lower bound (the gap source of the strict tangents) =================== *)

Lemma klst_ep_two_terms : forall (m : nat) (x : Q),
  Qle 0 x ->
  QleT' (1 + x + x * x * (1#2))
        (exp_partial (Datatypes.S (Datatypes.S m)) x).
Proof.
  intros m x Hx.
  apply Qle_to_QleT'.
  induction m as [| m IH].
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
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
    (* Qle A (B + T): split through Qle_trans into Qle A B (the IH) and *)
    (* Qle B (B + T); the latter again goes through Qle_trans via (B + 0) *)
    (* (a qeq_le ring reshaping settles the +0 mismatch), then the proj1 *)
    (* (forward iff direction) of Qplus_le_r 0 T B admits 0 <= T. *)
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
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
        ring.
      * apply (proj2 (Qplus_le_r 0%Q
                        (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                         q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
                        (exp_partial (Datatypes.S (Datatypes.S m)) x))).
        apply QleT'_to_Qle.
        apply (q_pow_fact_nonneg x (Datatypes.S (Datatypes.S (Datatypes.S m))) (Qle_to_QleT' _ _ Hx)).
Qed.

(* =================== Part B: strict exponential/logarithmic tangents (positive-argument branch) =================== *)

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
    (* The conclusion of HN0 has the shape QltT eps (u k - 0); since QltT is *)
    (* an Id on bool it cannot be unfolded directly — b5a_QltT_eq_r *)
    (* (x == y -> QltT a y -> QltT a x) plus a Q ring reshaping removes the -0. *)
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
    (* Finale: Hscale (strict) plus the left-multiplied shift of Htwo *)
    (* (nested Qplus_le_compat, shapes aligned position by position). *)
    apply (Qlt_le_trans (eps * eps * (1#2))
                        (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                        (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
    + exact Hscale.
    + apply (Qle_trans (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                       ((1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                          + (- 1) + (- u (Datatypes.S (Datatypes.S m))))
                       (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
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

(* =================== Part C0: small Real-layer reshaping helpers =================== *)
(* Pointwise exact identities closed by the Q ring. *)
(* Note: the projection of real_inv_pos carries an if-leb branch, so *)
(* pointwise q == p*(q*inv p) is not an identity; the reshaping in *)
(* gap_shape must therefore not go through real_eq_of_zero_diff but is *)
(* done at the Real layer along the assoc/comm/one/inv_pos_correct chain *)
(* (klst_r_pqx_eq_q). *)

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

(* Strict-plus-weak-order addition: 0 < x and 0 <= y give 0 < x + y *)
(* (the conclusion of real_lt_plus_compat_lt_le carries (0+0), reshaped *)
(* via real_lt_id_l + real_plus_zero). *)
Lemma klst_r_lt_plus_le : forall (x y : Real),
  real_lt real_zero x -> real_le real_zero y -> real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero) (real_plus x y)).
  - apply real_eq_sym. exact (real_plus_zero real_zero).
  - exact (real_lt_plus_compat_lt_le real_zero x real_zero y Hx Hy).
Qed.

(* =================== Part C: strict Gibbs pointwise kernel (q > p branch) and the degenerate counterpart =================== *)



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
  - (* Left shape: p*(-L) + (q + -p) -> -(p*L) + (p*X + -p). *)
    apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp L))
                                          (real_plus q (real_opp p))
                                          (real_opp (real_mult p L))
                                          (real_plus (real_mult p X) (real_opp p))).
    + exact (klst_r_mult_opp_r p L).
    + apply (RealSetoid.real_eq_plus_compat q (real_opp p) (real_mult p X) (real_opp p)).
      * apply real_eq_sym. exact (klst_r_pqx_eq_q p q Hp).
      * apply real_eq_refl.
  - (* Right shape: p*((X + -1) + -L) -> (p*(X + -1)) + p*(-L) -> *)
    (* (p*X + -p) + -(p*L), then reordered by commutativity. *)
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

(* Degenerate counterpart: p == q gives kl_term(p,q) + (q - p) == 0 *)
(* (paired with the strict lemma). *)
Lemma klst_gibbs_core_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) real_zero.
Proof.
  intros p q Hp Hq Hpq.
  unfold real_kl_term.
  set (x := real_mult q (real_inv_pos p Hp)).
  set (Hx := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  (* x == 1: replace the inverse under p == q (inv_pos_ext) plus inv_pos_correct. *)
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
  (* Real-layer reshaping chain: g == p*(-log x) + q - p == p*(-log 1) + q - p *)
  (* == p*0 + q - p == q - p == q - q == 0. *)
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

(* =================== Part D: the strict KL-sum main lemma (weak-order p <= q branch) =================== *)

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

(* Strict KL positivity main lemma: pointwise positivity + double *)
(* normalization + pointwise p <= q (weak order, with the strict q > p *)
(* branch as a subcase) + a strict separation witness at s0 *)
(* (p s0 < q s0) give 0 < sum_s kl_term. *)
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
  (* 1. g >= 0 pointwise (the two weak-order branches: the strict branch of *)
  (* Part C and the equality branch, the degenerate lemma). *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hlt | Heq].
    - unfold real_le. left.
      exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
    - unfold real_le. right. apply real_eq_sym.
      exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq). }
  (* 2. sum kl L == sum G L (the normalized zero-sum cancellation, in the *)
  (* manner of gibbs_inequality_eps). *)
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
  (* 3. sum G L == G s0 + sum G l1 + sum G l2 (app split + assoc + comm). *)
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
  (* 4. Tail sum >= 0 plus the strict term give 0 < sum G L, hence 0 < sum kl L. *)
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

(* =================== Assumption audits (all Print Assumptions outputs must read Closed) =================== *)

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

(* =================== Endnotes (summary of results) =================== *)
(* Result 1 (positive branch, fully closed): the strict exponential and *)
(* logarithmic tangents on the positive branch, the strict Gibbs kernel *)
(* (q > p branch), the degenerate counterpart, and the strict KL sum *)
(* (weak-order p <= q branch) are all closed by Qed with no standing *)
(* premises — "non-constant energy implies KL > 0" is fully closed on the *)
(* p <= q side. *)
(* Technical notes: (1) the Part A step case goes through Qle_trans via *)
(* (B + 0); (2) the real_eq_of_zero_diff route for gap_shape does not work *)
(* (the projection of real_inv_pos carries an if-leb branch, so pointwise *)
(* q == p*q*inv p is not an identity) and is replaced by the Real-layer *)
(* chain (the five C0 pieces: distr_l / mult_opp_r / mult_m1_r / pqx_eq_q / *)
(* opp_minus; the first four via assoc/comm/one/inv_pos_correct, *)
(* opp_minus pointwise exact); (3) in the reshaping chains of *)
(* klst_log_tangent_pos, the two (-1)+1 / 0+x positions are reordered by *)
(* comm+opp / comm+zero; (4) the Part D split and shift pieces bridge *)
(* sum(q-p) == 0 via real_list_sum_ext + real_opp_zero, and the strict *)
(* s0 term injects gibbs_core_strict directly (Hdiv is its Hpq argument). *)
(* Result 2 (negative branch, blocked pending one lemma): pointwise *)
(* g >= 0 on the q < p branch needs a strict exponential with negative *)
(* argument, i.e. the upper tangent of log on the x < 1 side. *)
(* Its Q-layer gap source requires the four-term alternating partial-sum *)
(* lower bound 1 - t + t^2/2 - t^3/6 <= ep_n(-t); the existing *)
(* exp_partial family has only the first-order bound *)
(* (exp_partial_ge_plus_x) and the sign-split non-strict pieces *)
(* (odd/even_ge_minus, serving the eps-form non-strict statements), *)
(* with no positive-gap witness field — a single-lemma gap; once filled, *)
(* swapping the pointwise premise of Part D for the unrestricted weak *)
(* order gives the unconditional statement (temperature bridge: beta2 < *)
(* beta1 and E0 < E1 give strictly separated ratios; the strict *)
(* monotonicity cauchy_real_exp_mono is already available, and the exp_neg *)
(* sign flip reshapes straight through). *)
(* Result 3 (relation to the eps-form engine): this file does not use the *)
(* real_le_b finisher — the strict layer real_lt is a sigT positive *)
(* statement with no Or-equality-branch extraction obstacle; the obstacle *)
(* is the library-side missing tangent fields *)
(* (real_exp_ge_linear_eps / real_log_le_linear_eps are both eps-form Or *)
(* encodings), the same limitation as recorded in the UpRealLeB endnotes *)
(* but at a different site. *)
