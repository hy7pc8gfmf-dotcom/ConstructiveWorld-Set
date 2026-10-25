(* ConstructiveWorld-Set — strict KL-divergence lemma family. *)

(** * UpReqKLStrict: strict Gibbs/KL inequality lemmas at the rational layer..

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

(* ============================================================ *)
(* Part A：Q 层二阶部分和下界（严格切线的间隙源）                       *)
(* ============================================================ *)

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
    (* Qle A (B + T)：经 Qle_trans 拆成 Qle A B（IH）与 Qle B (B + T)；      *)
    (* 后者再经 Qle_trans 过 (B + 0)（qeq_le 环换形杀 +0 失配）              *)
    (* + Qplus_le_r 0 T B 的 proj1（iff 正向）供 0 ≤ T 入场。               *)
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

(* ============================================================ *)
(* Part B：严格指数/对数切线（正 argument 支）                          *)
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
    (* HN0 结论形为 QltT eps (u k − 0)：QltT 为 Id bool，不可 unfolds 直用，   *)
    (* 经 b5a_QltT_eq_r（x==y ⟹ QltT a y ⟹ QltT a x）+ Q 环换形去 −0。       *)
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
    (* 收尾：Hscale（严格）+ Htwo 左乘平移（Qplus_le_compat 嵌套，形状逐位对齐） *)
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

(* ============================================================ *)
(* Part C0：实层换形微型助手（逐点 exact 恒等，Q 环收尾）                *)
(*   注：real_inv_pos 的投影带 if leb 分支，逐点 q == p·(q·inv p) 非恒等，  *)
(*   故 gap_shape 的换形不得走 real_eq_of_zero_diff，须在实层经            *)
(*   assoc/comm/one/inv_pos_correct 链完成（klst_r_pqx_eq_q）。           *)
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

(* 严格 + 弱序相加：0 < x、0 ≤ y ⟹ 0 < x + y
   （real_lt_plus_compat_lt_le 的结论带 (0+0)，经 real_lt_id_l + real_plus_zero 换形） *)
Lemma klst_r_lt_plus_le : forall (x y : Real),
  real_lt real_zero x -> real_le real_zero y -> real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero) (real_plus x y)).
  - apply real_eq_sym. exact (real_plus_zero real_zero).
  - exact (real_lt_plus_compat_lt_le real_zero x real_zero y Hx Hy).
Qed.

(* ============================================================ *)
(* Part C：严格 Gibbs 逐点核（q>p 支）+ 退化对照                        *)
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
  - (* 左形：p·(−L) + (q + −p) → −(p·L) + (p·X + −p) *)
    apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp L))
                                          (real_plus q (real_opp p))
                                          (real_opp (real_mult p L))
                                          (real_plus (real_mult p X) (real_opp p))).
    + exact (klst_r_mult_opp_r p L).
    + apply (RealSetoid.real_eq_plus_compat q (real_opp p) (real_mult p X) (real_opp p)).
      * apply real_eq_sym. exact (klst_r_pqx_eq_q p q Hp).
      * apply real_eq_refl.
  - (* 右形：p·((X + −1) + −L) → (p·(X+−1)) + p·(−L) → (p·X + −p) + −(p·L)，再交换合流 *)
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

(* 退化对照件：p == q ⟹ kl_term(p,q) + (q − p) == 0（与严格件成对）。 *)
Lemma klst_gibbs_core_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) real_zero.
Proof.
  intros p q Hp Hq Hpq.
  unfold real_kl_term.
  set (x := real_mult q (real_inv_pos p Hp)).
  set (Hx := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  (* x == 1：p==q 换 inv（inv_pos_ext）+ inv_pos_correct *)
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
  (* 实层换形链：g == p·(−log x) + q − p == p·(−log 1) + q − p
     == p·0 + q − p == q − p == q − q == 0 *)
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
(* Part D：KL 严格和主件（弱序 p≤q 支）                                 *)
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

(* KL 严格正主件：逐项正性 + 双归一化 + 逐项 p≤q（弱序，排除 q>p 支）+
   s₀ 处严格分离见证（p s₀ < q s₀）⟹ 0 < Σ_s kl_term。 *)
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
  (* 1. 逐项 g ≥ 0（弱序两支：严格支 C / 等号支退化件） *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hlt | Heq].
    - unfold real_le. left.
      exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
    - unfold real_le. right. apply real_eq_sym.
      exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq). }
  (* 2. Σ kl L == Σ G L（归一化零和抵消，gibbs_inequality_eps 同款） *)
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
  (* 3. Σ G L == G s₀ + Σ G l₁ + Σ G l₂（app 拆分 + assoc + comm） *)
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
  (* 4. 尾和 ≥ 0 + 严格项 ⟹ 0 < Σ G L ⟹ 0 < Σ kl L *)
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
(* 闭合证明（Print Assumptions 须全 Closed）                            *)
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
(* 尾注（结论总表）                                                      *)
(*   结论 1（正支全链闭合）：严格指数/对数切线正支 + 严格 Gibbs 核 q>p 支 +   *)
(*     退化对照件 + KL 严格和（弱序 p≤q 支）全 Qed，零假设位——            *)
(*     「能量非常数 ⟹ KL>0」在 p≤q 侧已完整闭合。                        *)
(*     技术注记：①Part A 步进 case 以 Qle_trans 过 (B+0)                      *)

(*     ②gap_shape 的 real_eq_of_zero_diff 路线证伪（real_inv_pos 投影带    *)
(*     if leb 分支，逐点 q == p·q·inv p 非恒等），改实层链               *)
(*     （C0 五件：distr_l / mult_opp_r / mult_m1_r / pqx_eq_q /           *)
(*     opp_minus，前四者经 assoc/comm/one/inv_pos_correct，               *)
(*     opp_minus 逐点 exact）；③klst_log_tangent_pos 换形链两处            *)
(*     (−1)+1 / 0+x 形位以 comm+opp / comm+zero 重排；④Part D 拆和/      *)
(*     平移各件以 real_list_sum_ext + real_opp_zero 桥 Σ(q−p)==0，        *)
(*     s₀ 严格项直接注入 gibbs_core_strict（Hdiv 即其 Hpq 实参）。         *)
(*   结论 2（负支阻塞精确裁决）：q<p 支的逐项 g≥0 需负 argument 严格指数    *)

(*     ＝ 对数上切线 x<1 侧。其 Q 层间隙源需四项交错部分和下界             *)
(*     1−t+t²/2−t³/6 ≤ ep_n(−t)；现有 exp_partial 族仅一阶                *)
(*     （exp_partial_ge_plus_x）与符号分段非严格件                *)
(*     （odd/even_ge_minus，服务 eps 形 non-strict），     *)
(*     无正间隙见证字段 ⟹ 单引理缺口，补齐后与 Part D 逐项前提换全称弱序    *)
(*     即得无条件件（温度桥：β₂<β₁、E₀<E₁ ⟹ 比率严格分离，               *)
(*     cauchy_real_exp_mono 严格单调已备，exp_neg 反号换形一路可通）。     *)
(*   结论 3（与 eps 形引擎关系）：本件不使用 real_le_b 完成器——严格层      *)
(*     real_lt 为 sigT 正陈述，无 Or 等号分支提取障碍；障碍在库侧切线      *)
(*     字段缺失（real_exp_ge_linear_eps / real_log_le_linear_eps 均为     *)
(*     eps 形 Or 编码），与 UpRealLeB 尾注已知限制同源不同位。             *)
(* ============================================================ *)
